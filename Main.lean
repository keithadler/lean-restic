import Restic
import Lean.Data.Json

/-!
# `lean-restic`: read a restic repository with the proved definitions

    lean-restic -r REPO ids
    lean-restic -r REPO [KEY] cat config
    lean-restic -r REPO [KEY] cat snapshot|index|lock|key ID
    lean-restic -r REPO [KEY] check
    lean-restic -r REPO [KEY] snapshots
    lean-restic -r REPO [KEY] ls SNAPSHOT
    lean-restic -r REPO [KEY] restore SNAPSHOT --target DIR

The key comes from the password, as restic takes it (`--password-file FILE` or `RESTIC_PASSWORD`),
unlocked with scrypt from a key file; or from `--masterkey FILE`, the JSON `restic cat masterkey` prints.

* `ids`: every file in the repository (except `config`) is named by the SHA-256 of its contents.
* `check`: reads every pack with `readPack` (every blob and header authenticated, the header accounts
  for every byte, every uncompressed blob hashes to its ID, `readPack_ok`); compressed blobs are
  decompressed and hashed too.
* `restore`: writes the snapshot's files, each byte fetched by ID and checked against it
  (`Restic/Repo.lean`). File contents and directories only: no permissions, times, or symlinks yet.

The master key file is read with Lean's own `Lean.Json`; everything read from the repository goes
through `Restic/`.
-/

open Restic Restic.Repo

def loadMasterKey (path : System.FilePath) : IO MasterKey := do
  let text ← IO.FS.readFile path
  let b64 (j : Lean.Json) (keys : List String) : Except String Bytes := do
    let mut v := j
    for k in keys do v ← v.getObjVal? k
    match Base64.decode (← v.getStr?) with
    | some bs => return bs
    | none => throw s!"{".".intercalate keys} is not Base64"
  let parsed : Except String MasterKey := do
    let j ← Lean.Json.parse text
    return ⟨← b64 j ["encrypt"], ← b64 j ["mac", "k"], ← b64 j ["mac", "r"]⟩
  match parsed with
  | .ok k =>
    unless k.valid do fail "the master key has the wrong lengths or an all-zero part"
    return k
  | .error e => fail s!"{path}: {e}"

def dirOf : String → Option String
  | "snapshot" => some "snapshots"
  | "index" => some "index"
  | "lock" => some "locks"
  | "key" => some "keys"
  | _ => none

def ids (repo : System.FilePath) : IO UInt32 := do
  let mut bad := 0
  let mut n := 0
  for sub in ["keys", "snapshots", "index", "data"] do
    for f in ← filesUnder (repo / sub) do
      n := n + 1
      let h := hex (sha256 (← readBytes f))
      if h != f.fileName.getD "" then
        bad := bad + 1
        IO.println s!"MISMATCH {f}: contents hash to {h}"
  IO.println s!"{n - bad} of {n} files are named by the SHA-256 of their contents"
  return if bad = 0 then 0 else 1

def explainPack : PackError → String
  | .badHeaderLength => "the header length in the last four bytes is larger than the file"
  | .header e => s!"header: {explainOpen e}"
  | .badHeader => "the header is not a list of blob entries"
  | .lengthMismatch => "the blob lengths in the header do not add up to the file"
  | .blob i e => s!"blob {i}: {explainOpen e}"
  | .idMismatch i => s!"blob {i}: plaintext does not hash to its ID"

def check (repo : System.FilePath) (key : MasterKey) : IO UInt32 := do
  let mut bad := 0
  let mut packs := 0
  let mut blobs := 0
  let mut hashed := 0
  let mut bytes := 0
  for f in ← filesUnder (repo / "data") do
    packs := packs + 1
    let data ← readBytes f
    bytes := bytes + data.length
    match readPack key data with
    | .error e =>
      bad := bad + 1
      IO.println s!"BAD {f}: {explainPack e}"
    | .ok xs =>
      blobs := blobs + xs.length
      hashed := hashed + (xs.filter (·.1.rawLength.isNone)).length
      -- Compressed blobs: decompress, then check the length and the ID (the zstd decoder is tested,
      -- not proved; see Restic/Zstd.lean).
      for (e, pt) in xs do
        if let some raw := e.rawLength then
          match Zstd.decompress (ByteArray.mk pt.toArray) with
          | .error err =>
            bad := bad + 1
            IO.println s!"BAD {f}: blob {hex e.id}: zstd: {err}"
          | .ok out =>
            if out.size ≠ raw then
              bad := bad + 1
              IO.println s!"BAD {f}: blob {hex e.id}: decompresses to {out.size} bytes, header says {raw}"
            else if sha256 out.toList ≠ e.id then
              bad := bad + 1
              IO.println s!"BAD {f}: blob {hex e.id}: decompressed plaintext does not hash to its ID"
            else
              hashed := hashed + 1
  IO.println s!"{packs - bad} of {packs} packs read ({bytes} bytes): {blobs} blobs authenticated, {hashed} of them hashed to their IDs"
  return if bad = 0 then 0 else 1

def snapshotJson (repo : System.FilePath) (key : MasterKey) (id : String) : IO (String × Json) := do
  let f ← findFile (repo / "snapshots") id
  let j ← orFail f.toString (Json.parse (← openFile key f))
  return (f.fileName.getD "", j)

def snapshots (repo : System.FilePath) (key : MasterKey) : IO UInt32 := do
  for f in ← filesUnder (repo / "snapshots") do
    let j ← orFail f.toString (Json.parse (← openFile key f))
    let time ← orFail f.toString (j.strField "time")
    let host := (j.get? "hostname").bind (fun v => (Json.asStr v).toOption) |>.getD ""
    let paths ← orFail f.toString (do (← Json.asArr (← j.field "paths")).mapM Json.asStr)
    IO.println s!"{(f.fileName.getD "").take 8}  {time.take 19}  {host}  {", ".intercalate paths.toList}"
  return 0

def walkSnapshot (repo : System.FilePath) (key : MasterKey) (id : String) (target : Option System.FilePath)
    (list : Bool) : IO UInt32 := do
  let (_, j) ← snapshotJson repo key id
  let root ← orFail "snapshot" (j.strField "tree")
  let r ← openRepo repo key
  if let some t := target then IO.FS.createDirAll t
  let st ← r.walk root "" target list 1000 {}
  unless list do
    IO.println s!"restored {st.files} files and {st.dirs} directories, {st.bytes} bytes from {st.blobs} blobs, each checked against its ID"
    unless st.skipped.isEmpty do
      IO.println s!"not restored ({st.skipped.size}): {", ".intercalate st.skipped.toList}"
  return 0

def usage : String := "usage: lean-restic -r REPO ids
       lean-restic -r REPO [KEY] cat config
       lean-restic -r REPO [KEY] cat snapshot|index|lock|key ID
       lean-restic -r REPO [KEY] check
       lean-restic -r REPO [KEY] snapshots
       lean-restic -r REPO [KEY] ls SNAPSHOT
       lean-restic -r REPO [KEY] restore SNAPSHOT --target DIR
KEY is --password-file FILE or --masterkey FILE; without one, the password is read from RESTIC_PASSWORD"

/-- The master key: from `--masterkey FILE`, or from the password in `--password-file FILE` or
`RESTIC_PASSWORD`, as restic takes it. -/
def getKey (repo : System.FilePath) : List String → IO (MasterKey × List String)
  | "--masterkey" :: f :: rest => return (← loadMasterKey f, rest)
  | "--password-file" :: f :: rest => do
    let pw := (← IO.FS.readFile f).trimAsciiEnd.toString
    return (← unlock repo pw.toUTF8.toList, rest)
  | rest => do
    match ← IO.getEnv "RESTIC_PASSWORD" with
    | some pw => return (← unlock repo pw.toUTF8.toList, rest)
    | none => fail "no key: give --masterkey FILE or --password-file FILE, or set RESTIC_PASSWORD"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["-r", repo, "ids"] => ids repo
    | "-r" :: repo :: rest =>
      let (key, rest) ← getKey repo rest
      match rest with
      | ["check"] => check repo key
      | ["cat", "config"] =>
        IO.println (← openFile key (System.FilePath.mk repo / "config") (checkName := false)); return 0
      | ["cat", kind, id] =>
        let some dir := dirOf kind | IO.eprintln usage; return 2
        IO.println (← openFile key (← findFile (System.FilePath.mk repo / dir) id) (checkName := kind ≠ "key"))
        return 0
      | ["snapshots"] => snapshots repo key
      | ["ls", id] => walkSnapshot repo key id none true
      | ["restore", id, "--target", dir] => walkSnapshot repo key id (some dir) false
      | _ => IO.eprintln usage; return 2
    | _ => IO.eprintln usage; return 2
  catch e =>
    IO.eprintln s!"lean-restic: {e}"
    return 1
