import Restic
import Lean.Data.Json

/-!
# `lean-restic`: read a restic repository with the proved definitions

    lean-restic -r REPO --masterkey FILE cat config
    lean-restic -r REPO --masterkey FILE cat snapshot|index|lock|key ID
    lean-restic -r REPO ids

`FILE` is the JSON that `restic cat masterkey` prints. `ids` checks that every file in the repository
(except `config`) is named by the SHA-256 of its contents; it needs no key.

Everything that touches repository bytes is the specification in `Restic/`: `openBlob`, `sha256`,
`Base64.decode`. The JSON of the master key file is read with Lean's own `Lean.Json`, which is not part
of what is proved.
-/

open Restic

def hex (bs : Bytes) : String :=
  String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d.getD (b.toNat / 16) '0', d.getD (b.toNat % 16) '0'])

def readBytes (path : System.FilePath) : IO Bytes := do
  return (← IO.FS.readBinFile path).toList

def b64 (j : Lean.Json) (path : List String) : Except String Bytes := do
  let mut v := j
  for k in path do
    v ← v.getObjVal? k
  let s ← v.getStr?
  match Base64.decode s with
  | some bs => return bs
  | none => throw s!"{".".intercalate path} is not Base64"

def loadMasterKey (path : System.FilePath) : IO MasterKey := do
  let text ← IO.FS.readFile path
  let parsed : Except String MasterKey := do
    let j ← Lean.Json.parse text
    return ⟨← b64 j ["encrypt"], ← b64 j ["mac", "k"], ← b64 j ["mac", "r"]⟩
  match parsed with
  | .ok k =>
    unless k.valid do throw (IO.userError "the master key has the wrong lengths or an all-zero part")
    return k
  | .error e => throw (IO.userError s!"{path}: {e}")

def dirOf : String → Option String
  | "snapshot" => some "snapshots"
  | "index" => some "index"
  | "lock" => some "locks"
  | "key" => some "keys"
  | _ => none

/-- The one file in `dir` whose name starts with `id`. -/
def findFile (dir : System.FilePath) (id : String) : IO System.FilePath := do
  let entries ← dir.readDir
  match entries.toList.filter (·.fileName.startsWith id) with
  | [e] => return e.path
  | [] => throw (IO.userError s!"no file in {dir} starts with {id}")
  | _ => throw (IO.userError s!"more than one file in {dir} starts with {id}")

def explain : OpenError → String
  | .invalidKey => "invalid key"
  | .tooShort => "too short to be an encrypted object"
  | .invalidIV => "the IV is all zero"
  | .unauthenticated => "MAC mismatch: wrong key, or the file was changed"

/-- Restic's unpacked format: version 1 is plain JSON; version 2 puts an encoding byte first, where
`[` or `{` means the whole plaintext is JSON and 2 means zstd-compressed JSON. -/
def unpacked (pt : Bytes) : Except String String := do
  match pt with
  | 2 :: _ => throw "compressed with zstd (repository format 2); not supported yet"
  | _ =>
    match String.fromUTF8? (ByteArray.mk pt.toArray) with
    | some s => return s
    | none => throw "the plaintext is not UTF-8"

def catFile (key : MasterKey) (path : System.FilePath) : IO Unit := do
  match openBlob key (← readBytes path) with
  | .error e => throw (IO.userError s!"{path}: {explain e}")
  | .ok pt =>
    match unpacked pt with
    | .ok s => IO.println s
    | .error e => throw (IO.userError s!"{path}: {e}")

partial def filesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.pathExists) then return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← filesUnder e.path)
    else out := out.push e.path
  return out

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

def usage : String := "usage: lean-restic -r REPO --masterkey FILE cat config
       lean-restic -r REPO --masterkey FILE cat snapshot|index|lock|key ID
       lean-restic -r REPO ids"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["-r", repo, "ids"] => ids repo
    | ["-r", repo, "--masterkey", mk, "cat", "config"] =>
      catFile (← loadMasterKey mk) (System.FilePath.mk repo / "config"); return 0
    | ["-r", repo, "--masterkey", mk, "cat", kind, id] =>
      let some dir := dirOf kind | IO.eprintln usage; return 2
      let key ← loadMasterKey mk
      catFile key (← findFile (System.FilePath.mk repo / dir) id); return 0
    | _ => IO.eprintln usage; return 2
  catch e =>
    IO.eprintln s!"lean-restic: {e}"
    return 1
