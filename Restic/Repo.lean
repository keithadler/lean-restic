import Restic.Pack
import Restic.Zstd
import Restic.Json
import Restic.Scrypt
import Restic.Base64
import Std.Data.HashMap

/-!
# Reading a repository

The I/O around the proved core: find files, load the index, fetch blobs, walk trees.

Every byte handed to a caller has been through the same checks:

* each object is opened with `openBlob`, so it is authenticated under the master key;
* each blob's plaintext (decompressed, for a compressed blob) must hash to the ID it was asked for;
* snapshot, index and key files must hash to their file names;
* a tree names each subtree and each file chunk by ID, so a restored file is tied by an unbroken chain of
  SHA-256 hashes to the snapshot file, and the snapshot file to its own name.

The index only says where to look; a wrong index entry can make a lookup fail, never return wrong bytes.
-/

namespace Restic.Repo

open Std

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- Lower-case hexadecimal. -/
def hex (bs : Bytes) : String := String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def readBytes (path : System.FilePath) : IO Bytes := do
  return (← IO.FS.readBinFile path).toList

def explainOpen : OpenError → String
  | .invalidKey => "invalid key"
  | .tooShort => "too short to be an encrypted object"
  | .invalidIV => "the IV is all zero"
  | .unauthenticated => "MAC mismatch: wrong key, or the file was changed"

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

def orFail {α : Type} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => fail s!"{ctx}: {e}"

/-- Restic's unpacked encoding (design.rst, "Unpacked Data Format"): format 1 is plain JSON; format 2
starts with a version byte, where `[` or `{` means plain JSON and 2 means zstd-compressed JSON. -/
def unpacked (pt : Bytes) : Except String String := do
  let json ← match pt with
    | 2 :: rest => Zstd.decompress (ByteArray.mk rest.toArray)
    | 0x5b :: _ | 0x7b :: _ => pure (ByteArray.mk pt.toArray)
    | _ => throw "unknown encoding version"
  match String.fromUTF8? json with
  | some s => return s
  | none => throw "the plaintext is not UTF-8"

/-- Open a snapshot, index or lock file: it must hash to its name, authenticate, and decode. -/
def openFile (key : MasterKey) (path : System.FilePath) (checkName := true) : IO String := do
  let data ← readBytes path
  if checkName ∧ hex (sha256 data) ≠ path.fileName.getD "" then
    fail s!"{path}: contents do not hash to the file name"
  match openBlob key data with
  | .error e => fail s!"{path}: {explainOpen e}"
  | .ok pt => orFail path.toString (unpacked pt)

partial def filesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.pathExists) then return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← filesUnder e.path)
    else out := out.push e.path
  return out

/-- The one file in `dir` whose name starts with `id`. -/
def findFile (dir : System.FilePath) (id : String) : IO System.FilePath := do
  let entries ← filesUnder dir
  match entries.toList.filter (fun p => (p.fileName.getD "").startsWith id) with
  | [e] => return e
  | [] => fail s!"no file in {dir} starts with {id}"
  | _ => fail s!"more than one file in {dir} starts with {id}"

/-- Where a blob is, as the index says. -/
structure Loc where
  pack : String
  offset : Nat
  length : Nat
  rawLength : Option Nat

/-- An open repository. -/
structure Repo where
  root : System.FilePath
  key : MasterKey
  index : HashMap String Loc
  cache : IO.Ref (Option (String × ByteArray))

def loadIndex (root : System.FilePath) (key : MasterKey) : IO (HashMap String Loc) := do
  let mut m : HashMap String Loc := {}
  for f in ← filesUnder (root / "index") do
    let j ← orFail f.toString (Json.parse (← openFile key f))
    for p in ← orFail "index" (do Json.asArr (← j.field "packs")) do
      let (packId, blobs) ← orFail "index" (do pure (← p.strField "id", ← Json.asArr (← p.field "blobs")))
      for b in blobs do
        let (id, off, len) ← orFail "index" (do pure (← b.strField "id", ← b.natField "offset", ← b.natField "length"))
        let raw ← match b.get? "uncompressed_length" with
          | some v => some <$> orFail "index" (Json.asNat v)
          | none => pure none
        m := m.insert id ⟨packId, off, len, raw⟩
  return m

def openRepo (root : System.FilePath) (key : MasterKey) : IO Repo := do
  return ⟨root, key, ← loadIndex root key, ← IO.mkRef none⟩

def Repo.packPath (r : Repo) (packId : String) : System.FilePath :=
  r.root / "data" / (String.ofList (packId.toList.take 2)) / packId

/-- Fetch blob `id`: read it from its pack, authenticate it, decompress it if needed, and check that it
hashes to `id`. -/
def Repo.blob (r : Repo) (id : String) : IO Bytes := do
  let some loc := r.index.get? id | fail s!"blob {id} is not in the index"
  let data ← match ← r.cache.get with
    | some (p, d) => if p = loc.pack then pure d else IO.FS.readBinFile (r.packPath loc.pack)
    | none => IO.FS.readBinFile (r.packPath loc.pack)
  r.cache.set (some (loc.pack, data))
  if loc.offset + loc.length > data.size then fail s!"blob {id}: the index points past the end of its pack"
  let piece := (data.extract loc.offset (loc.offset + loc.length)).toList
  let pt ← match openBlob r.key piece with
    | .error e => fail s!"blob {id}: {explainOpen e}"
    | .ok pt => pure pt
  let pt ← match loc.rawLength with
    | none => pure pt
    | some n => do
      let out ← orFail s!"blob {id}: zstd" (Zstd.decompress (ByteArray.mk pt.toArray))
      if out.size ≠ n then fail s!"blob {id}: decompresses to {out.size} bytes, index says {n}"
      pure out.toList
  if hex (sha256 pt) ≠ id then fail s!"blob {id}: plaintext does not hash to its ID"
  return pt

/-- A tree blob, parsed. -/
def Repo.tree (r : Repo) (id : String) : IO (Array Json) := do
  let pt ← r.blob id
  let some s := String.fromUTF8? (ByteArray.mk pt.toArray) | fail s!"tree {id}: not UTF-8"
  let j ← orFail s!"tree {id}" (Json.parse s)
  orFail s!"tree {id}" (do Json.asArr (← j.field "nodes"))

/-- A file name from a tree must be one path component. -/
def safeName (name : String) : Bool :=
  name ≠ "" ∧ name ≠ "." ∧ name ≠ ".." ∧ !name.contains '/' ∧ !name.contains '\x00'

/-- What a walk did. -/
structure Stats where
  files : Nat := 0
  dirs : Nat := 0
  bytes : Nat := 0
  blobs : Nat := 0
  skipped : Array String := #[]

/-- Walk the tree `id` at `path`. With `target`, write files and directories under it. `fuel` bounds
the depth. -/
def Repo.walk (r : Repo) (id : String) (path : String) (target : Option System.FilePath) (list : Bool) :
    Nat → Stats → IO Stats
  | 0, _ => fail "trees nested deeper than the fuel"
  | fuel + 1, st => do
    let mut st := st
    for node in ← r.tree id do
      let (name, ty) ← orFail s!"tree {id}" (do pure (← node.strField "name", ← node.strField "type"))
      unless safeName name do fail s!"tree {id}: unsafe file name {name.quote}"
      let p := path ++ "/" ++ name
      if ty = "dir" then
        let sub ← orFail s!"tree {id}" (node.strField "subtree")
        if list then IO.println (p ++ "/")
        if let some t := target then IO.FS.createDirAll (t / (p.drop 1).toString)
        st := { st with dirs := st.dirs + 1 }
        st ← r.walk sub p target list fuel st
      else if ty = "file" then
        -- Go's encoding/json omits an empty file's `size` and `content` (omitempty).
        let size ← match node.get? "size" with
          | some v => orFail s!"tree {id}" (Json.asNat v)
          | none => pure 0
        let content ← match node.get? "content" with
          | some v => orFail s!"tree {id}" (Json.asArr v)
          | none => pure #[]
        if list then IO.println s!"{p}  {size}"
        let h ← match target with
          | some t => some <$> IO.FS.Handle.mk (t / (p.drop 1).toString) .write
          | none => pure none
        let mut n := 0
        for c in content do
          let cid ← orFail s!"tree {id}" (Json.asStr c)
          let data ← r.blob cid
          n := n + data.length
          st := { st with blobs := st.blobs + 1 }
          if let some h := h then h.write (ByteArray.mk data.toArray)
        if n ≠ size then fail s!"{p}: content is {n} bytes, tree says {size}"
        st := { st with files := st.files + 1, bytes := st.bytes + n }
      else
        if list then IO.println s!"{p}  ({ty}, not restored)"
        st := { st with skipped := st.skipped.push s!"{p} ({ty})" }
    return st

/-! ## Unlocking with a password

A key file (design.rst, "Keys, Encryption and MAC") holds scrypt parameters, a salt, and the master key
sealed under a key derived from the password: scrypt gives 64 bytes, the first 32 the AES-256 key, the
last 32 the MAC key `k ‖ r`. Opening the sealed data authenticates the password: a wrong one fails the
MAC. -/

def b64Field (j : Json) (k : String) : Except String Bytes := do
  match Base64.decode (← j.strField k) with
  | some bs => pure bs
  | none => throw s!"{k} is not Base64"

/-- Try one key file with the password. -/
def tryKeyFile (path : System.FilePath) (password : Bytes) : IO (Option MasterKey) := do
  let data ← readBytes path
  if hex (sha256 data) ≠ path.fileName.getD "" then fail s!"{path}: contents do not hash to the file name"
  let some text := String.fromUTF8? (ByteArray.mk data.toArray) | fail s!"{path}: not UTF-8"
  let j ← orFail path.toString (Json.parse text)
  let (kdf, n, r, p, salt, sealed) ← orFail path.toString (do
    pure (← j.strField "kdf", ← j.natField "N", ← j.natField "r", ← j.natField "p",
      ← b64Field j "salt", ← b64Field j "data"))
  unless kdf = "scrypt" do fail s!"{path}: unknown key derivation {kdf}"
  if n < 2 ∨ n &&& (n - 1) ≠ 0 ∨ r = 0 ∨ p = 0 ∨ n * r > 1 <<< 24 ∨ p > 64 then
    fail s!"{path}: unreasonable scrypt parameters N={n} r={r} p={p}"
  let dk := scrypt password salt n r p 64
  let userKey : MasterKey := ⟨dk.take 32, (dk.drop 32).take 16, dk.drop 48⟩
  match openBlob userKey sealed with
  | .error _ => return none
  | .ok pt =>
    let some mtext := String.fromUTF8? (ByteArray.mk pt.toArray) | fail s!"{path}: master key is not UTF-8"
    let mj ← orFail path.toString (Json.parse mtext)
    let mk ← orFail path.toString (do
      let mac ← mj.field "mac"
      pure (⟨← b64Field mj "encrypt", ← b64Field mac "k", ← b64Field mac "r"⟩ : MasterKey))
    unless mk.valid do fail s!"{path}: the master key has the wrong lengths or an all-zero part"
    return some mk

/-- The master key, from the first key file the password opens. -/
def unlock (root : System.FilePath) (password : Bytes) : IO MasterKey := do
  let files ← filesUnder (root / "keys")
  if files.isEmpty then fail "the repository has no key files"
  for f in files do
    if let some mk ← tryKeyFile f password then return mk
  fail "wrong password: no key file opens with it"

end Restic.Repo
