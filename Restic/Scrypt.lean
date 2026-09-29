import Restic.SHA256

/-!
# HMAC-SHA256, PBKDF2 and scrypt

What turns a repository password into the key that opens a key file (design.rst, "Keys, Encryption
and MAC"): scrypt with the file's `N`, `r`, `p` and salt, 64 bytes out. The first 32 are the AES-256
key; the last 32 are the MAC key `k ‖ r`.

* HMAC: RFC 2104 with SHA-256.
* PBKDF2: RFC 8018 §5.2 with HMAC-SHA256.
* scrypt: RFC 7914. `Salsa20/8` (§3), `scryptBlockMix` (§4), `scryptROMix` (§5), `scrypt` (§6). The
  large vector `V` is a flat array of 32-bit words.

`Restic.Vectors` checks HMAC and PBKDF2 against RFC 4231 and RFC 7914 §11, and scrypt against RFC 7914
§12, by kernel evaluation.
-/

namespace Restic

/-! ## HMAC and PBKDF2 -/

/-- HMAC-SHA256, RFC 2104. -/
def hmacSha256 (key msg : Bytes) : Bytes :=
  let k := if key.length > 64 then sha256 key else key
  let k := k ++ List.replicate (64 - k.length) 0
  let ipad := k.map (· ^^^ 0x36)
  let opad := k.map (· ^^^ 0x5c)
  sha256 (opad ++ sha256 (ipad ++ msg))

/-- `U_c` of RFC 8018 §5.2, XORed together: `U_1 ⊕ … ⊕ U_c`. -/
def pbkdf2Block (p : Bytes) : Nat → Bytes → Bytes → Bytes
  | 0, _, acc => acc
  | c + 1, u, acc =>
    let u' := hmacSha256 p u
    pbkdf2Block p c u' (xorBytes acc u')

/-- PBKDF2-HMAC-SHA256 with `c` iterations, `dkLen` bytes out. -/
def pbkdf2 (p s : Bytes) (c dkLen : Nat) : Bytes :=
  let blocks := (dkLen + 31) / 32
  let out := (List.range blocks).flatMap fun i =>
    let u1 := hmacSha256 p (s ++ toBE 4 (i + 1))
    pbkdf2Block p (c - 1) u1 u1
  out.take dkLen

/-! ## Salsa20/8, RFC 7914 §3 -/

def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The Salsa20 quarter-round on words `a b c d` of `x`. -/
def qr (x : Array UInt32) (a b c d : Nat) : Array UInt32 :=
  let x := x.set! b (x[b]! ^^^ rotl32 (x[a]! + x[d]!) 7)
  let x := x.set! c (x[c]! ^^^ rotl32 (x[b]! + x[a]!) 9)
  let x := x.set! d (x[d]! ^^^ rotl32 (x[c]! + x[b]!) 13)
  x.set! a (x[a]! ^^^ rotl32 (x[d]! + x[c]!) 18)

/-- Salsa20/8 core on 16 words: four double rounds, then the input added back. -/
def salsa8 (input : Array UInt32) : Array UInt32 := Id.run do
  let mut x := input
  for _ in [0:4] do
    x := qr x 0 4 8 12
    x := qr x 5 9 13 1
    x := qr x 10 14 2 6
    x := qr x 15 3 7 11
    x := qr x 0 1 2 3
    x := qr x 5 6 7 4
    x := qr x 10 11 8 9
    x := qr x 15 12 13 14
  let mut out := Array.mkEmpty 16
  for i in [0:16] do
    out := out.push (x[i]! + input[i]!)
  return out

/-! ## scrypt, RFC 7914 §4–6 -/

/-- `scryptBlockMix` on `2r` 64-byte blocks, as `32r` words. -/
def blockMix (r : Nat) (b : Array UInt32) : Array UInt32 := Id.run do
  let mut x := b.extract (32 * r - 16) (32 * r)
  let mut ys : Array (Array UInt32) := Array.mkEmpty (2 * r)
  for i in [0:2 * r] do
    let mut t := Array.mkEmpty 16
    for k in [0:16] do
      t := t.push (x[k]! ^^^ b[16 * i + k]!)
    x := salsa8 t
    ys := ys.push x
  let mut out := Array.mkEmpty (32 * r)
  for i in [0:r] do out := out ++ ys[2 * i]!
  for i in [0:r] do out := out ++ ys[2 * i + 1]!
  return out

/-- `scryptROMix` with cost `n`. -/
def roMix (r n : Nat) (b : Array UInt32) : Array UInt32 := Id.run do
  let w := 32 * r
  let mut x := b
  let mut v : Array UInt32 := Array.mkEmpty (n * w)
  for _ in [0:n] do
    v := v ++ x
    x := blockMix r x
  for _ in [0:n] do
    let j := x[w - 16]!.toNat % n
    let mut t := Array.mkEmpty w
    for k in [0:w] do
      t := t.push (x[k]! ^^^ v[j * w + k]!)
    x := blockMix r t
  return x

def wordsOfBytes (bs : Bytes) : Array UInt32 :=
  ((List.range (bs.length / 4)).map fun i =>
    let b (k : Nat) : UInt32 := (bs.getD (4 * i + k) 0).toUInt32
    b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24)).toArray

def bytesOfWords (ws : Array UInt32) : Bytes :=
  ws.toList.flatMap fun w => toLE 4 w.toNat

/-- scrypt, RFC 7914 §6. -/
def scrypt (password salt : Bytes) (n r p dkLen : Nat) : Bytes :=
  let blockLen := 128 * r
  let b := pbkdf2 password salt 1 (p * blockLen)
  let mixed := (List.range p).flatMap fun i =>
    bytesOfWords (roMix r n (wordsOfBytes ((b.drop (i * blockLen)).take blockLen)))
  pbkdf2 password mixed 1 dkLen

end Restic
