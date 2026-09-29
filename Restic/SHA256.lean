import Restic.Bytes

/-!
# SHA-256

FIPS 180-4 §6.2, over byte strings. Restic names every file in a repository by the SHA-256 of its
contents, and every blob by the SHA-256 of its plaintext, so this is what ties a name to what it names.

Names follow the standard: `Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁` (§4.1.2), the constants `K` (§4.2.2), the
initial hash value `H⁽⁰⁾` (§5.3.3), padding (§5.1.1) and the computation (§6.2.2). The message
schedule keeps the last sixteen words and slides, so every function is structural recursion and the
kernel can run it. `Restic.Vectors` checks the FIPS 180-2 Appendix B examples.
-/

namespace Restic.SHA256

/-- `ROTRⁿ(x)`, §3.2. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- §4.1.2 (4.2). -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)
/-- §4.1.2 (4.3). -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
/-- `Σ₀`, §4.1.2 (4.4). -/
def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
/-- `Σ₁`, §4.1.2 (4.5). -/
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
/-- `σ₀`, §4.1.2 (4.6). -/
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
/-- `σ₁`, §4.1.2 (4.7). -/
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The 64 constants `K₀ … K₆₃`, §4.2.2. -/
def K : List UInt32 := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Eight working variables, or eight words of hash value. -/
structure Regs where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
  deriving DecidableEq, Repr

/-- `H⁽⁰⁾`, §5.3.3. -/
def H0 : Regs :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- Word `i` of a block, big-endian, §5.2.1. -/
def word (block : Bytes) (i : Nat) : UInt32 :=
  let b (j : Nat) : UInt32 := (block.getD (4 * i + j) 0).toUInt32
  (b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3

/-- `W₁₆, W₁₇, …`, `n` of them, from the sixteen words before (oldest first), §6.2.2 step 1:
`Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆`. -/
def extend : Nat → List UInt32 → List UInt32
  | 0, _ => []
  | n + 1, w =>
    let next := smallSigma1 (w.getD 14 0) + w.getD 9 0 + smallSigma0 (w.getD 1 0) + w.getD 0 0
    next :: extend n (w.tail ++ [next])

/-- The message schedule `W₀ … W₆₃` of one 64-byte block. -/
def schedule (block : Bytes) : List UInt32 :=
  let w := (List.range 16).map (word block)
  w ++ extend 48 w

/-- One step of §6.2.2 step 3. -/
def round (s : Regs) (k w : UInt32) : Regs :=
  let t1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + k + w
  let t2 := bigSigma0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Wordwise addition modulo `2³²`. -/
def Regs.add (x y : Regs) : Regs :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e, x.f + y.f, x.g + y.g, x.h + y.h⟩

/-- `H⁽ⁱ⁾` from `H⁽ⁱ⁻¹⁾` and block `i`, §6.2.2 steps 2–4. -/
def compress (hv : Regs) (block : Bytes) : Regs :=
  hv.add ((List.zip K (schedule block)).foldl (fun s kw => round s kw.1 kw.2) hv)

/-- Padding, §5.1.1: a 1 bit, zeros, and the length in bits as 64 big-endian bits, to a multiple of
512 bits. -/
def pad (m : Bytes) : Bytes :=
  m ++ [0x80] ++ List.replicate ((64 + 55 - m.length % 64) % 64) 0 ++ toBE 8 (8 * m.length)

/-- Cut into 64-byte blocks; `fuel` bounds the number of blocks. -/
def blocks : Nat → Bytes → List Bytes
  | 0, _ => []
  | _, [] => []
  | fuel + 1, m => m.take 64 :: blocks fuel (m.drop 64)

/-- A word as four big-endian bytes. -/
def wordBytes (w : UInt32) : Bytes := toBE 4 w.toNat

/-- The 32-byte digest `H₀ ‖ … ‖ H₇`. -/
def Regs.bytes (r : Regs) : Bytes :=
  [r.a, r.b, r.c, r.d, r.e, r.f, r.g, r.h].flatMap wordBytes

end SHA256

open SHA256 in
/-- SHA-256 of a byte string, FIPS 180-4. -/
def sha256 (m : Bytes) : Bytes :=
  let p := pad m
  ((blocks p.length p).foldl compress H0).bytes

theorem SHA256.pad_length (m : Bytes) : (SHA256.pad m).length % 64 = 0 := by
  simp [SHA256.pad]; omega

end Restic
