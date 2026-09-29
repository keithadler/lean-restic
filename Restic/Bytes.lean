/-!
# Bytes

Everything in this library is a function on `List UInt8`. Lists are slow to run over large inputs, but
they are what the kernel evaluates and what induction works on, so the specification is written over
them. A byte string is read as a number in either byte order; the test vectors are written as one
hexadecimal `Nat` literal plus a length, which the kernel handles with its fast arithmetic.
-/

namespace Restic

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- The number whose little-endian encoding is these bytes: the first byte is the least significant. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- The number whose big-endian encoding is these bytes: the first byte is the most significant. -/
def beNat (bs : Bytes) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- The low `k` bytes of `n`, least significant first. -/
def toLE : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: toLE k (n / 256)

/-- The low `k` bytes of `n`, most significant first. -/
def toBE (k n : Nat) : Bytes := (toLE k n).reverse

/-- A byte string written as a hexadecimal number and its length: `bytes 2 0x0a0b = [0x0a, 0x0b]`. -/
abbrev bytes (k n : Nat) : Bytes := toBE k n

/-- Bytewise exclusive or, as long as the shorter argument. -/
def xorBytes (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

@[simp] theorem toLE_length (k n : Nat) : (toLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [toLE, ih]

@[simp] theorem toBE_length (k n : Nat) : (toBE k n).length = k := by simp [toBE]

theorem xor_xor_cancel_right (a b : UInt8) : a ^^^ b ^^^ b = a := by
  rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

end Restic
