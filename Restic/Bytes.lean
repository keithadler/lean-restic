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

namespace Restic

/-! ## Little-endian numbers: encoding and decoding are inverse -/

theorem toNat_ofNat8 (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := Nat.add_zero _

theorem leNat_toLE (k n : Nat) : leNat (toLE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [toLE, leNat, Nat.mod_one]
  | succ k ih =>
    simp only [toLE, leNat, ih, Nat.toUInt8, toNat_ofNat8, Nat.pow_succ']
    rw [Nat.mod_mul]
    omega

theorem leNat_lt (bs : Bytes) : leNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ']
    have := b.toNat_lt
    omega

theorem toLE_leNat (bs : Bytes) : toLE bs.length (leNat bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, toLE, leNat]
    have hb := b.toNat_lt
    have h1 : (b.toNat + 256 * leNat bs) % 256 = b.toNat := by omega
    have h2 : (b.toNat + 256 * leNat bs) / 256 = leNat bs := by omega
    rw [h1, h2, ih]
    simp [Nat.toUInt8]

end Restic

namespace Restic

/-! ## Big-endian numbers -/

theorem beNat_append_singleton (l : Bytes) (x : UInt8) : beNat (l ++ [x]) = 256 * beNat l + x.toNat := by
  simp [beNat, List.foldl_append]

theorem beNat_reverse (l : Bytes) : beNat l.reverse = leNat l := by
  induction l with
  | nil => rfl
  | cons b bs ih => rw [List.reverse_cons, beNat_append_singleton, ih, leNat]; omega

theorem beNat_toBE (k n : Nat) : beNat (toBE k n) = n % 256 ^ k := by
  rw [toBE, beNat_reverse, leNat_toLE]

end Restic
