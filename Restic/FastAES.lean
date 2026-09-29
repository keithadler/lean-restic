import AES.Linear
import Restic.AES

/-!
# A fast AES-256, proved equal to the specification

The specification recomputes the key schedule for every block and multiplies in GF(2⁸) with a loop,
so it runs at about 400 KiB/s. This file gives the standard fast form (Daemen and Rijmen, *The Design
of Rijndael*, §4.2) and proves it computes the same function:

* the round keys are expanded once per key, into an array;
* `SubBytes`, `ShiftRows` and `MixColumns` together become four table lookups per column. The tables
  are computed from the specification's own `sbox` and `mixColumn`, not typed in: `T0[a]` is
  `mixColumn ⟨sbox a, 0, 0, 0⟩`, and so on. That four lookups XORed together give `mixColumn` of the
  whole column is `mixColumn`'s linearity, which lean-aes proves (`mixColumn_xor`).

`aes256_eq_fast` is marked `@[csimp]`: compiled code calls `aes256Fast` wherever the specification says
`aes256`. The kernel-checked vectors still evaluate the specification itself.
-/

namespace Restic

open AES

/-- Column `j`'s contribution table: `mixColumn` of a column with `sbox a` in row `j` and zeros
elsewhere. -/
def tTable (j : Nat) : Array Word :=
  Array.ofFn (n := 256) fun i =>
    let s := sbox i.val.toUInt8
    mixColumn (match j with
      | 0 => ⟨s, 0, 0, 0⟩
      | 1 => ⟨0, s, 0, 0⟩
      | 2 => ⟨0, 0, s, 0⟩
      | _ => ⟨0, 0, 0, s⟩)

def T0 : Array Word := tTable 0
def T1 : Array Word := tTable 1
def T2 : Array Word := tTable 2
def T3 : Array Word := tTable 3

theorem tTable_get (j : Nat) (a : Byte) :
    (tTable j).getD a.toNat 0 = mixColumn (match j with
      | 0 => ⟨sbox a, 0, 0, 0⟩
      | 1 => ⟨0, sbox a, 0, 0⟩
      | 2 => ⟨0, 0, sbox a, 0⟩
      | _ => ⟨0, 0, 0, sbox a⟩) := by
  have h := a.toNat_lt
  simp [tTable, Array.getD, h]

/-- `mixColumn` of a column after `SubBytes`, as four lookups. -/
def colT (a b c d : Byte) : Word :=
  T0.getD a.toNat 0 ^^^ T1.getD b.toNat 0 ^^^ T2.getD c.toNat 0 ^^^ T3.getD d.toNat 0

theorem colT_eq (a b c d : Byte) : colT a b c d = mixColumn ⟨sbox a, sbox b, sbox c, sbox d⟩ := by
  have split : (⟨sbox a, sbox b, sbox c, sbox d⟩ : Word) =
      (⟨sbox a, 0, 0, 0⟩ : Word) ^^^ ⟨0, sbox b, 0, 0⟩ ^^^ ⟨0, 0, sbox c, 0⟩ ^^^ ⟨0, 0, 0, sbox d⟩ := by
    simp [UInt8.xor_zero, UInt8.zero_xor]
  rw [split, mixColumn_xor, mixColumn_xor, mixColumn_xor]
  simp only [colT, T0, T1, T2, T3, tTable_get]

/-- One full round: `AddRoundKey(MixColumns(ShiftRows(SubBytes s)), k)`, by lookups. -/
def roundT (s k : State) : State :=
  ⟨colT s.c0.b0 s.c1.b1 s.c2.b2 s.c3.b3 ^^^ k.c0,
   colT s.c1.b0 s.c2.b1 s.c3.b2 s.c0.b3 ^^^ k.c1,
   colT s.c2.b0 s.c3.b1 s.c0.b2 s.c1.b3 ^^^ k.c2,
   colT s.c3.b0 s.c0.b1 s.c1.b2 s.c2.b3 ^^^ k.c3⟩

theorem roundT_eq (s k : State) :
    roundT s k = addRoundKey (mixColumns (shiftRows (subBytes s))) k := by
  obtain ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := s
  simp only [roundT, colT_eq, addRoundKey, mixColumns, shiftRows, subBytes, State.mapCols_mk, Word.map_mk,
    State.xor_def]

/-- Rounds `r, r+1, …`, `n` of them, reading round keys from an array. -/
def cipherRoundsT (rks : Array State) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, r, s => cipherRoundsT rks n (r + 1) (roundT s (rks.getD r 0))

theorem cipherRoundsT_eq (rks : Array State) (n r : Nat) (s : State) :
    cipherRoundsT rks n r s = cipherRounds (fun i => rks.getD i 0) n r s := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih => simp only [cipherRoundsT, cipherRounds, ih, roundT_eq]

/-- The fourteen rounds of AES-256 with precomputed round keys. -/
def cipherT (rks : Array State) (input : State) : State :=
  let s := addRoundKey input (rks.getD 0 0)
  let s := cipherRoundsT rks (Nr - 1) 1 s
  addRoundKey (shiftRows (subBytes s)) (rks.getD Nr 0)

theorem getD_of_length_le {α : Type} (l : List α) (n : Nat) (d : α) (h : l.length ≤ n) : l.getD n d = d := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n => simp only [List.getD_cons_succ]; exact ih n (by simp at h; omega)

/-- The fifteen round keys of AES-256, once. -/
def expandKey256 (key : Bytes) : Array State :=
  ((List.range 15).map (roundKey (keyExpansion (Key.ofNat (beNat key))))).toArray

theorem expandKey256_getD (key : Bytes) (i : Nat) :
    (expandKey256 key).getD i 0 = roundKey (keyExpansion (Key.ofNat (beNat key))) i := by
  unfold expandKey256
  by_cases hi : i < 15
  · simp [Array.getD, hi]
  · have hlen : (keyExpansion (Key.ofNat (beNat key))).length = 60 := rfl
    simp only [Array.getD, List.size_toArray, List.length_map, List.length_range, hi, ↓reduceDIte]
    simp only [roundKey, State.zero_def, Word.zero_def]
    rw [getD_of_length_le _ _ _ (by omega), getD_of_length_le _ _ _ (by omega),
      getD_of_length_le _ _ _ (by omega), getD_of_length_le _ _ _ (by omega)]

/-- AES-256 with precomputed round keys and table lookups. -/
def aes256Keyed (rks : Array State) (block : Bytes) : Bytes := (cipherT rks (stateOf block)).toList

/-- Expand the key once, then encrypt any number of blocks. -/
def aes256Fast (key : Bytes) : Bytes → Bytes :=
  let rks := expandKey256 key
  fun block => aes256Keyed rks block

/-- The fast form is the specification. -/
@[csimp] theorem aes256_eq_fast : @aes256 = @aes256Fast := by
  funext key block
  simp only [aes256Fast, aes256Keyed, cipherT, cipherRoundsT_eq, expandKey256_getD, aes256, AES.encrypt,
    cipher]

end Restic
