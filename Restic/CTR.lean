import Restic.AES

/-!
# Counter mode

NIST SP 800-38A §6.5, as Go's `crypto/cipher.NewCTR` runs it and restic uses it: the IV is the first
counter block, each later counter block is the previous one plus one as a 128-bit big-endian number
(wrapping at `2¹²⁸`), and byte `j` of the message is XORed with byte `j` of the concatenated cipher
outputs.

`ctrGo` walks the message one byte at a time and keeps the unused part of the current keystream block,
so it is structural recursion on the message: the kernel can run it and induction proves things
about it. The keystream never depends on the message, which is why encrypting twice gives the message
back (`ctr_ctr`) whatever the block cipher is.
-/

namespace Restic

/-- Counter block `i`: the IV plus `i`, modulo `2¹²⁸`, as 16 big-endian bytes. -/
def ctrBlock (iv : Bytes) (i : Nat) : Bytes := toBE 16 ((beNat iv + i) % 2 ^ 128)

/-- Counter mode from counter block `i` on, with `buf` the keystream bytes of block `i - 1` not yet
used. `E` is the block cipher with its key applied. -/
def ctrGo (E : Bytes → Bytes) (iv : Bytes) : Nat → Bytes → Bytes → Bytes
  | _, _, [] => []
  | i, [], b :: bs =>
    let ks := E (ctrBlock iv i)
    (b ^^^ ks.headD 0) :: ctrGo E iv (i + 1) ks.tail bs
  | i, x :: xs, b :: bs => (b ^^^ x) :: ctrGo E iv i xs bs

/-- Counter-mode encryption (and decryption) of `m` with block cipher `E` and initial counter `iv`. -/
def ctr (E : Bytes → Bytes) (iv m : Bytes) : Bytes := ctrGo E iv 0 [] m

theorem ctrGo_length (E : Bytes → Bytes) (iv : Bytes) (i : Nat) (buf m : Bytes) :
    (ctrGo E iv i buf m).length = m.length := by
  induction m generalizing i buf with
  | nil => cases buf <;> rfl
  | cons b bs ih => cases buf <;> simp [ctrGo, ih]

@[simp] theorem ctr_length (E : Bytes → Bytes) (iv m : Bytes) : (ctr E iv m).length = m.length :=
  ctrGo_length E iv 0 [] m

theorem ctrGo_ctrGo (E : Bytes → Bytes) (iv : Bytes) (i : Nat) (buf m : Bytes) :
    ctrGo E iv i buf (ctrGo E iv i buf m) = m := by
  induction m generalizing i buf with
  | nil => cases buf <;> rfl
  | cons b bs ih => cases buf <;> simp [ctrGo, ih, xor_xor_cancel_right]

/-- Counter mode undoes itself: the same key and IV decrypt what they encrypted. -/
theorem ctr_ctr (E : Bytes → Bytes) (iv m : Bytes) : ctr E iv (ctr E iv m) = m :=
  ctrGo_ctrGo E iv 0 [] m

theorem ctr_injective (E : Bytes → Bytes) (iv : Bytes) {m m' : Bytes} (h : ctr E iv m = ctr E iv m') :
    m = m' := by
  rw [← ctr_ctr E iv m, h, ctr_ctr]

/-! ## Agreement with the textbook definition

SP 800-38A writes counter mode as `Cᵢ = Pᵢ ⊕ CIPH_K(Tᵢ)`: the message XORed with the keystream
`E(T₀) ‖ E(T₁) ‖ …`, cut to the message's length. `ctr_eq_xor_keystream` proves `ctr` is exactly that,
for any block cipher that returns 16 bytes. -/

/-- The first `n` blocks of keystream from counter block `i` on. -/
def keystream (E : Bytes → Bytes) (iv : Bytes) : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, i => E (ctrBlock iv i) ++ keystream E iv n (i + 1)

theorem ctrGo_eq (E : Bytes → Bytes) (hE : ∀ x, (E x).length = 16) (iv : Bytes) (m : Bytes) :
    ∀ (i : Nat) (buf : Bytes) (n : Nat), m.length ≤ buf.length + 16 * n →
      ctrGo E iv i buf m = xorBytes m (buf ++ keystream E iv n i) := by
  induction m with
  | nil => intro i buf n _; cases buf <;> rfl
  | cons b bs ih =>
    intro i buf n hlen
    cases buf with
    | nil =>
      cases n with
      | zero => simp at hlen
      | succ n =>
        have hk := hE (ctrBlock iv i)
        obtain ⟨k, ks, hks⟩ : ∃ k ks, E (ctrBlock iv i) = k :: ks := by
          cases h : E (ctrBlock iv i) with
          | nil => rw [h] at hk; simp at hk
          | cons k ks => exact ⟨k, ks, rfl⟩
        rw [hks] at hk
        simp only [List.length_cons, List.length_nil] at hk hlen
        simp only [ctrGo, hks, List.headD_cons, List.tail_cons, keystream, List.nil_append,
          List.cons_append, xorBytes, List.zipWith_cons_cons]
        congr 1
        exact ih (i + 1) ks n (by omega)
    | cons x xs =>
      simp only [List.length_cons] at hlen
      simp only [ctrGo, xorBytes, List.cons_append, List.zipWith_cons_cons]
      congr 1
      exact ih i xs n (by omega)

/-- `ctr` is SP 800-38A counter mode: the message XORed with enough keystream blocks. -/
theorem ctr_eq_xor_keystream (E : Bytes → Bytes) (hE : ∀ x, (E x).length = 16) (iv m : Bytes) :
    ctr E iv m = xorBytes m (keystream E iv ((m.length + 15) / 16) 0) := by
  rw [ctr, ctrGo_eq E hE iv m 0 [] ((m.length + 15) / 16) (by simp; omega)]
  rfl

end Restic
