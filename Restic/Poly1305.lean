import Restic.Bytes

/-!
# Poly1305

The one-time authenticator of Bernstein's *The Poly1305-AES message-authentication code* (2005), in
the form RFC 8439 §2.5 gives it. The 32-byte key is `r ‖ s`. The message is cut into 16-byte chunks;
each chunk, read little-endian with a 1 appended above its top byte, is added to an accumulator,
which is then multiplied by the clamped `r` modulo `p = 2¹³⁰ - 5`. The tag is `(acc + s) mod 2¹²⁸`,
little-endian.

`polyGo` reads one byte at a time so that it is structural recursion on the message.
`Restic.Vectors` checks it against RFC 8439 §2.5.2 and against the Poly1305-AES vectors from
Bernstein's paper that restic's own tests use.
-/

namespace Restic

/-- The prime `2¹³⁰ - 5`. -/
def P1305 : Nat := 2 ^ 130 - 5

/-- Clear the bits of `r` that Poly1305 requires to be zero: the top four bits of bytes 3, 7, 11 and
15, and the bottom two bits of bytes 4, 8 and 12. -/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- The accumulator after the rest of the message, given `acc` so far and the partial chunk `cur` of
`len` bytes read so far. -/
def polyGo (r : Nat) : Nat → Nat → Nat → Bytes → Nat
  | acc, cur, len, [] => if len = 0 then acc else (acc + cur + 2 ^ (8 * len)) * r % P1305
  | acc, cur, len, b :: bs =>
    let cur := cur + b.toNat * 2 ^ (8 * len)
    if len = 15 then polyGo r ((acc + cur + 2 ^ 128) * r % P1305) 0 0 bs
    else polyGo r acc cur (len + 1) bs

/-- Poly1305 with the 32-byte one-time key `r ‖ s`. -/
def poly1305 (key m : Bytes) : Bytes :=
  let r := clamp (leNat (key.take 16))
  let s := leNat (key.drop 16)
  toLE 16 ((polyGo r 0 0 0 m + s) % 2 ^ 128)

@[simp] theorem poly1305_length (key m : Bytes) : (poly1305 key m).length = 16 := by
  simp [poly1305]

/-! ## Sixteen bytes at a time

`polyGo` reads one byte at a time, which is easy to reason about and slow to run: a big-number
multiplication per byte. `polyFast` reads a whole 16-byte chunk and does one multiplication per chunk,
as Poly1305 is usually written. `poly1305_eq_fast` proves they compute the same tag, and `@[csimp]`
makes compiled code use `poly1305Fast`. -/

/-- Poly1305's accumulator over the rest of the message, a chunk at a time. -/
def polyFast (r acc : Nat) (m : Bytes) : Nat :=
  -- `(m.drop 15).isEmpty` rather than `m.length < 16`: it looks at 16 cells, not the whole message.
  if (m.drop 15).isEmpty then
    if m = [] then acc else (acc + leNat m + 2 ^ (8 * m.length)) * r % P1305
  else
    polyFast r ((acc + leNat (m.take 16) + 2 ^ 128) * r % P1305) (m.drop 16)
termination_by m.length
decreasing_by simp_all [List.isEmpty_iff]; omega

/-- Reading bytes into a partial chunk just accumulates them little-endian. -/
theorem polyGo_append (r acc : Nat) (bs rest : Bytes) :
    ∀ (cur len : Nat), len + bs.length ≤ 15 →
      polyGo r acc cur len (bs ++ rest) = polyGo r acc (cur + leNat bs * 2 ^ (8 * len)) (len + bs.length) rest := by
  induction bs with
  | nil => intro cur len _; simp [leNat]
  | cons b bs ih =>
    intro cur len h
    simp only [List.length_cons] at h
    simp only [List.cons_append, polyGo, show len ≠ 15 by omega, ↓reduceIte]
    rw [ih _ _ (by omega)]
    have hp : 2 ^ (8 * (len + 1)) = 2 ^ (8 * len) * 256 := by
      rw [show 8 * (len + 1) = 8 * len + 8 by omega, Nat.pow_add]
    simp only [List.length_cons, leNat, hp, show len + 1 + bs.length = len + (bs.length + 1) by omega]
    grind

theorem polyGo_eq_fast (r : Nat) : ∀ (m : Bytes) (acc : Nat), polyGo r acc 0 0 m = polyFast r acc m := by
  intro m
  induction h : m.length using Nat.strongRecOn generalizing m with
  | ind n ih =>
    intro acc
    subst h
    rw [polyFast]
    by_cases h16 : 16 ≤ m.length
    · have hne : (m.drop 15).isEmpty = false := by simp [List.isEmpty_iff]; omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hsplit : m = m.take 15 ++ (m.drop 15).take 1 ++ m.drop 16 := by
        conv => lhs; rw [← List.take_append_drop 15 m, ← List.take_append_drop 1 (m.drop 15)]
        simp [List.drop_drop]
      obtain ⟨b, hb⟩ : ∃ b, (m.drop 15).take 1 = [b] := by
        cases hd : m.drop 15 with
        | nil => have := congrArg List.length hd; simp at this; omega
        | cons b _ => exact ⟨b, by simp⟩
      have h15 : (m.take 15).length = 15 := by simp; omega
      conv => lhs; rw [hsplit, hb, List.append_assoc]
      rw [polyGo_append r acc (m.take 15) ([b] ++ m.drop 16) 0 0 (by omega)]
      simp only [List.singleton_append, polyGo, Nat.zero_add, h15, ↓reduceIte]
      have h16' : m.take 16 = m.take 15 ++ [b] := by
        rw [← hb, ← List.take_add]
      rw [ih (m.drop 16).length (by simp; omega) (m.drop 16) rfl, h16', leNat_append, h15]
      simp [leNat]
      grind
    · have he : (m.drop 15).isEmpty = true := by simp [List.isEmpty_iff]; omega
      simp only [he, ↓reduceIte]
      have hm : m = m ++ [] := by simp
      rw [hm, polyGo_append r acc m [] 0 0 (by omega)]
      simp only [List.append_nil, Nat.zero_add, polyGo]
      by_cases he : m = []
      · subst he; simp
      · have : m.length ≠ 0 := by simpa using he
        simp [this, he]

/-- Poly1305, a chunk at a time. -/
def poly1305Fast (key m : Bytes) : Bytes :=
  let r := clamp (leNat (key.take 16))
  let s := leNat (key.drop 16)
  toLE 16 ((polyFast r 0 m + s) % 2 ^ 128)

/-- Compiled code runs `poly1305Fast` for `poly1305`; they are the same function. -/
@[csimp] theorem poly1305_eq_fast : @poly1305 = @poly1305Fast := by
  funext key m
  simp only [poly1305, poly1305Fast, polyGo_eq_fast]

end Restic
