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

end Restic
