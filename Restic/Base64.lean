import Restic.Bytes

/-!
# Base64

RFC 4648 §4, the standard alphabet with `=` padding, as Go's `encoding/json` writes `[]byte` fields.
Restic keeps keys in this form: the master key's parts, and a key file's salt and encrypted data.
A key decoded wrongly shows up as a MAC failure in `openBlob`, not as wrong plaintext (short of a
forged tag, the assumption `Restic.Seal` names). `test/base64.py`
compares both directions with Python's `base64` module.
-/

namespace Restic.Base64

/-- The alphabet, RFC 4648 Table 1. -/
def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

/-- The value of one character, if it is in the alphabet. -/
def value (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- The character for a value below 64. -/
def char (n : Nat) : Char := alphabet.getD n '='

/-- Decode a whole string: groups of four characters, the last possibly padded. Unused low bits of
a padded group must be zero, as in Go's strict decoding. -/
def decodeChars : List Char → Option Bytes
  | [] => some []
  | [a, b, '=', '='] => do
    let x := (← value a) * 64 + (← value b)
    if x % 16 ≠ 0 then none
    return [(x / 16).toUInt8]
  | [a, b, c, '='] => do
    let x := ((← value a) * 64 + (← value b)) * 64 + (← value c)
    if x % 4 ≠ 0 then none
    return [(x / 1024).toUInt8, (x / 4 % 256).toUInt8]
  | a :: b :: c :: d :: rest => do
    let x := (((← value a) * 64 + (← value b)) * 64 + (← value c)) * 64 + (← value d)
    let tail ← decodeChars rest
    return [(x / 65536).toUInt8, (x / 256 % 256).toUInt8, (x % 256).toUInt8] ++ tail
  | _ => none

/-- Decode a Base64 string. -/
def decode (s : String) : Option Bytes := decodeChars s.toList

/-- Encode bytes as characters. -/
def encodeBytes : Bytes → List Char
  | [] => []
  | [x] =>
    let n := x.toNat * 16
    [char (n / 64), char (n % 64), '=', '=']
  | [x, y] =>
    let n := (x.toNat * 256 + y.toNat) * 4
    [char (n / 4096), char (n / 64 % 64), char (n % 64), '=']
  | x :: y :: z :: rest =>
    let n := (x.toNat * 256 + y.toNat) * 256 + z.toNat
    [char (n / 262144), char (n / 4096 % 64), char (n / 64 % 64), char (n % 64)] ++ encodeBytes rest

/-- Encode bytes as a Base64 string. -/
def encode (bs : Bytes) : String := String.ofList (encodeBytes bs)

theorem value_char (n : Nat) (h : n < 64) : value (char n) = some n := by
  have : ∀ m < 64, value (char m) = some m := by decide +kernel
  exact this n h

end Restic.Base64
