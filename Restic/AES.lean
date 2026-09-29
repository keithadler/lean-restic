import AES.Spec
import AES.RoundTrip
import Restic.Bytes

/-!
# AES on byte strings

Restic uses AES twice: AES-256 in counter mode encrypts, and AES-128 turns the nonce into the one-time
part of the Poly1305-AES key. The block cipher is the FIPS-197 specification from
[lean-aes](https://github.com/keithadler/lean-aes), whose round functions are proved invertible there.
lean-aes specializes the key schedule to AES-256, so the AES-128 key schedule (Algorithm 2 with
`Nk = 4`, `Nr = 10`) is added here on top of its round functions, and checked against FIPS-197
Appendices A.1 and C.1 in `Restic.Vectors`.
-/

namespace Restic

open AES

/-! ## AES-128 key expansion, FIPS-197 §5.2 with `Nk = 4` -/

/-- The last four words `w[i-4] … w[i-1]`, oldest first. -/
structure Window4 where
  /-- `w[i-4]`. -/
  w0 : Word
  /-- `w[i-3]`. -/
  w1 : Word
  /-- `w[i-2]`. -/
  w2 : Word
  /-- `w[i-1]`. -/
  w3 : Word

/-- The body of the loop in Algorithm 2 for `Nk = 4`. -/
def nextWord128 (i : Nat) (win : Window4) : Word :=
  let temp := if i % 4 = 0 then subWord (rotWord win.w3) ^^^ rcon (i / 4) else win.w3
  win.w0 ^^^ temp

/-- `w[i], w[i+1], …`, `n` of them, given the four words before `w[i]`. -/
def expandFrom128 : Nat → Nat → Window4 → List Word
  | 0, _, _ => []
  | n + 1, i, win =>
    let w := nextWord128 i win
    w :: expandFrom128 n (i + 1) ⟨win.w1, win.w2, win.w3, w⟩

/-- A 128-bit key as four words, from its 16 bytes. -/
def key128Words (k : Bytes) : Window4 :=
  let w (i : Nat) : Word := ⟨k.getD (4 * i) 0, k.getD (4 * i + 1) 0, k.getD (4 * i + 2) 0, k.getD (4 * i + 3) 0⟩
  ⟨w 0, w 1, w 2, w 3⟩

/-- `KeyExpansion` for AES-128: the `4 * (10 + 1) = 44` words `w[0] … w[43]`. -/
def keyExpansion128 (k : Bytes) : List Word :=
  let win := key128Words k
  [win.w0, win.w1, win.w2, win.w3] ++ expandFrom128 40 4 win

/-- `Cipher` (Algorithm 1) with `Nr = 10`, over any round keys. It is lean-aes's round function, run
nine times between the first and last `AddRoundKey`. -/
def cipher128 (rk : Nat → State) (input : State) : State :=
  let s := addRoundKey input (rk 0)
  let s := cipherRounds rk 9 1 s
  addRoundKey (shiftRows (subBytes s)) (rk 10)

/-! ## Byte-string interfaces -/

/-- A 16-byte block as a state: byte `i` of the block is byte `i` of the state (column-major, as
FIPS-197 §3.4 lays the input out). -/
def stateOf (b : Bytes) : State := State.ofNat (beNat b)

/-- AES-128 encryption of one 16-byte block under a 16-byte key. -/
def aes128 (key block : Bytes) : Bytes :=
  let ks := keyExpansion128 key
  (cipher128 (roundKey ks) (stateOf block)).toList

/-- AES-256 encryption of one 16-byte block under a 32-byte key: lean-aes's `encrypt`. -/
def aes256 (key block : Bytes) : Bytes :=
  (AES.encrypt (Key.ofNat (beNat key)) (stateOf block)).toList

@[simp] theorem State.toList_length (s : State) : s.toList.length = 16 := rfl

@[simp] theorem aes128_length (key block : Bytes) : (aes128 key block).length = 16 := rfl
@[simp] theorem aes256_length (key block : Bytes) : (aes256 key block).length = 16 := rfl

end Restic
