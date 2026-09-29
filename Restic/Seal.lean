import Restic.CTR
import Restic.FastAES
import Restic.Poly1305

/-!
# Sealing and opening, restic's encryption format

Every encrypted object in a restic repository is `IV ‖ CIPHERTEXT ‖ MAC` (design.rst, "Repository
Format"; `internal/repository/crypto/crypto.go`, `Seal` and `Open`):

* the ciphertext is the plaintext under AES-256 in counter mode, with the 16-byte IV as the first
  counter block;
* the MAC is Poly1305-AES over the ciphertext only (encrypt-then-MAC): Poly1305 keyed with
  `r ‖ AES-128_k(IV)`, where the master key's MAC part is `k ‖ r`.

`openBlob` mirrors restic's `Open`: it refuses an all-zero key part, an all-zero IV and input shorter
than 32 bytes, and it releases plaintext only after the MAC matches.

The two theorems at the end are the point of this file. `openBlob_sealBlob`: what `sealBlob` writes, `openBlob`
reads back exactly. `openBlob_ok_iff`: `openBlob` accepts a byte string **only** if it is literally the
output of `sealBlob` under this key for some valid IV and the plaintext returned. There is no input that
yields plaintext by any other route, truncated, reordered or with a wrong tag. Whether someone without
the key can *produce* such a string is the security of Poly1305-AES, which is a cryptographic
assumption and is not proved here.
-/

namespace Restic

/-- A repository master key: 32 bytes of AES-256 key, and the MAC key `k ‖ r`. -/
structure MasterKey where
  /-- The AES-256 key for counter mode. -/
  encrypt : Bytes
  /-- `k`: the AES-128 key that turns the IV into Poly1305's `s`. -/
  macK : Bytes
  /-- `r`: Poly1305's multiplier, clamped before use. -/
  macR : Bytes
  deriving Repr, DecidableEq

/-- Not all zero, as restic's `Valid` methods require of each key part and `validNonce` of the IV. -/
def nonzero (bs : Bytes) : Bool := bs.any (· != 0)

/-- The key has the right lengths and no part is all zero (restic's `Key.Valid`). -/
def MasterKey.valid (k : MasterKey) : Bool :=
  k.encrypt.length == 32 && k.macK.length == 16 && k.macR.length == 16 &&
    nonzero k.encrypt && nonzero k.macK && nonzero k.macR

/-- An IV restic accepts: 16 bytes, not all zero. -/
def validIV (iv : Bytes) : Bool := iv.length == 16 && nonzero iv

/-- Poly1305-AES over the ciphertext (restic's `poly1305MAC`). -/
def mac (k : MasterKey) (iv ct : Bytes) : Bytes := poly1305 (k.macR ++ aes128 k.macK iv) ct

/-- AES-256-CTR under the master key's encryption key. -/
def crypt (k : MasterKey) (iv m : Bytes) : Bytes := ctr (aes256 k.encrypt) iv m

/-- `2¹²⁸`, computed once. -/
def two128 : Nat := 2 ^ 128

/-- `crypt` as it runs: the round keys are expanded once per object and each counter block goes
straight from a number to an AES state, skipping the byte lists in between. -/
def cryptFast (k : MasterKey) (iv m : Bytes) : Bytes :=
  let rks := expandKey256 k.encrypt
  let base := beNat iv
  ctrGoK (fun j => (cipherT rks (AES.State.ofNat ((base + j) % two128))).toList) 0 [] m

/-- Compiled code runs `cryptFast` for `crypt`; they are the same function. -/
@[csimp] theorem crypt_eq_fast : @crypt = @cryptFast := by
  funext k iv m
  simp only [crypt, cryptFast, ctr, ctrGo_eq_ctrGoK, aes256_eq_fast, aes256Fast, aes256Keyed, stateOf,
    ctrBlock, beNat_toBE, two128]
  rw [show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]
  simp only [Nat.mod_mod]

/-- What restic writes for plaintext `m` with IV `iv`: `IV ‖ CIPHERTEXT ‖ MAC`. -/
def sealBlob (k : MasterKey) (iv m : Bytes) : Bytes :=
  let ct := crypt k iv m
  iv ++ ct ++ mac k iv ct

/-- Why `openBlob` refused. -/
inductive OpenError where
  /-- A key part is the wrong length or all zero. -/
  | invalidKey
  /-- Fewer than 32 bytes: no room for an IV and a MAC. -/
  | tooShort
  /-- The IV is all zero. -/
  | invalidIV
  /-- The MAC does not match: wrong key, or the data was changed. -/
  | unauthenticated
  deriving Repr, DecidableEq

deriving instance DecidableEq for Except

/-- Read `IV ‖ CIPHERTEXT ‖ MAC`: check the MAC, then decrypt (restic's `Open`). -/
def openBlob (k : MasterKey) (c : Bytes) : Except OpenError Bytes :=
  if !k.valid then .error .invalidKey
  else if c.length < 32 then .error .tooShort
  else
    let iv := c.take 16
    let body := c.drop 16
    let ct := body.take (body.length - 16)
    let tag := body.drop (body.length - 16)
    if !validIV iv then .error .invalidIV
    else if mac k iv ct != tag then .error .unauthenticated
    else .ok (crypt k iv ct)

@[simp] theorem sealBlob_length (k : MasterKey) (iv m : Bytes) :
    (sealBlob k iv m).length = iv.length + m.length + 16 := by
  simp [sealBlob, mac, crypt]; omega

theorem crypt_crypt (k : MasterKey) (iv m : Bytes) : crypt k iv (crypt k iv m) = m := ctr_ctr _ _ _

/-- What `sealBlob` writes, `openBlob` reads back. -/
theorem openBlob_sealBlob {k : MasterKey} {iv : Bytes} (hk : k.valid) (hiv : validIV iv) (m : Bytes) :
    openBlob k (sealBlob k iv m) = .ok m := by
  have hlen : iv.length = 16 := by simp [validIV] at hiv; exact hiv.1
  have hct : (crypt k iv m).length = m.length := by simp [crypt]
  have hn : ¬ (sealBlob k iv m).length < 32 := by rw [sealBlob_length, hlen]; omega
  simp only [openBlob, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hn]
  simp only [sealBlob, List.append_assoc]
  simp only [List.take_left' hlen, List.drop_left' hlen, List.length_append, hct, mac, poly1305_length,
    Nat.add_sub_cancel, List.take_left' hct, List.drop_left' hct, hiv, Bool.not_true]
  simp [crypt_crypt]

/-- `openBlob` accepts exactly the outputs of `sealBlob`: it returns plaintext `m` for `c` if and only if `c`
is `sealBlob k iv m` for some valid IV. -/
theorem openBlob_ok_iff {k : MasterKey} (hk : k.valid) (c m : Bytes) :
    openBlob k c = .ok m ↔ ∃ iv, validIV iv ∧ c = sealBlob k iv m := by
  constructor
  · intro h
    simp only [openBlob, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hc : c.length < 32
    · simp only [hc, ↓reduceIte, reduceCtorEq] at h
    simp only [hc, ↓reduceIte] at h
    by_cases hv : validIV (c.take 16) = true
    · by_cases hm : mac k (c.take 16) ((c.drop 16).take ((c.drop 16).length - 16)) =
          (c.drop 16).drop ((c.drop 16).length - 16)
      · simp only [hv, hm, Bool.not_true, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          Except.ok.injEq] at h
        subst h
        refine ⟨c.take 16, hv, ?_⟩
        simp only [sealBlob, crypt_crypt, hm, List.append_assoc, List.take_append_drop]
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq, hm,
          not_false_eq_true, reduceCtorEq] at h
    · simp only [hv, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  · rintro ⟨iv, hiv, rfl⟩
    exact openBlob_sealBlob hk hiv m

/-- The plaintext `openBlob` returns is 32 bytes shorter than its input. -/
theorem openBlob_ok_length {k : MasterKey} (hk : k.valid) {c m : Bytes} (h : openBlob k c = .ok m) :
    m.length + 32 = c.length := by
  obtain ⟨iv, hiv, rfl⟩ := (openBlob_ok_iff hk c m).1 h
  have : iv.length = 16 := by simp [validIV] at hiv; exact hiv.1
  simp [this]; omega

/-- There is one accepted encoding of a plaintext per IV: two strings that start with the same IV and
openBlob to the same plaintext are the same string. -/
theorem openBlob_ok_unique {k : MasterKey} (hk : k.valid) {c c' m : Bytes}
    (h : openBlob k c = .ok m) (h' : openBlob k c' = .ok m) (hiv : c.take 16 = c'.take 16) : c = c' := by
  obtain ⟨iv, hv, rfl⟩ := (openBlob_ok_iff hk c m).1 h
  obtain ⟨iv', hv', rfl⟩ := (openBlob_ok_iff hk c' m).1 h'
  have h1 : iv.length = 16 := by simp [validIV] at hv; exact hv.1
  have h2 : iv'.length = 16 := by simp [validIV] at hv'; exact hv'.1
  simp only [sealBlob, List.append_assoc, List.take_left' h1, List.take_left' h2] at hiv
  subst hiv; rfl

end Restic
