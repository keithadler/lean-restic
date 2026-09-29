import Restic

/-! The axioms the main theorems rest on: only Lean's standard three (`propext`, `Classical.choice`,
`Quot.sound`), never `Lean.ofReduceBool` (no `native_decide`, no `bv_decide`). Run with
`lake env lean test/Axioms.lean`. -/

#print axioms Restic.openBlob_ok_iff
#print axioms Restic.openBlob_sealBlob
#print axioms Restic.readPack_ok
#print axioms Restic.parseHeader_encodeHeader
#print axioms Restic.encodeHeader_of_parseHeader
#print axioms Restic.ctr_eq_xor_keystream
#print axioms Restic.aes256_eq_fast
#print axioms Restic.crypt_eq_fast
#print axioms Restic.restic_TestCrypto
#print axioms Restic.sp800_38a_F55
#print axioms Restic.rfc7914_11
