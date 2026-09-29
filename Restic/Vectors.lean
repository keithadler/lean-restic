import Restic.Seal
import Restic.SHA256

/-!
# Known answers, as theorems

Each theorem here is proved by `decide +kernel`: Lean's kernel runs the definitions on the published
inputs and compares with the published outputs. Nothing is compiled, so an independent kernel such as
Tenet re-derives the same facts.

* FIPS-197 Appendix A.1 and C.1: the AES-128 key schedule and cipher added in `Restic.AES`.
* NIST SP 800-38A F.5.5: CTR-AES256, four blocks.
* FIPS 180-2 Appendix B.1 and B.2: SHA-256 of "abc" and of a two-block message, and of the empty string.
* RFC 8439 §2.5.2: Poly1305.
* Restic's own tests (`internal/repository/crypto/crypto_int_test.go`): the four Poly1305-AES vectors
  from Bernstein's paper, run through restic's `mac`, and a complete object restic sealed, which
  `openBlob` opens to the ASCII bytes of "Dies ist ein Test!".
-/

namespace Restic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## FIPS-197 AES-128 -/

/-- Appendix A.1: the second word and the last word of the key schedule for key
`2b7e1516 28aed2a6 abf71588 09cf4f3c`. -/
theorem fips197_A1 :
    (keyExpansion128 (bytes 16 0x2b7e151628aed2a6abf7158809cf4f3c)).getD 4 0 = .ofNat 0xa0fafe17 ∧
    (keyExpansion128 (bytes 16 0x2b7e151628aed2a6abf7158809cf4f3c)).getD 43 0 = .ofNat 0xb6630ca6 := by
  decide +kernel

theorem keyExpansion128_length (k : Bytes) : (keyExpansion128 k).length = 44 := rfl

/-- Appendix C.1: AES-128 encryption of one block. -/
theorem fips197_C1 :
    aes128 (bytes 16 0x000102030405060708090a0b0c0d0e0f) (bytes 16 0x00112233445566778899aabbccddeeff) =
      bytes 16 0x69c4e0d86a7b0430d8cdb78070b4c55a := by
  decide +kernel

/-! ## SP 800-38A F.5.5, CTR-AES256.Encrypt -/

theorem sp800_38a_F55 :
    ctr (aes256 (bytes 32 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4))
        (bytes 16 0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff)
        (bytes 64 0x6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710) =
      bytes 64 0x601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c52b0930daa23de94ce87017ba2d84988ddfc9c58db67aada613c2dd08457941a6 := by
  decide +kernel

/-! ## SHA-256 -/

theorem sha256_empty :
    sha256 [] = bytes 32 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 := by
  decide +kernel

/-- FIPS 180-2 B.1: "abc". -/
theorem fips180_B1 :
    sha256 (bytes 3 0x616263) = bytes 32 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad := by
  decide +kernel

/-- FIPS 180-2 B.2: "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 448 bits, two blocks
after padding. -/
theorem fips180_B2 :
    sha256 (bytes 56 0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071) =
      bytes 32 0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1 := by
  decide +kernel

/-! ## RFC 8439 §2.5.2, Poly1305 -/

/-- The key `85:d6:…:1b` and the 34-byte message "Cryptographic Forum Research Group". -/
theorem rfc8439_2_5_2 :
    poly1305 (bytes 32 0x85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b)
        (bytes 34 0x43727970746f6772617068696320466f72756d2052657365617263682047726f7570) =
      bytes 16 0xa8061dc1305136c6c22b8baf0c0127a9 := by
  decide +kernel

/-! ## Restic's Poly1305-AES vectors (Bernstein 2005, Appendix B) -/

/-- A master key with only the MAC part set, as restic's `TestPoly1305` builds one. -/
def macOnly (k r : Bytes) : MasterKey := ⟨[], k, r⟩

theorem poly1305aes_1 :
    mac (macOnly (bytes 16 0xec074c835580741701425b623235add6) (bytes 16 0x851fc40c3467ac0be05cc20404f3f700))
        (bytes 16 0xfb447350c4e868c52ac3275cf9d4327e) (bytes 2 0xf3f6) =
      bytes 16 0xf4c633c3044fc145f84f335cb81953de := by
  decide +kernel

theorem poly1305aes_2 :
    mac (macOnly (bytes 16 0x75deaa25c09f208e1dc4ce6b5cad3fbf) (bytes 16 0xa0f3080000f46400d0c7e9076c834403))
        (bytes 16 0x61ee09218d29b0aaed7e154a2c5509cc) [] =
      bytes 16 0xdd3fab2251f11ac759f0887129cc2ee7 := by
  decide +kernel

theorem poly1305aes_3 :
    mac (macOnly (bytes 16 0x6acb5f61a7176dd320c5c1eb2edcdc74) (bytes 16 0x48443d0bb0d21109c89a100b5ce2c208))
        (bytes 16 0xae212a55399729595dea458bc621ff0e)
        (bytes 32 0x663cea190ffb83d89593f3f476b6bc24d7e679107ea26adb8caf6652d0656136) =
      bytes 16 0x0ee1c16bb73f0f4fd19881753c01cdbe := by
  decide +kernel

theorem poly1305aes_4 :
    mac (macOnly (bytes 16 0xe1a5668a4d5b66a5f68cc5424ed5982d) (bytes 16 0x12976a08c4426d0ce8a82407c4f48207))
        (bytes 16 0x9ae831e743978d3a23527c7128149e3a)
        (bytes 63 0xab0812724a7f1e342742cbed374d94d136c6b8795d45b3819830f2c04491faf0990c62e48b8018b2c3e4a0fa3134cb67fa83e158c994d961c4cb21095c1bf9) =
      bytes 16 0x5154ad0d2cb26e01274fc51148491f1b := by
  decide +kernel

/-! ## An object restic sealed (`TestCrypto`) -/

/-- The master key of restic's `TestCrypto`. -/
def testKey : MasterKey :=
  ⟨bytes 32 0x303e8687b1d7db18421bdc6bb8588ccadac4d59ee87b8ff70c44e635790cafef,
   bytes 16 0xef4d8824cb80b2bcc5fbff8a9b12a42c,
   bytes 16 0xcc8d4b948ee0ebfe1d415de921d10353⟩

/-- The 50 bytes restic wrote: IV, 18 bytes of ciphertext, MAC. -/
def testObject : Bytes :=
  bytes 50 0x69fb41c62d12def4593bd71757138606338f621aeaeb39da0fe4f99233f8037a54ea63338a813bcf3f75d8c3cc75dddf8750

/-- `openBlob` opens it to "Dies ist ein Test!". -/
theorem restic_TestCrypto : openBlob testKey testObject = .ok (bytes 18 0x44696573206973742065696e205465737421) := by
  decide +kernel

/-- Flip one bit of the MAC and it is refused, as restic's test checks. -/
theorem restic_TestCrypto_tampered :
    openBlob testKey (testObject.modify 42 (· ^^^ 0x23)) = .error .unauthenticated := by
  decide +kernel

end Restic
