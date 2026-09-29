# lean-restic

An independent reader for [restic](https://restic.net) backups, with restic's encryption and pack format
specified and proved in Lean 4.

`restic check` asks restic whether restic's own output is right. `lean-restic` is a second opinion: a
separate program, written from restic's [design document](https://github.com/restic/restic/blob/master/doc/design.rst)
and the published standards, that opens your repository with your password, checks every pack, and
restores files, where the core of what it trusts is a Lean theorem rather than a test.

From `test/`, on a repository restic made:

```
$ lean-restic -r repo-v2 check
4 of 4 packs read (12338350 bytes): 226 blobs authenticated, 226 of them hashed to their IDs

$ lean-restic -r repo-v2 restore e4691693 --target /tmp/restored
restored 209 files and 8 directories, 12615851 bytes from 214 blobs, each checked against its ID
not restored (1): /src/link (symlink)
```

## What is proved

| Theorem | What it says |
|---|---|
| `openBlob_ok_iff` | Opening an encrypted object returns plaintext **only** for bytes that are exactly what restic's `Seal` writes under your key: `IV ‖ AES-256-CTR ciphertext ‖ Poly1305-AES tag`. No truncated, reordered or re-tagged input yields plaintext. |
| `openBlob_sealBlob` | What restic seals, `lean-restic` opens, byte for byte. |
| `ctr_eq_xor_keystream`, `ctr_ctr` | Counter mode is SP 800-38A's definition and undoes itself. |
| `parseHeader_encodeHeader`, `encodeHeader_of_parseHeader` | A pack header has exactly one reading: the parser and the encoder are inverse, and no byte is ignored. |
| `readPack_ok` | When a pack reads, it is exactly the sealed blobs laid end to end, then the sealed header listing them, then its length, and every uncompressed blob hashes to its ID. |
| `aes256_eq_fast`, `crypt_eq_fast`, `poly1305_eq_fast`, `compress_eq_fast`, `leNat_eq_fast` | The faster forms the program actually runs (AES with round keys once and table lookups, counter mode without byte lists, Poly1305 a chunk at a time, SHA-256 with array lookups, little-endian decoding four bytes at a time) are the specification, swapped in with `@[csimp]`. |
| `leNat_toLE`, `toLE_leNat`, `beNat_toBE` | Byte-order encodings are inverse. |

Known answers are theorems too, proved by the kernel evaluating the definitions: FIPS-197 (AES-128
key schedule and cipher; AES-256 comes from [lean-aes](https://github.com/keithadler/lean-aes)),
SP 800-38A F.5.5 (CTR-AES256), FIPS 180-2 (SHA-256), RFC 8439 (Poly1305), HMAC-SHA256 (the widely published
pangram example), RFC 7914 §11 (PBKDF2), restic's own Poly1305-AES vectors, and an object restic sealed in its test suite.

Everything is core Lean, no Mathlib. The theorems rest only on Lean's standard axioms (`propext`,
`Quot.sound`, `Classical.choice`; never `native_decide`), which `test/Axioms.lean` prints, and
[Tenet](https://github.com/keithadler/tenet), an independent Lean kernel, re-checks all 643
declarations: 643 verified, none rejected.

## What is tested, not proved

These have no simpler specification to be proved equal to, so they are written from their standards,
total by construction (no `partial`, bounded loops: bad input is an error, never a hang), and tested
differentially:

* **zstd** (RFC 8878), for repository format 2: `test/zstd.py` decodes 170 frames from the reference
  `zstd` tool exactly (levels `--fast=5` to `--ultra -22`, long mode, with and without checksums) and
  2,400 corrupted frames with no crash, hang or disagreement.
* **JSON**, for snapshots, indexes and trees: `test/json_diff.py` agrees with Python on 400 documents
  and refuses 253 malformed ones.
* **scrypt** (RFC 7914), to turn the password into a key: RFC 7914 §12 vectors, compiled
  (`test/vectors`), and every real restic key file in the tests.
* **Invalid zstd frames**: `test/zstd-invalid/` holds three frames the reference decoder rejects (a
  reserved header bit, a block over the maximum size, leftover sequence bits); each must be refused.
* **The whole program against restic**: `test/check.sh` makes format 1 and 2 repositories with restic
  (a 12 MB multi-chunk file, Unicode names, 200 small files, an incremental snapshot) and compares
  config, snapshots, indexes, `check`, password unlocking and every restore with restic's.
  `test/tamper.py` flips bytes throughout real packs: every change is refused.

## What you still trust

* That Poly1305-AES cannot be forged without the key. This is a cryptographic assumption, not a theorem;
  `openBlob_ok_iff` is stated so that this is the only way around it.
* Lean's compiler and runtime, and the operating system's file I/O.
* The tested parts above, and the thin I/O layer in `Restic/Repo.lean` and `Main.lean`.

## Use

```
lake build
.lake/build/bin/lean-restic -r REPO [KEY] snapshots
.lake/build/bin/lean-restic -r REPO [KEY] check
.lake/build/bin/lean-restic -r REPO [KEY] ls SNAPSHOT
.lake/build/bin/lean-restic -r REPO [KEY] restore SNAPSHOT --target DIR
.lake/build/bin/lean-restic -r REPO [KEY] cat config|snapshot|index ID
.lake/build/bin/lean-restic -r REPO ids
```

`KEY` is `--password-file FILE`, or `--masterkey FILE` with the output of `restic cat masterkey`;
without either, the password is read from `RESTIC_PASSWORD`, as restic reads it.

## Limits

* **Local repositories only.** For S3, B2, Wasabi or SFTP, point it at a local copy or an
  `rclone mount`.
* **Slow.** `check` runs at under 1 MB/s (15 seconds for the 12 MB test repository): the proved code
  works on lists. The program already runs faster forms of AES, counter mode, Poly1305, SHA-256 and
  byte decoding, each proved equal to its specification and swapped in with `@[csimp]`, but checking a
  large repository still means hours. Proved-equal byte-array code is the next step. Unlocking takes a
  few seconds (scrypt).
* **Restore writes file contents and directories.** Not yet permissions, times, ownership, symlinks or
  special files; `restore` lists what it skipped.
* Repository formats 1 and 2, tested with restic 0.19.1. No dictionaries in zstd frames (restic writes none).

## Layout

```
Restic/Bytes.lean     byte strings, byte order
Restic/AES.lean       AES-128 key schedule and byte-level AES (block cipher from lean-aes)
Restic/FastAES.lean   T-table AES-256, proved equal to the spec
Restic/CTR.lean       counter mode
Restic/Poly1305.lean  Poly1305
Restic/Seal.lean      restic's object format: sealBlob, openBlob, the main theorems
Restic/SHA256.lean    SHA-256
Restic/Pack.lean      pack headers and readPack
Restic/Vectors.lean   known answers, kernel-checked
Restic/Base64.lean    Base64
Restic/Scrypt.lean    HMAC-SHA256, PBKDF2, scrypt
Restic/XXH64.lean     XXH64, for zstd checksums
Restic/Zstd.lean      zstd decompression
Restic/Json.lean      JSON
Restic/Repo.lean      files, index, blobs, trees, key files
Main.lean             the command line
test/                 make-repo.sh, check.sh, tamper.py, zstd.py, zstd-invalid/, json_diff.py, vectors, Axioms.lean
.github/workflows/    CI: every test above on Linux, against restic 0.19.1
```

## License

MIT
