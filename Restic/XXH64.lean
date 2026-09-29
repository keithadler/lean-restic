/-!
# XXH64

The 64-bit xxHash (github.com/Cyan4973/xxHash, `doc/xxhash_spec.md`), which a zstd frame uses for its
optional content checksum: the low 32 bits of XXH64 of the decompressed content, seed 0. Restic writes
frames without it; the reference `zstd` tool writes it by default, so the tests exercise it.
-/

namespace Restic.XXH64

def P1 : UInt64 := 11400714785074694791
def P2 : UInt64 := 14029467366897019727
def P3 : UInt64 := 1609587929392839161
def P4 : UInt64 := 9650029242287828579
def P5 : UInt64 := 2870177450012600261

def rotl (x : UInt64) (r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64 - r))

def round (acc input : UInt64) : UInt64 := rotl (acc + input * P2) 31 * P1

def mergeRound (acc v : UInt64) : UInt64 := (acc ^^^ round 0 v) * P1 + P4

def read64 (d : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for k in [0:8] do
    v := v ||| ((d.get! (i + k)).toUInt64 <<< (8 * k).toUInt64)
  return v

def read32 (d : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for k in [0:4] do
    v := v ||| ((d.get! (i + k)).toUInt64 <<< (8 * k).toUInt64)
  return v

/-- XXH64 of `d[start, start + len)` with seed 0. -/
def hash (d : ByteArray) (start len : Nat) : UInt64 := Id.run do
  let mut p := start
  let stop := start + len
  let mut h : UInt64 := 0
  if len ≥ 32 then
    let mut v1 : UInt64 := P1 + P2
    let mut v2 : UInt64 := P2
    let mut v3 : UInt64 := 0
    let mut v4 : UInt64 := 0 - P1
    for _ in [0:len / 32] do
      v1 := round v1 (read64 d p)
      v2 := round v2 (read64 d (p + 8))
      v3 := round v3 (read64 d (p + 16))
      v4 := round v4 (read64 d (p + 24))
      p := p + 32
    h := rotl v1 1 + rotl v2 7 + rotl v3 12 + rotl v4 18
    h := mergeRound h v1
    h := mergeRound h v2
    h := mergeRound h v3
    h := mergeRound h v4
  else
    h := P5
  h := h + len.toUInt64
  for _ in [0:(stop - p) / 8] do
    h := h ^^^ round 0 (read64 d p)
    h := rotl h 27 * P1 + P4
    p := p + 8
  if stop - p ≥ 4 then
    h := h ^^^ (read32 d p * P1)
    h := rotl h 23 * P2 + P3
    p := p + 4
  for _ in [0:stop - p] do
    h := h ^^^ ((d.get! p).toUInt64 * P5)
    h := rotl h 11 * P1
    p := p + 1
  h := h ^^^ (h >>> 33)
  h := h * P2
  h := h ^^^ (h >>> 29)
  h := h * P3
  h := h ^^^ (h >>> 32)
  return h

end Restic.XXH64
