import Restic.XXH64

/-!
# Zstandard decompression

RFC 8878. Restic's repository format 2 compresses the JSON of snapshots, indexes and trees, and may
compress blobs, with zstd.

A decompressor has no simpler specification to be proved equal to: the format *is* the decoding
procedure. So this file is written directly from the RFC, section by section, and what is guaranteed
is weaker than elsewhere in this library:

* every function is total: there is no `partial`, every loop runs over a bounded range, and malformed
  input is an `.error`, never a crash or a hang;
* `test/zstd.py` compares it with the reference `zstd` tool on thousands of frames, and `test/check.sh`
  with restic on real repositories.

Names follow the RFC: frames (§3.1.1), blocks (§3.1.1.2), literals (§3.1.1.3.1), sequences
(§3.1.1.3.2), sequence execution (§3.1.1.4), repeat offsets (§3.1.1.5), FSE (§4.1) and Huffman (§4.2)
coding.
-/

namespace Restic.Zstd

/-- Decoding either succeeds or says why not. -/
abbrev M := Except String

/-- Byte `i`, or an error past the end. -/
def byteAt (d : ByteArray) (i : Nat) : M Nat :=
  if h : i < d.size then pure d[i].toNat else throw "truncated input"

/-- `n` bytes little-endian from `i`. -/
def readLE (d : ByteArray) (i n : Nat) : M Nat := do
  let mut v := 0
  for k in [0:n] do
    v := v + (← byteAt d (i + k)) <<< (8 * k)
  return v

/-! ## Bitstreams

FSE and Huffman streams are read backward (§4.1, §4.2.2): the last byte's highest set bit marks the
start, and bits are consumed from there toward the first byte, most significant first. Bits before the
first byte read as zero, which the RFC allows at the very end of a stream. Table descriptions are read
forward, least significant bit first. -/

/-- A backward bitstream over `data[start, start + len)`: `pos` bits remain unread. -/
structure BackBits where
  data : ByteArray
  start : Nat
  pos : Int

def BackBits.init (d : ByteArray) (start len : Nat) : M BackBits := do
  if len = 0 then throw "empty bitstream"
  if start + len > d.size then throw "bitstream runs past the end"
  let last ← byteAt d (start + len - 1)
  if last = 0 then throw "bitstream's last byte is zero"
  return ⟨d, start, ((8 * (len - 1) + Nat.log2 last : Nat) : Int)⟩

/-- Bit `j` of the stream, zero before its start. -/
def BackBits.bit (b : BackBits) (j : Int) : Nat :=
  if j < 0 then 0 else ((b.data.get! (b.start + j.toNat / 8)).toNat >>> (j.toNat % 8)) % 2

/-- The next `n` bits as a number, and the stream after them. -/
def BackBits.read (b : BackBits) (n : Nat) : Nat × BackBits := Id.run do
  let mut v := 0
  for k in [0:n] do
    v := 2 * v + b.bit (b.pos - 1 - k)
  return (v, { b with pos := b.pos - n })

/-- The next `n` bits without consuming them. -/
def BackBits.peek (b : BackBits) (n : Nat) : Nat := (b.read n).1

/-- Bit `j` counted forward from byte `start`, least significant first; zero past the end. -/
def fwdBit (d : ByteArray) (start j : Nat) : Nat :=
  ((d.get! (start + j / 8)).toNat >>> (j % 8)) % 2

def fwdBits (d : ByteArray) (start j n : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:n] do
    v := v + fwdBit d start (j + k) <<< k
  return v

/-! ## FSE, §4.1 -/

/-- One decoding-table cell: the symbol, and how to reach the next state. -/
structure FseCell where
  sym : Nat
  nbBits : Nat
  base : Nat
  deriving Inhabited

/-- A decoding table with accuracy log `al`: `2^al` cells. -/
structure Fse where
  al : Nat
  cells : Array FseCell
  deriving Inhabited

/-- Build the decoding table from normalized counts, §4.1.1. A count of `-1` means "less than one":
the symbol gets one cell at the top of the table. -/
def buildFse (al : Nat) (counts : Array Int) : M Fse := do
  let size := 1 <<< al
  let mut total := 0
  for c in counts do
    total := total + (if c = -1 then 1 else c.toNat)
  if total ≠ size then throw "FSE: counts do not add up to the table size"
  let mut syms : Array Nat := Array.replicate size 0
  let mut high := size
  for s in [0:counts.size] do
    if counts[s]! = -1 then
      high := high - 1
      syms := syms.set! high s
  let step := (size >>> 1) + (size >>> 3) + 3
  let mask := size - 1
  let mut pos := 0
  for s in [0:counts.size] do
    let c := counts[s]!
    if c > 0 then
      for _ in [0:c.toNat] do
        syms := syms.set! pos s
        pos := (pos + step) &&& mask
        for _ in [0:size] do
          if pos ≥ high then pos := (pos + step) &&& mask else break
  if pos ≠ 0 then throw "FSE: symbols do not spread over the table"
  let mut next : Array Nat := counts.map fun c => if c = -1 then 1 else c.toNat
  let mut cells := Array.mkEmpty size
  for i in [0:size] do
    let s := syms[i]!
    let n := next[s]!
    next := next.set! s (n + 1)
    let nb := al - Nat.log2 n
    cells := cells.push ⟨s, nb, (n <<< nb) - size⟩
  return ⟨al, cells⟩

/-- A one-symbol table (RLE mode): state 0 always gives `s` and reads no bits. -/
def rleFse (s : Nat) : Fse := ⟨0, #[⟨s, 0, 0⟩]⟩

/-- Read an FSE table description, §4.1.1, from `d` at `start`. Returns the accuracy log, the counts,
and the number of bytes the description took. -/
def readNCount (d : ByteArray) (start maxSym maxAL : Nat) : M (Nat × Array Int × Nat) := do
  let _ ← byteAt d start
  let al := fwdBits d start 0 4 + 5
  if al > maxAL then throw "FSE: accuracy log too large"
  let size := 1 <<< al
  let mut bitpos := 4
  let mut remaining := size + 1
  let mut threshold := size
  let mut nbBits := al + 1
  let mut counts : Array Int := #[]
  for _ in [0:maxSym + 2] do
    if remaining ≤ 1 ∨ counts.size > maxSym then break
    let maxv := 2 * threshold - 1 - remaining
    let low := fwdBits d start bitpos (nbBits - 1)
    let mut count := 0
    if low < maxv then
      count := low
      bitpos := bitpos + (nbBits - 1)
    else
      let v := fwdBits d start bitpos nbBits
      count := if v ≥ threshold then v - maxv else v
      bitpos := bitpos + nbBits
    let c : Int := (count : Int) - 1
    if c.natAbs > remaining then throw "FSE: count larger than what remains"
    remaining := remaining - c.natAbs
    counts := counts.push c
    if c = 0 then
      for _ in [0:maxSym + 1] do
        let r := fwdBits d start bitpos 2
        bitpos := bitpos + 2
        for _ in [0:r] do counts := counts.push 0
        if r ≠ 3 then break
    for _ in [0:nbBits] do
      if remaining < threshold then
        nbBits := nbBits - 1
        threshold := threshold >>> 1
  if remaining ≠ 1 then throw "FSE: table description does not add up"
  if counts.size > maxSym + 1 then throw "FSE: too many symbols"
  let bytes := (bitpos + 7) / 8
  let _ ← byteAt d (start + bytes - 1)
  return (al, counts, bytes)

/-! ## Huffman, §4.2 -/

/-- A Huffman decoding table: `2^maxBits` cells, each a symbol and its code length. -/
structure Huff where
  maxBits : Nat
  syms : Array UInt8
  lens : Array Nat
  deriving Inhabited

/-- Build the table from the weights of symbols `0 … n-1`; the last symbol's weight is implied,
§4.2.1.3. Weight-1 symbols get the lowest codes, then weight 2, and so on, each in symbol order. -/
def buildHuff (weights : Array Nat) : M Huff := do
  let mut total := 0
  for w in weights do
    if w > 12 then throw "Huffman: weight too large"
    if w > 0 then total := total + (1 <<< (w - 1))
  if total = 0 then throw "Huffman: all weights zero"
  let maxBits := Nat.log2 total + 1
  if maxBits > 11 then throw "Huffman: code too long"
  let rest := (1 <<< maxBits) - total
  if rest &&& (rest - 1) ≠ 0 then throw "Huffman: weights do not complete a tree"
  let ws := weights.push (Nat.log2 rest + 1)
  if ws.size > 256 then throw "Huffman: too many symbols"
  let size := 1 <<< maxBits
  let mut syms := Array.mkEmpty size
  let mut lens := Array.mkEmpty size
  for w in [1:maxBits + 1] do
    for s in [0:ws.size] do
      if ws[s]! = w then
        for _ in [0:1 <<< (w - 1)] do
          syms := syms.push s.toUInt8
          lens := lens.push (maxBits + 1 - w)
  if syms.size ≠ size then throw "Huffman: table size mismatch"
  return ⟨maxBits, syms, lens⟩

/-- Decode the Huffman weights compressed with FSE (header byte `< 128`), §4.2.1.2: two states
alternate over one backward stream until it runs out. -/
def fseWeights (d : ByteArray) (start len : Nat) : M (Array Nat) := do
  let (al, counts, used) ← readNCount d start 255 6
  if used ≥ len then throw "Huffman: weight stream missing"
  let fse ← buildFse al counts
  let mut bits ← BackBits.init d (start + used) (len - used)
  let (s1, b1) := bits.read al
  let (s2, b2) := b1.read al
  bits := b2
  let mut st1 := s1
  let mut st2 := s2
  let mut out : Array Nat := #[]
  for _ in [0:256] do
    let c1 := fse.cells[st1]!
    out := out.push c1.sym
    let (v1, b) := bits.read c1.nbBits
    bits := b
    st1 := c1.base + v1
    if bits.pos < 0 then
      out := out.push fse.cells[st2]!.sym
      break
    let c2 := fse.cells[st2]!
    out := out.push c2.sym
    let (v2, b') := bits.read c2.nbBits
    bits := b'
    st2 := c2.base + v2
    if bits.pos < 0 then
      out := out.push fse.cells[st1]!.sym
      break
  if out.size > 255 then throw "Huffman: too many weights"
  return out

/-- Read a Huffman tree description at `start`: the table and the bytes it took, §4.2.1. -/
def readHuffTree (d : ByteArray) (start : Nat) : M (Huff × Nat) := do
  let h ← byteAt d start
  if h < 128 then
    let ws ← fseWeights d (start + 1) h
    return (← buildHuff ws, 1 + h)
  else
    let n := h - 127
    let nbytes := (n + 1) / 2
    let mut ws : Array Nat := #[]
    for i in [0:n] do
      let b ← byteAt d (start + 1 + i / 2)
      ws := ws.push (if i % 2 = 0 then b >>> 4 else b &&& 15)
    return (← buildHuff ws, 1 + nbytes)

/-- Decode `count` symbols from one Huffman stream. The stream must be used up exactly. -/
def huffStream (hf : Huff) (d : ByteArray) (start len count : Nat) (out : ByteArray) : M ByteArray := do
  let mut bits ← BackBits.init d start len
  let mut out := out
  for _ in [0:count] do
    let i := bits.peek hf.maxBits
    out := out.push hf.syms[i]!
    bits := (bits.read hf.lens[i]!).2
  if bits.pos ≠ 0 then throw "Huffman: stream not used up exactly"
  return out

/-! ## Literals section, §3.1.1.3.1 -/

/-- Decode the literals section at `start`: the literals, the bytes the section took, and the Huffman
table to keep for a later treeless section. -/
def readLiterals (d : ByteArray) (start : Nat) (prevHuff : Option Huff) :
    M (ByteArray × Nat × Option Huff) := do
  let b0 ← byteAt d start
  let ty := b0 &&& 3
  let sf := (b0 >>> 2) &&& 3
  if ty ≤ 1 then
    -- Raw or RLE
    let (hsize, regen) ←
      if sf % 2 = 0 then pure (1, b0 >>> 3)
      else if sf = 1 then pure (2, (← readLE d start 2) >>> 4)
      else pure (3, (← readLE d start 3) >>> 4)
    if ty = 0 then
      if start + hsize + regen > d.size then throw "literals: raw literals run past the end"
      return (d.extract (start + hsize) (start + hsize + regen), hsize + regen, prevHuff)
    else
      let b ← byteAt d (start + hsize)
      return (ByteArray.mk (Array.replicate regen b.toUInt8), hsize + 1, prevHuff)
  else
    -- Compressed (2) or Treeless (3)
    let (hsize, sizeBits, streams) :=
      match sf with
      | 0 => (3, 10, 1)
      | 1 => (3, 10, 4)
      | 2 => (4, 14, 4)
      | _ => (5, 18, 4)
    let hv := (← readLE d start hsize) >>> 4
    let regen := hv &&& ((1 <<< sizeBits) - 1)
    let csize := hv >>> sizeBits
    if regen > 131072 then throw "literals: more than a block"
    let body := start + hsize
    if body + csize > d.size then throw "literals: compressed literals run past the end"
    let (hf, treeBytes) ←
      if ty = 2 then do
        let (hf, n) ← readHuffTree d body
        pure (hf, n)
      else
        match prevHuff with
        | some hf => pure (hf, 0)
        | none => throw "literals: treeless without a previous Huffman table"
    if treeBytes > csize then throw "literals: tree larger than the section"
    let sStart := body + treeBytes
    let sLen := csize - treeBytes
    let mut out := ByteArray.emptyWithCapacity regen
    if streams = 1 then
      out ← huffStream hf d sStart sLen regen out
    else
      if sLen < 6 then throw "literals: no room for the jump table"
      let l1 ← readLE d sStart 2
      let l2 ← readLE d (sStart + 2) 2
      let l3 ← readLE d (sStart + 4) 2
      if 6 + l1 + l2 + l3 > sLen then throw "literals: jump table past the section"
      let l4 := sLen - 6 - l1 - l2 - l3
      let per := (regen + 3) / 4
      if 3 * per > regen then throw "literals: too few for four streams"
      let s1 := sStart + 6
      out ← huffStream hf d s1 l1 per out
      out ← huffStream hf d (s1 + l1) l2 per out
      out ← huffStream hf d (s1 + l1 + l2) l3 per out
      out ← huffStream hf d (s1 + l1 + l2 + l3) l4 (regen - 3 * per) out
    return (out, hsize + csize, some hf)

/-! ## Sequences section, §3.1.1.3.2 -/

/-- Literal-length codes: baseline and extra bits, Table 17. -/
def llBase : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32,
  40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]
def llBits : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8,
  9, 10, 11, 12, 13, 14, 15, 16]

/-- Match-length codes, Table 18. -/
def mlBase : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051,
  4099, 8195, 16387, 32771, 65539]
def mlBits : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

/-- Predefined distributions, §3.1.1.3.2.2. -/
def llDefault : Array Int := #[4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2,
  1, 1, 1, 1, 1, -1, -1, -1, -1]
def mlDefault : Array Int := #[1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1]
def ofDefault : Array Int := #[1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1,
  -1, -1, -1]

/-- What carries from one block to the next within a frame. -/
structure Carry where
  huff : Option Huff := none
  ll : Option Fse := none
  of : Option Fse := none
  ml : Option Fse := none
  reps : Nat × Nat × Nat := (1, 4, 8)

/-- Choose one symbol's decoding table from its mode, §3.1.1.3.2.1: predefined, RLE, described here,
or repeated from the previous block. Returns the table and the bytes the description took. -/
def readTable (d : ByteArray) (pos mode : Nat) (dflt : Array Int) (defaultAL maxSym maxAL : Nat)
    (prev : Option Fse) : M (Fse × Nat) := do
  match mode with
  | 0 => return (← buildFse defaultAL dflt, 0)
  | 1 =>
    let s ← byteAt d pos
    if s > maxSym then throw "sequences: RLE symbol out of range"
    return (rleFse s, 1)
  | 2 =>
    let (al, counts, n) ← readNCount d pos maxSym maxAL
    return (← buildFse al counts, n)
  | _ =>
    match prev with
    | some t => return (t, 0)
    | none => throw "sequences: repeat mode without a previous table"

/-- A decoded sequence: literals to copy, then a match of `ml` bytes at distance `off`. -/
structure Seq where
  ll : Nat
  ml : Nat
  off : Nat

/-- Decode the sequences section at `start`, which ends at `stop`. -/
def readSequences (d : ByteArray) (start stop : Nat) (carry : Carry) : M (Array Seq × Carry) := do
  let b0 ← byteAt d start
  let (nb, hlen) ←
    if b0 = 0 then pure (0, 1)
    else if b0 < 128 then pure (b0, 1)
    else if b0 < 255 then pure (((b0 - 128) <<< 8) + (← byteAt d (start + 1)), 2)
    else pure ((← readLE d (start + 1) 2) + 0x7F00, 3)
  if nb = 0 then
    if start + hlen ≠ stop then throw "sequences: bytes after an empty section"
    return (#[], carry)
  let modes ← byteAt d (start + hlen)
  if modes &&& 3 ≠ 0 then throw "sequences: reserved bits set"
  let mut pos := start + hlen + 1
  let (llT, n1) ← readTable d pos (modes >>> 6) llDefault 6 35 9 carry.ll
  pos := pos + n1
  let (ofT, n2) ← readTable d pos ((modes >>> 4) &&& 3) ofDefault 5 31 8 carry.of
  pos := pos + n2
  let (mlT, n3) ← readTable d pos ((modes >>> 2) &&& 3) mlDefault 6 52 9 carry.ml
  pos := pos + n3
  if pos ≥ stop then throw "sequences: no bitstream"
  let mut bits ← BackBits.init d pos (stop - pos)
  let (s1, b1) := bits.read llT.al
  let (s2, b2) := b1.read ofT.al
  let (s3, b3) := b2.read mlT.al
  bits := b3
  let mut llS := s1
  let mut ofS := s2
  let mut mlS := s3
  let (r1, r2, r3) := carry.reps
  let mut rep1 := r1
  let mut rep2 := r2
  let mut rep3 := r3
  let mut seqs : Array Seq := Array.mkEmpty nb
  for i in [0:nb] do
    let llC := llT.cells[llS]!
    let ofC := ofT.cells[ofS]!
    let mlC := mlT.cells[mlS]!
    let ofCode := ofC.sym
    if ofCode > 31 then throw "sequences: offset code too large"
    let (ofExtra, b) := bits.read ofCode
    bits := b
    let ofVal := (1 <<< ofCode) + ofExtra
    let (mlExtra, b) := bits.read (mlBits.getD mlC.sym 0)
    bits := b
    let ml := mlBase.getD mlC.sym 0 + mlExtra
    let (llExtra, b) := bits.read (llBits.getD llC.sym 0)
    bits := b
    let ll := llBase.getD llC.sym 0 + llExtra
    -- Repeat offsets, §3.1.1.5
    let mut off := 0
    if ofVal > 3 then
      off := ofVal - 3
      rep3 := rep2; rep2 := rep1; rep1 := off
    else
      let idx := if ll = 0 then ofVal + 1 else ofVal
      if idx = 1 then off := rep1
      else if idx = 2 then
        off := rep2
        rep2 := rep1; rep1 := off
      else if idx = 3 then
        off := rep3
        rep3 := rep2; rep2 := rep1; rep1 := off
      else
        if rep1 ≤ 1 then throw "sequences: repeat offset would be zero"
        off := rep1 - 1
        rep3 := rep2; rep2 := rep1; rep1 := off
    seqs := seqs.push ⟨ll, ml, off⟩
    if i + 1 < nb then
      let (v, b) := bits.read llC.nbBits
      bits := b
      llS := llC.base + v
      let (v, b) := bits.read mlC.nbBits
      bits := b
      mlS := mlC.base + v
      let (v, b) := bits.read ofC.nbBits
      bits := b
      ofS := ofC.base + v
  if bits.pos ≠ 0 then throw "sequences: bitstream not used up exactly"
  return (seqs, { carry with ll := some llT, of := some ofT, ml := some mlT, reps := (rep1, rep2, rep3) })

/-! ## Blocks and frames, §3.1.1 -/

/-- Execute sequences, §3.1.1.4: literals, then a copy from `off` bytes back in the output. -/
def execute (out : ByteArray) (lits : ByteArray) (seqs : Array Seq) (windowStart : Nat) : M ByteArray := do
  let mut out := out
  let mut lp := 0
  for s in seqs do
    if lp + s.ll > lits.size then throw "execute: not enough literals"
    out := out.append (lits.extract lp (lp + s.ll))
    lp := lp + s.ll
    if s.off = 0 ∨ s.off > out.size - windowStart then throw "execute: offset before the start of the frame"
    let from0 := out.size - s.off
    for k in [0:s.ml] do
      out := out.push (out.get! (from0 + k))
  out := out.append (lits.extract lp lits.size)
  return out

/-- Decode one compressed block `d[start, start + size)` onto `out`. -/
def compressedBlock (d : ByteArray) (start size : Nat) (out : ByteArray) (windowStart : Nat)
    (carry : Carry) : M (ByteArray × Carry) := do
  let (lits, n, huff) ← readLiterals d start carry.huff
  if n > size then throw "block: literals larger than the block"
  let (seqs, carry') ← readSequences d (start + n) (start + size) { carry with huff := huff }
  let out ← execute out lits seqs windowStart
  return (out, carry')

/-- Decode one frame at `start`, appending to `out`. Returns the output and where the frame ends. -/
def frame (d : ByteArray) (start : Nat) (out : ByteArray) : M (ByteArray × Nat) := do
  if (← readLE d start 4) ≠ 0xFD2FB528 then throw "not a zstd frame"
  let fhd ← byteAt d (start + 4)
  let fcsFlag := fhd >>> 6
  let single := (fhd >>> 5) &&& 1 = 1
  if (fhd >>> 3) &&& 1 = 1 then throw "frame: reserved bit set"
  let checksum := (fhd >>> 2) &&& 1 = 1
  let didFlag := fhd &&& 3
  let mut pos := start + 5
  let wd ← if single then pure 0 else byteAt d pos
  if !single then pos := pos + 1
  let didBytes := match didFlag with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 4
  let did ← readLE d pos didBytes
  if did ≠ 0 then throw "frame: dictionaries are not supported"
  pos := pos + didBytes
  let fcsBytes := match fcsFlag with | 0 => (if single then 1 else 0) | 1 => 2 | 2 => 4 | _ => 8
  let fcsRaw ← readLE d pos fcsBytes
  let fcs : Option Nat := if fcsBytes = 0 then none else some (if fcsBytes = 2 then fcsRaw + 256 else fcsRaw)
  pos := pos + fcsBytes
  -- Window_Size, §3.1.1.1.2; a block never decompresses to more than min(Window_Size, 128 KiB).
  let windowSize :=
    if single then fcs.getD 0
    else
      let base := 1 <<< (10 + (wd >>> 3))
      base + (base / 8) * (wd &&& 7)
  let blockMax := min windowSize 131072
  let windowStart := out.size
  let mut out := out
  let mut carry : Carry := {}
  let mut last := false
  for _ in [0:d.size] do
    if last then break
    let bh ← readLE d pos 3
    pos := pos + 3
    last := bh &&& 1 = 1
    let bt := (bh >>> 1) &&& 3
    let bsize := bh >>> 3
    if bsize > 131072 then throw "block: larger than 128 KiB"
    if bt ≤ 1 ∧ bsize > blockMax then throw "block: larger than the maximum block size"
    let before := out.size
    if bt = 0 then
      if pos + bsize > d.size then throw "block: raw block runs past the end"
      out := out.append (d.extract pos (pos + bsize))
      pos := pos + bsize
    else if bt = 1 then
      let b ← byteAt d pos
      out := out.append (ByteArray.mk (Array.replicate bsize b.toUInt8))
      pos := pos + 1
    else if bt = 2 then
      if pos + bsize > d.size then throw "block: compressed block runs past the end"
      let (o, c) ← compressedBlock d pos bsize out windowStart carry
      if o.size - before > blockMax then throw "block: decompresses to more than the maximum block size"
      out := o
      carry := c
      pos := pos + bsize
    else throw "block: reserved block type"
  if !last then throw "frame: no last block"
  if let some n := fcs then
    if out.size - windowStart ≠ n then throw "frame: content size does not match"
  if checksum then
    let want ← readLE d pos 4
    let got := (XXH64.hash out windowStart (out.size - windowStart)).toNat % 2 ^ 32
    if want ≠ got then throw "frame: checksum mismatch"
    pos := pos + 4
  return (out, pos)

/-- Decompress `d`, which must be exactly one zstd frame. -/
def decompress (d : ByteArray) : M ByteArray := do
  let (out, stop) ← frame d 0 ByteArray.empty
  if stop ≠ d.size then throw "bytes after the frame"
  return out

end Restic.Zstd
