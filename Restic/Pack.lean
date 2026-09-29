import Restic.Seal
import Restic.SHA256

/-!
# Pack files

design.rst, "Pack Format". A pack is

    EncryptedBlob₁ ‖ … ‖ EncryptedBlobₙ ‖ EncryptedHeader ‖ Header_Length

where `Header_Length` is the length of `EncryptedHeader` as four little-endian bytes, and the header,
once opened, is a list of entries, one per blob, in order:

| type | meaning              | data                                                      |
|------|----------------------|-----------------------------------------------------------|
| 0    | data blob            | `Length(encrypted) ‖ Hash(plaintext)`                     |
| 1    | tree blob            | `Length(encrypted) ‖ Hash(plaintext)`                     |
| 2    | compressed data blob | `Length(encrypted) ‖ Length(plaintext) ‖ Hash(plaintext)` |
| 3    | compressed tree blob | `Length(encrypted) ‖ Length(plaintext) ‖ Hash(plaintext)` |

Lengths are four little-endian bytes, hashes 32 bytes of SHA-256. Blob offsets are not stored; each
blob starts where the previous one ends.

Proved here:

* `parseHeader_encodeHeader` and `encodeHeader_of_parseHeader`: the header parser and the encoder are
  inverse. Every byte string the parser accepts is the encoding of what it returns, so a header has one
  reading and no bytes are ignored.
* `readPack_ok`: when `readPack` succeeds, the pack is exactly the sealed blobs laid end to end, then the
  sealed header, then its length; and every uncompressed blob's plaintext hashes to the ID the header
  gives it.
-/

namespace Restic

set_option linter.unusedSimpArgs false

/-- Data or tree. -/
inductive BlobKind where
  | data
  | tree
  deriving DecidableEq, Repr

/-- One header entry. `rawLength` is present exactly for compressed blobs (types 2 and 3). -/
structure Entry where
  /-- Data or tree. -/
  kind : BlobKind
  /-- Length of the encrypted blob in the pack. -/
  length : Nat
  /-- Length of the plaintext after decompression, for compressed blobs. -/
  rawLength : Option Nat
  /-- SHA-256 of the (uncompressed) plaintext. -/
  id : Bytes
  deriving DecidableEq, Repr

/-- An entry the format can express: lengths fit in four bytes and the ID is 32 bytes. -/
def Entry.WF (e : Entry) : Prop :=
  e.length < 2 ^ 32 ∧ (∀ r, e.rawLength = some r → r < 2 ^ 32) ∧ e.id.length = 32

/-- The type byte. -/
def Entry.typeByte (e : Entry) : UInt8 :=
  match e.kind, e.rawLength with
  | .data, none => 0
  | .tree, none => 1
  | .data, some _ => 2
  | .tree, some _ => 3

/-- One entry's bytes. -/
def Entry.encode (e : Entry) : Bytes :=
  match e.rawLength with
  | none => e.typeByte :: (toLE 4 e.length ++ e.id)
  | some r => e.typeByte :: (toLE 4 e.length ++ toLE 4 r ++ e.id)

/-- A header's bytes. -/
def encodeHeader (es : List Entry) : Bytes := es.flatMap Entry.encode

/-- Parse header entries; `fuel` bounds their number. -/
def parseEntries : Nat → Bytes → Option (List Entry)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, t :: rest =>
    let kind := if t = 0 ∨ t = 2 then BlobKind.data else BlobKind.tree
    if t = 0 ∨ t = 1 then
      if rest.length < 36 then none
      else
        (⟨kind, leNat (rest.take 4), none, (rest.drop 4).take 32⟩ :: ·) <$> parseEntries fuel (rest.drop 36)
    else if t = 2 ∨ t = 3 then
      if rest.length < 40 then none
      else
        (⟨kind, leNat (rest.take 4), some (leNat ((rest.drop 4).take 4)), (rest.drop 8).take 32⟩ :: ·) <$>
          parseEntries fuel (rest.drop 40)
    else none

/-- Parse a decrypted pack header. Every entry is at least 37 bytes, so the length is enough fuel. -/
def parseHeader (h : Bytes) : Option (List Entry) := parseEntries h.length h

/-! ## The header encoding is canonical -/

theorem Entry.encode_length_pos (e : Entry) : 0 < e.encode.length := by
  unfold Entry.encode; split <;> simp

theorem parseEntries_encode (fuel : Nat) (es : List Entry) (hwf : ∀ e ∈ es, e.WF) (hf : es.length ≤ fuel) :
    parseEntries fuel (encodeHeader es) = some es := by
  induction es generalizing fuel with
  | nil => simp [encodeHeader, parseEntries]
  | cons e es ih =>
    obtain ⟨hl, hr, hid⟩ := hwf e (by simp)
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have ih' := ih fuel (fun x hx => hwf x (by simp [hx])) (by simp at hf; omega)
      obtain ⟨kind, len, raw, id⟩ := e
      simp only at hl hr hid
      cases raw with
      | none =>
        have h4 : (toLE 4 len).length = 4 := toLE_length 4 len
        simp only [encodeHeader, List.flatMap_cons, Entry.encode, Entry.typeByte, List.cons_append] at ih' ⊢
        cases kind <;>
        · simp only [parseEntries, or_false, false_or, ↓reduceIte, List.length_append, h4, hid,
            List.append_assoc]
          simp [List.take_left' h4, List.drop_left' h4, List.take_left' hid, List.drop_left' hid,
            leNat_toLE, Nat.mod_eq_of_lt hl, ih']
          refine ⟨by omega, ?_⟩
          rw [← List.append_assoc, List.drop_left' (by simp [h4, hid]), ih']
      | some r =>
        have hr' := hr r rfl
        have h4 : (toLE 4 len).length = 4 := toLE_length 4 len
        have h4' : (toLE 4 r).length = 4 := toLE_length 4 r
        simp only [encodeHeader, List.flatMap_cons, Entry.encode, Entry.typeByte, List.cons_append] at ih' ⊢
        cases kind <;>
        · simp only [parseEntries, reduceCtorEq, or_false, false_or, ↓reduceIte, List.length_append, h4, h4',
            hid, List.append_assoc]
          simp [List.take_left' h4, List.drop_left' h4, List.take_left' h4', List.drop_left' h4',
            List.take_left' hid, List.drop_left' hid, leNat_toLE, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr', ih']
          refine ⟨by omega, ?_, ?_⟩
          · rw [← List.append_assoc, ← List.append_assoc, List.drop_left' (by simp [h4, h4', hid]), ih']
          · rw [← List.append_assoc, List.drop_left' (by simp [h4, h4']), List.take_left' hid]

/-- Parsing an encoded header gives back its entries. -/
theorem parseHeader_encodeHeader (es : List Entry) (hwf : ∀ e ∈ es, e.WF) :
    parseHeader (encodeHeader es) = some es := by
  apply parseEntries_encode _ _ hwf
  unfold encodeHeader
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := e.encode_length_pos
    have := ih (fun x hx => hwf x (by simp [hx]))
    omega

theorem toLE_leNat_take (r : Bytes) (h : 4 ≤ r.length) : toLE 4 (leNat (r.take 4)) = r.take 4 := by
  have h1 := toLE_leNat (r.take 4)
  rw [show (r.take 4).length = 4 by simp; omega] at h1
  exact h1

theorem leNat_take4_lt (r : Bytes) : leNat (r.take 4) < 2 ^ 32 := by
  have := leNat_lt (r.take 4)
  have hl : (r.take 4).length ≤ 4 := by simp; omega
  have : 256 ^ (r.take 4).length ≤ 256 ^ 4 := Nat.pow_le_pow_right (by decide) hl
  omega

theorem split36 (r : Bytes) : r.take 4 ++ ((r.drop 4).take 32 ++ r.drop 36) = r := by
  conv => rhs; rw [← List.take_append_drop 4 r, ← List.take_append_drop 32 (r.drop 4)]
  simp [List.drop_drop]

theorem split40 (r : Bytes) :
    r.take 4 ++ ((r.drop 4).take 4 ++ ((r.drop 8).take 32 ++ r.drop 40)) = r := by
  conv => rhs; rw [← List.take_append_drop 4 r, ← List.take_append_drop 4 (r.drop 4),
    ← List.take_append_drop 32 ((r.drop 4).drop 4)]
  simp [List.drop_drop]

theorem encode_of_parseEntries (fuel : Nat) (h : Bytes) (es : List Entry) (hp : parseEntries fuel h = some es) :
    encodeHeader es = h ∧ ∀ e ∈ es, e.WF := by
  induction fuel generalizing h es with
  | zero =>
    cases h with
    | nil => simp [parseEntries] at hp; subst hp; simp [encodeHeader]
    | cons _ _ => simp [parseEntries] at hp
  | succ fuel ih =>
    cases h with
    | nil => simp [parseEntries] at hp; subst hp; simp [encodeHeader]
    | cons t rest =>
      simp only [parseEntries] at hp
      split at hp
      · rename_i ht
        split at hp
        · cases hp
        · rename_i hlen
          obtain ⟨es', hes', rfl⟩ := Option.map_eq_some_iff.1 hp
          obtain ⟨henc, hwf⟩ := ih _ _ hes'
          have hk := toLE_leNat_take rest (by omega)
          refine ⟨?_, ?_⟩
          · simp only [encodeHeader, List.flatMap_cons, Entry.encode] at henc ⊢
            rw [henc, hk]
            rcases ht with rfl | rfl <;> simp [Entry.typeByte, split36]
          · intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · exact ⟨leNat_take4_lt rest, by simp, by simp; omega⟩
            · exact hwf e he
      · split at hp
        · rename_i ht0 ht
          split at hp
          · cases hp
          · rename_i hlen
            obtain ⟨es', hes', rfl⟩ := Option.map_eq_some_iff.1 hp
            obtain ⟨henc, hwf⟩ := ih _ _ hes'
            have hk := toLE_leNat_take rest (by omega)
            have hk' := toLE_leNat_take (rest.drop 4) (by simp; omega)
            refine ⟨?_, ?_⟩
            · simp only [encodeHeader, List.flatMap_cons, Entry.encode] at henc ⊢
              rw [henc, hk, hk']
              rcases ht with rfl | rfl <;> simp [Entry.typeByte, List.drop_drop, split40]
            · intro e he
              simp only [List.mem_cons] at he
              rcases he with rfl | he
              · refine ⟨leNat_take4_lt rest, ?_, by simp; omega⟩
                intro r hr
                simp only [Option.some.injEq] at hr
                subst hr
                exact leNat_take4_lt _
              · exact hwf e he
        · cases hp

/-- Whatever the parser accepts is the encoding of what it returns, and every entry is well formed. -/
theorem encodeHeader_of_parseHeader {h : Bytes} {es : List Entry} (hp : parseHeader h = some es) :
    encodeHeader es = h ∧ ∀ e ∈ es, e.WF :=
  encode_of_parseEntries _ _ _ hp

/-! ## Reading a pack -/

/-- `R` holds between corresponding elements of two lists of the same length. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- Split a pack into the blob region and the encrypted header, using the last four bytes. -/
def splitPack (f : Bytes) : Option (Bytes × Bytes) :=
  if f.length < 4 then none
  else
    let n := f.length - 4
    let hl := leNat (f.drop n)
    if n < hl then none
    else
      let body := f.take n
      some (body.take (n - hl), body.drop (n - hl))

/-- Cut the blob region into one piece per entry, of the entry's length, using all of it. -/
def cutBlobs : List Entry → Bytes → Option (List Bytes)
  | [], [] => some []
  | [], _ :: _ => none
  | e :: es, r =>
    if r.length < e.length then none
    else (r.take e.length :: ·) <$> cutBlobs es (r.drop e.length)

/-- Why a pack could not be read. -/
inductive PackError where
  /-- The last four bytes give a header longer than the file. -/
  | badHeaderLength
  /-- The header did not open. -/
  | header (e : OpenError)
  /-- The opened header is not a list of entries. -/
  | badHeader
  /-- The entries' lengths do not add up to the blob region. -/
  | lengthMismatch
  /-- Blob `i` did not open. -/
  | blob (i : Nat) (e : OpenError)
  /-- Blob `i` opened, but its plaintext does not hash to the ID in the header. -/
  | idMismatch (i : Nat)
  deriving DecidableEq, Repr

/-- Open each blob and check each uncompressed blob's ID. (A compressed blob's ID is the hash of its
decompressed plaintext, which needs zstd; it is only authenticated here.) -/
def readBlobs (k : MasterKey) : Nat → List Entry → List Bytes → Except PackError (List (Entry × Bytes))
  | _, [], [] => .ok []
  | i, e :: es, p :: ps =>
    match openBlob k p with
    | .error err => .error (.blob i err)
    | .ok pt =>
      if e.rawLength = none ∧ sha256 pt ≠ e.id then .error (.idMismatch i)
      else ((e, pt) :: ·) <$> readBlobs k (i + 1) es ps
  | _, _, _ => .error .lengthMismatch

/-- Read a whole pack: every blob with its header entry and its plaintext. -/
def readPack (k : MasterKey) (f : Bytes) : Except PackError (List (Entry × Bytes)) :=
  match splitPack f with
  | none => .error .badHeaderLength
  | some (region, hdr) =>
    match openBlob k hdr with
    | .error e => .error (.header e)
    | .ok h =>
      match parseHeader h with
      | none => .error .badHeader
      | some es =>
        match cutBlobs es region with
        | none => .error .lengthMismatch
        | some pieces => readBlobs k 0 es pieces

/-! ## What a successful read means -/

theorem splitPack_some {f region hdr : Bytes} (h : splitPack f = some (region, hdr)) :
    f = region ++ hdr ++ toLE 4 hdr.length := by
  unfold splitPack at h
  split at h
  · cases h
  · rename_i h4
    simp only at h
    split at h
    · cases h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd : (f.drop (f.length - 4)).length = 4 := by simp; omega
      have hlen : ((f.take (f.length - 4)).drop (f.length - 4 - leNat (f.drop (f.length - 4)))).length =
          leNat (f.drop (f.length - 4)) := by simp; omega
      rw [hlen, List.take_append_drop]
      have := toLE_leNat (f.drop (f.length - 4))
      rw [hd] at this
      rw [this, List.take_append_drop]

theorem cutBlobs_some {es : List Entry} {r : Bytes} {pieces : List Bytes} (h : cutBlobs es r = some pieces) :
    r = pieces.flatten ∧ Forall2 (fun e p => p.length = e.length) es pieces := by
  induction es generalizing r pieces with
  | nil =>
    cases r with
    | nil => simp [cutBlobs] at h; subst h; exact ⟨rfl, .nil⟩
    | cons _ _ => simp [cutBlobs] at h
  | cons e es ih =>
    simp only [cutBlobs] at h
    split at h
    · cases h
    · rename_i hlt
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hr, hf⟩ := ih hps
      refine ⟨?_, .cons (by simp; omega) hf⟩
      simp [← hr]

theorem readBlobs_ok {k : MasterKey} (hk : k.valid) {i : Nat} {es : List Entry} {ps : List Bytes}
    {xs : List (Entry × Bytes)} (h : readBlobs k i es ps = .ok xs) :
    xs.map Prod.fst = es ∧
    Forall2 (fun x p => ∃ iv, validIV iv ∧ p = sealBlob k iv x.2) xs ps ∧
    ∀ x ∈ xs, x.1.rawLength = none → sha256 x.2 = x.1.id := by
  induction es generalizing i ps xs with
  | nil =>
    cases ps with
    | nil => simp [readBlobs] at h; subst h; exact ⟨rfl, .nil, by simp⟩
    | cons _ _ => simp [readBlobs] at h
  | cons e es ih =>
    cases ps with
    | nil => simp [readBlobs] at h
    | cons p ps =>
      simp only [readBlobs] at h
      split at h
      · cases h
      · rename_i pt hopen
        split at h
        · cases h
        · rename_i hid
          cases hr : readBlobs k (i + 1) es ps with
          | error err => rw [hr] at h; cases h
          | ok ys =>
            rw [hr] at h
            simp only [Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            obtain ⟨h1, h2, h3⟩ := ih hr
            refine ⟨by simp [h1], Forall2.cons ((openBlob_ok_iff hk p pt).1 hopen) h2, ?_⟩
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · intro hn
              exact Decidable.byContradiction fun hne => hid ⟨hn, hne⟩
            · exact h3 x hx

/-- **A successful read accounts for every byte of the pack.** The pack is the blobs, each sealed under
the master key, laid end to end; then the header listing exactly those entries, sealed; then the
header's length. Every uncompressed blob's plaintext hashes to its ID. -/
theorem readPack_ok {k : MasterKey} (hk : k.valid) {f : Bytes} {xs : List (Entry × Bytes)}
    (h : readPack k f = .ok xs) :
    (∃ (pieces : List Bytes) (hiv : Bytes), validIV hiv ∧
      Forall2 (fun x p => ∃ iv, validIV iv ∧ p = sealBlob k iv x.2) xs pieces ∧
      f = pieces.flatten ++ sealBlob k hiv (encodeHeader (xs.map Prod.fst)) ++
        toLE 4 (sealBlob k hiv (encodeHeader (xs.map Prod.fst))).length) ∧
    ∀ x ∈ xs, x.1.rawLength = none → sha256 x.2 = x.1.id := by
  unfold readPack at h
  split at h
  · cases h
  · rename_i region hdr hsplit
    split at h
    · cases h
    · rename_i hh hopen
      split at h
      · cases h
      · rename_i es hparse
        split at h
        · cases h
        · rename_i pieces hcut
          obtain ⟨h1, h2, h3⟩ := readBlobs_ok hk h
          obtain ⟨hiv, hivv, rfl⟩ := (openBlob_ok_iff hk hdr hh).1 hopen
          obtain ⟨henc, -⟩ := encodeHeader_of_parseHeader hparse
          obtain ⟨hr, -⟩ := cutBlobs_some hcut
          refine ⟨⟨pieces, hiv, hivv, h2, ?_⟩, h3⟩
          rw [h1, henc, ← hr]
          exact splitPack_some hsplit

end Restic
