import Restic
open Restic

def timeIt (label : String) (bytes : Nat) (act : Unit → IO Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← act ()
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  IO.println s!"{label}: {ms} ms for {bytes} bytes ({if ms = 0 then 0 else bytes * 1000 / ms / 1024} KiB/s) [{r}]"

def main : IO Unit := do
  let n := 1 <<< 20
  let m : Bytes := (List.range n).map (·.toUInt8)
  let k : MasterKey := ⟨bytes 32 0x303e8687b1d7db18421bdc6bb8588ccadac4d59ee87b8ff70c44e635790cafef,
    bytes 16 0xef4d8824cb80b2bcc5fbff8a9b12a42c, bytes 16 0xcc8d4b948ee0ebfe1d415de921d10353⟩
  let iv := bytes 16 0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
  let sealed := sealBlob k iv m
  let chunk : Bytes := m.take 16
  timeIt "leNat (take 16) x65536" n fun _ => do
    let mut acc := 0
    for i in [0:65536] do acc := acc + leNat ((if i = 99999 then m else chunk).take 16) % 7
    return acc
  timeIt "mulmod x65536" n fun _ => do
    let mut acc := 12345678901234567890123456789
    for _ in [0:65536] do acc := (acc + 340282366920938463463374607431768211456 + 77) * 1234567890123456789012345678901 % P1305
    return acc % 256
  timeIt "ByteArray→List 1 MiB" n fun _ => do
    let ba := ByteArray.mk (m.toArray)
    return (ba.toList.getLast?.getD 0).toNat
  timeIt "crypt (fast)" n fun _ => return ((crypt k iv m).getLast?.getD 0).toNat
  timeIt "mac (poly1305-aes)" n fun _ => return ((mac k iv m).headD 0).toNat
  timeIt "sha256" n fun _ => return ((sha256 m).headD 0).toNat
  timeIt "openBlob" n fun _ => return match openBlob k sealed with | .ok pt => pt.length | .error _ => 0
