import Restic
open Restic

def timeIt (label : String) (bytes : Nat) (act : Unit → IO Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← act ()
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  IO.println s!"{label}: {ms} ms for {bytes} bytes ({if ms = 0 then 0 else bytes * 1000 / ms / 1024} KiB/s) [{r}]"

def main : IO Unit := do
  let n := 1 <<< 18
  let m : Bytes := (List.range n).map (·.toUInt8)
  let key := bytes 32 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4
  let iv := bytes 16 0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
  timeIt "aes256 x1024 blocks" (1024*16) fun _ => do
    let mut acc := 0
    for i in [0:1024] do acc := acc + ((aes256 key (ctrBlock iv i)).headD 0).toNat
    return acc
  let rks := expandKey256 key
  timeIt "aes256Keyed x1024 blocks" (1024*16) fun _ => do
    let mut acc := 0
    for i in [0:1024] do acc := acc + ((aes256Keyed rks (ctrBlock iv i)).headD 0).toNat
    return acc
  timeIt "roundT x14336" (1024*16) fun _ => do
    let mut s : AES.State := stateOf (ctrBlock iv 0)
    for _ in [0:14336] do s := roundT s (rks.getD 1 0)
    return s.c0.b0.toNat
  timeIt "State.ofNat x1024" (1024*16) fun _ => do
    let mut acc := 0
    for i in [0:1024] do acc := acc + (AES.State.ofNat (0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff + i)).c0.b0.toNat
    return acc
  timeIt "cipherT x1024" (1024*16) fun _ => do
    let mut acc := 0
    let s0 := AES.State.ofNat 0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
    for i in [0:1024] do acc := acc + (cipherT rks (if i = 7777 then 0 else s0)).c0.b0.toNat
    return acc
  timeIt "expandKey256 x100" (1600) fun _ => do
    let mut acc := 0
    for i in [0:100] do acc := acc + ((expandKey256 (if i = 7777 then [] else key)).getD 3 0).c0.b0.toNat
    return acc
  timeIt "ctrBlock x1024" (1024*16) fun _ => do
    let mut acc := 0
    for i in [0:1024] do acc := acc + ((ctrBlock iv i).headD 0).toNat
    return acc
  timeIt "ctr" n fun _ => return ((ctr (aes256 key) iv m).getLast?.getD 0).toNat
  timeIt "poly1305" n fun _ => return ((poly1305 (key) m).headD 0).toNat
  timeIt "sha256" n fun _ => return ((sha256 m).headD 0).toNat
