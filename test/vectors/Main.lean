import Restic.Scrypt
import Restic.Repo

/-! `vectors`: known answers too large for kernel evaluation, run compiled. scrypt, RFC 7914 §12. -/

open Restic

def ascii (s : String) : Bytes := s.toUTF8.toList

def cases : List (String × Bytes × String) := [
  ("scrypt('', '', N=16, r=1, p=1)", scrypt [] [] 16 1 1 64,
   "77d6576238657b203b19ca42c18a0497f16b4844e3074ae8dfdffa3fede21442fcd0069ded0948f8326a753a0fc81f17e8d3e0fb2e0d3628cf35e20c38d18906"),
  ("scrypt('password', 'NaCl', N=1024, r=8, p=16)", scrypt (ascii "password") (ascii "NaCl") 1024 8 16 64,
   "fdbabe1c9d3472007856e7190d01e9fe7c6ad7cbc8237830e77376634b3731622eaf30d92e22a3886ff109279d9830dac727afb94a83ee6d8360cbdfa2cc0640")]

def main : IO UInt32 := do
  let mut bad := 0
  for (name, got, want) in cases do
    if Repo.hex got = want then IO.println s!"ok   {name}"
    else
      bad := bad + 1
      IO.println s!"FAIL {name}: {Repo.hex got}"
  return if bad = 0 then 0 else 1
