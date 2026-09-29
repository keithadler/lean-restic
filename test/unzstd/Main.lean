import Restic.Zstd

/-! `unzstd FILE`: decompress one zstd frame to stdout with `Restic.Zstd.decompress`; for `test/zstd.py`. -/

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: unzstd FILE"; return 2
  match Restic.Zstd.decompress (← IO.FS.readBinFile path) with
  | .ok out => (← IO.getStdout).write out; return 0
  | .error e => IO.eprintln s!"unzstd: {e}"; return 1
