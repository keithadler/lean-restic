import Restic.Json

/-! `jsoncheck FILE`: parse with `Restic.Json.parse` and print it back compactly; for `test/json_diff.py`. -/

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: jsoncheck FILE"; return 2
  match Restic.Json.parse (← IO.FS.readFile path) with
  | .ok j => IO.println j.render; return 0
  | .error e => IO.eprintln s!"jsoncheck: {e}"; return 1
