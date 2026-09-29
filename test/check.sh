#!/bin/sh
# Compare lean-restic with restic on the repositories test/make-repo.sh made.
set -eu
cd "$(dirname "$0")"
B=../.lake/build/bin/lean-restic
export RESTIC_PASSWORD=lean-restic-test
fail=0
same() { if [ "$2" = "$3" ]; then echo "ok   $1"; else echo "FAIL $1"; fail=1; fi; }
norm() { python3 -c "import json,sys; print(json.dumps(json.load(sys.stdin), sort_keys=True))"; }
for v in 1 2; do
  r=repo-v$v; mk=$r/masterkey.json
  same "v$v config" "$($B -r $r --masterkey $mk cat config | norm)" "$(restic -q -r $r cat config | norm)"
  same "v$v ids" "$($B -r $r ids | tail -1 | cut -d' ' -f1,3)" "$(find $r/keys $r/snapshots $r/index $r/data -type f | wc -l | tr -d ' ') $(find $r/keys $r/snapshots $r/index $r/data -type f | wc -l | tr -d ' ')"
  if $B -r $r --masterkey repo-v$((3 - v))/masterkey.json cat config >/dev/null 2>&1; then echo "FAIL v$v wrong key accepted"; fail=1; else echo "ok   v$v wrong key refused"; fi
done
for kind in snapshot index; do
  dir=snapshots; [ $kind = index ] && dir=index
  for f in repo-v1/$dir/*; do
    id=$(basename "$f")
    same "v1 $kind ${id%${id#????????}}" "$($B -r repo-v1 --masterkey repo-v1/masterkey.json cat $kind $id | norm)" "$(restic -q -r repo-v1 cat $kind $id | norm)"
  done
done
exit $fail
