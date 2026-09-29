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
for v in 1 2; do
  r=repo-v$v
  for kind in snapshot index; do
    dir=snapshots; [ $kind = index ] && dir=index
    for f in $r/$dir/*; do
      id=$(basename "$f")
      same "v$v $kind ${id%${id#????????}}" "$($B -r $r --masterkey $r/masterkey.json cat $kind $id | norm)" "$(restic -q -r $r cat $kind $id | norm)"
    done
  done
  out=$($B -r $r --masterkey $r/masterkey.json check | tail -1)
  n=$(echo "$out" | sed -E 's/.*: ([0-9]+) blobs authenticated, ([0-9]+) of them.*/\1 \2/')
  set -- $n
  if [ "$1" = "$2" ] && [ "$1" -gt 0 ]; then echo "ok   v$v check: $out"; else echo "FAIL v$v check: $out"; fail=1; fi
done
# Restore every snapshot with both programs and compare the trees. lean-restic restores contents and
# directories, not symlinks, so symlinks are left out of the comparison.
tmp=$(mktemp -d)
for v in 1 2; do
  r=repo-v$v
  for f in $r/snapshots/*; do
    id=$(basename "$f"); short=$(printf %.8s "$id")
    $B -r $r --masterkey $r/masterkey.json restore $id --target $tmp/lean-$v-$short >/dev/null
    restic -q -r $r restore $id --target $tmp/restic-$v-$short >/dev/null
    find $tmp/restic-$v-$short -type l -delete
    if diff -r $tmp/lean-$v-$short $tmp/restic-$v-$short >/dev/null; then echo "ok   v$v restore $short = restic restore"
    else echo "FAIL v$v restore $short differs from restic restore"; fail=1; fi
  done
done
rm -rf "$tmp"
exit $fail
