#!/bin/sh
# Make small restic repositories to test against, with real restic.
#   test/repo-v1   repository format 1 (no compression)
#   test/repo-v2   repository format 2 (restic's default: zstd)
# Each gets one snapshot of test/src and its master key in masterkey.json.
# The password is a throwaway, used for nothing else.
set -eu
cd "$(dirname "$0")"
export RESTIC_PASSWORD=lean-restic-test
rm -rf src repo-v1 repo-v2
mkdir -p src/sub
printf 'Dies ist ein Test!\n' > src/hello.txt
printf '' > src/empty
head -c 300000 /dev/urandom > src/sub/random.bin
python3 -c "print('restic ' * 20000)" > src/sub/repeats.txt
for v in 1 2; do
  restic -q init --repository-version $v -r repo-v$v
  restic -q -r repo-v$v backup --host lean-restic --tag test src
  restic -q -r repo-v$v cat masterkey > repo-v$v/masterkey.json
done
echo "made repo-v1 and repo-v2"
