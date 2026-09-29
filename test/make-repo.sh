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
mkdir -p src/sub/deep/a/b/c src/many "src/with space"
printf 'deep\n' > src/sub/deep/a/b/c/file.txt
printf 'ünïcødé\n' > "src/ünïcødé 名前.txt"
printf 'spaced\n' > "src/with space/file name.txt"
head -c 12000000 /dev/urandom > src/big.bin
python3 -c "
import os
for i in range(200):
    open(f'src/many/f{i:03d}.txt', 'w').write(f'file {i}\n' * (i + 1))
"
ln -s hello.txt src/link
for v in 1 2; do
  restic -q init --repository-version $v -r repo-v$v
  restic -q -r repo-v$v backup --host lean-restic --tag test src
  restic -q -r repo-v$v cat masterkey > repo-v$v/masterkey.json
done
# A second, incremental snapshot: one file changed, one added.
printf 'changed\n' >> src/hello.txt
printf 'new\n' > src/new.txt
for v in 1 2; do
  restic -q -r repo-v$v backup --host lean-restic --tag second src
done
echo "made repo-v1 and repo-v2"
