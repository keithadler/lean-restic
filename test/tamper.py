#!/usr/bin/env python3
"""Flip single bytes in test/repo-v1's packs and check that lean-restic refuses every one.

readPack_ok says a pack that reads is exactly the sealed blobs, the sealed header and its length, so a
changed byte can only get through by forging a Poly1305-AES tag. This checks that the compiled program
behaves that way on real restic packs: the first and last bytes of every region, and random bytes.
"""
import os, random, shutil, subprocess, sys, tempfile

here = os.path.dirname(os.path.abspath(__file__))
exe = os.path.join(here, "..", ".lake", "build", "bin", "lean-restic")
repo = os.path.join(here, "repo-v1")
key = os.path.join(repo, "masterkey.json")
random.seed(1)

packs = [os.path.join(d, f) for d, _, fs in os.walk(os.path.join(repo, "data")) for f in fs]
fails = 0
tried = 0
with tempfile.TemporaryDirectory() as tmp:
    for pack in sorted(packs, key=os.path.getsize):
        size = os.path.getsize(pack)
        data = open(pack, "rb").read()
        hl = int.from_bytes(data[-4:], "little")
        hdr = size - 4 - hl
        spots = {0, 1, 15, 16, 17, hdr - 17, hdr - 1, hdr, hdr + 15, hdr + 16, size - 20, size - 17, size - 5,
                 size - 4, size - 1} | {random.randrange(size) for _ in range(8)}
        for pos in sorted(p for p in spots if 0 <= p < size):
            # A repository holding only the changed pack: `check` reads data/ and nothing else.
            copy = os.path.join(tmp, "repo")
            shutil.rmtree(copy, ignore_errors=True)
            target = os.path.join(copy, os.path.relpath(pack, repo))
            os.makedirs(os.path.dirname(target))
            b = bytearray(data)
            b[pos] ^= 0x01
            open(target, "wb").write(b)
            r = subprocess.run([exe, "-r", copy, "--masterkey", key, "check"], capture_output=True, text=True)
            tried += 1
            if r.returncode == 0:
                fails += 1
                print(f"NOT DETECTED: {os.path.basename(pack)[:8]} byte {pos} of {size}")
            else:
                why = [l for l in r.stdout.splitlines() if l.startswith("BAD")][0].split(": ", 1)[1]
                print(f"refused  {os.path.basename(pack)[:8]} byte {pos:>6} of {size}: {why}")
print(f"{tried - fails} of {tried} single-byte changes refused")
sys.exit(1 if fails else 0)
