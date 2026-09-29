#!/usr/bin/env python3
"""Differential test: Restic.Zstd.decompress against the reference zstd tool.

Compresses a variety of inputs with `zstd` at many levels and options, decompresses each frame with the
Lean decoder (the `unzstd` executable), and compares byte for byte. Then corrupts frames and checks the
decoder never crashes or hangs: it must either refuse or, if it accepts, zstd must accept too.
"""
import os, random, subprocess, sys, tempfile

here = os.path.dirname(os.path.abspath(__file__))
exe = os.environ.get("UNZSTD") or os.path.join(here, "..", ".lake", "build", "bin", "unzstd")
random.seed(int(os.environ.get("SEED", "7")))

def inputs():
    yield "empty", b""
    yield "one byte", b"x"
    yield "hello", b"Dies ist ein Test!\n"
    yield "zeros 1M", bytes(1 << 20)
    yield "random 200K", random.randbytes(200_000)
    words = [b"restic", b"lean", b"backup", b"snapshot", b"tree", b"blob", b"pack", b"index", b"{", b"}", b'"']
    yield "words 500K", b" ".join(random.choice(words) for _ in range(90_000))
    yield "json", (b'{"name":"file%05d","type":"file","mode":420,"size":%d,"content":["%064x"]},' * 1) * 0 + b"".join(
        b'{"name":"file%05d","type":"file","mode":420,"size":%d,"content":["%064x"]},' % (i, i * 37, random.getrandbits(256))
        for i in range(3000))
    src = os.path.join(here, "..", "Restic", "Zstd.lean")
    yield "source", open(src, "rb").read()
    yield "mixed", b"".join(random.choice([random.randbytes(300), b"A" * 700, b"abcabcabc" * 50]) for _ in range(800))
    for n in [3, 17, 100, 1000, 131071, 131072, 131073, 262145]:
        yield f"repeat-ish {n}", bytes((i * i) % 7 for i in range(n))

configs = [["-1"], ["-3"], ["-9"], ["-19"], ["--ultra", "-22"], ["--fast=5"], ["-3", "--no-check"],
           ["-6", "--no-check", "--no-content-size"], ["-12", "--long=24"], ["-5", "--format=zstd", "--content-size"]]

ok = bad = 0
with tempfile.TemporaryDirectory() as tmp:
    raw, comp = os.path.join(tmp, "raw"), os.path.join(tmp, "raw.zst")
    frames = []
    for name, data in inputs():
        open(raw, "wb").write(data)
        for cfg in configs:
            subprocess.run(["zstd", "-q", "-f", *cfg, raw, "-o", comp], check=True)
            r = subprocess.run([exe, comp], capture_output=True)
            if r.returncode == 0 and r.stdout == data:
                ok += 1
            else:
                bad += 1
                print(f"FAIL {name} {' '.join(cfg)}: {r.stderr.decode().strip() or 'output differs'}")
                if os.environ.get("KEEP"):
                    tag = f"fail-{bad}"
                    open(os.path.join(here, tag + ".raw"), "wb").write(data)
                    open(os.path.join(here, tag + ".zst"), "wb").write(open(comp, "rb").read())
            frames.append(open(comp, "rb").read())
    print(f"{ok} of {ok + bad} frames decoded exactly")
    # Corruption: flip bytes; the decoder must refuse or agree with zstd, and never crash.
    crashes = disagree = refused = 0
    for _ in range(int(os.environ.get("CORRUPT", "400"))):
        f = bytearray(random.choice([x for x in frames if len(x) > 8]))
        for _ in range(random.randint(1, 3)):
            f[random.randrange(len(f))] ^= 1 << random.randrange(8)
        open(comp, "wb").write(f)
        try:
            r = subprocess.run([exe, comp], capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            crashes += 1; print("HANG on a corrupted frame"); continue
        if r.returncode not in (0, 1):
            crashes += 1; print(f"CRASH (exit {r.returncode}): {r.stderr[:200]}")
        elif r.returncode == 1:
            refused += 1
        else:
            z = subprocess.run(["zstd", "-q", "-d", "-c", comp], capture_output=True)
            if z.returncode != 0 or z.stdout != r.stdout:
                disagree += 1
                keep = os.path.join(here, f"disagree-{disagree}.zst")
                open(keep, "wb").write(f)
                print(f"ACCEPTED a frame zstd {'rejects: ' + z.stderr.decode().strip() if z.returncode else 'decodes differently'} (saved {os.path.basename(keep)})")
    print(f"corrupted frames: {refused} refused, {crashes} crashes or hangs, {disagree} disagreements")
sys.exit(1 if bad or crashes else 0)
