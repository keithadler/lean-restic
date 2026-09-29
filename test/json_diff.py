#!/usr/bin/env python3
"""Differential test: Restic.Json.parse against Python's json module.

Random documents (nesting, escapes, non-ASCII, surrogate pairs, numbers), written the way Go's
encoding/json writes them and a few other ways, must parse to the same value; malformed documents must
be refused, never crash or hang.
"""
import json, os, random, subprocess, sys, tempfile

here = os.path.dirname(os.path.abspath(__file__))
exe = os.path.join(here, "..", ".lake", "build", "bin", "jsoncheck")
random.seed(3)
alphabet = "abcXYZ 09\"\\/\b\f\n\r\t\x01\x1féü名前😀 <>&"

def rstr():
    return "".join(random.choice(alphabet) for _ in range(random.randint(0, 12)))

def value(d=0):
    k = random.randint(0, 7 if d < 5 else 4)
    if k == 0: return None
    if k == 1: return random.choice([True, False])
    if k == 2: return random.randint(0, 2**64)
    if k == 3: return rstr()
    if k == 4: return random.randint(-1000, 1000)
    if k == 5: return [value(d + 1) for _ in range(random.randint(0, 4))]
    return {rstr(): value(d + 1) for _ in range(random.randint(0, 4))}

def go(v):
    """What Go's encoding/json decodes: an unpaired surrogate becomes U+FFFD."""
    if isinstance(v, str): return "".join("\ufffd" if 0xD800 <= ord(c) < 0xE000 else c for c in v)
    if isinstance(v, list): return [go(x) for x in v]
    if isinstance(v, dict): return {go(k): go(x) for k, x in v.items()}
    return v

ok = bad = refused = crashes = 0
with tempfile.TemporaryDirectory() as tmp:
    path = os.path.join(tmp, "doc.json")
    for i in range(400):
        v = value()
        text = json.dumps(v, ensure_ascii=(i % 2 == 0), indent=(2 if i % 3 == 0 else None))
        open(path, "w", encoding="utf-8").write(text)
        r = subprocess.run([exe, path], capture_output=True, timeout=60)
        if r.returncode == 0 and json.loads(r.stdout.decode()) == v:
            ok += 1
        else:
            bad += 1
            print("FAIL:", text[:200], r.stderr.decode()[:200])
    for _ in range(300):
        text = json.dumps(value())
        if not text: continue
        pos = random.randrange(len(text))
        text = text[:pos] + random.choice(['"', "{", "]", ",", "\\", ":", "", "\\u12"]) + text[pos + 1:]
        open(path, "w", encoding="utf-8").write(text)
        try:
            r = subprocess.run([exe, path], capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            crashes += 1; continue
        if r.returncode not in (0, 1):
            crashes += 1
            continue
        try:
            want = go(json.loads(text))
            if r.returncode == 1 or json.loads(r.stdout.decode()) != want:
                bad += 1; print("DIFFERS on a still-valid document:", text[:200])
        except json.JSONDecodeError:
            if r.returncode == 0:
                bad += 1; print("ACCEPTED invalid JSON:", text[:200])
            else:
                refused += 1
print(f"{ok} documents parsed identically; {refused} malformed refused; {bad} failures; {crashes} crashes or hangs")
sys.exit(1 if bad or crashes else 0)
