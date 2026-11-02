#!/usr/bin/env python3
"""Differential fuzzing of MlDsaOpt/NN/opt.hex (Python EVM, exact gas model)
against the FIPS 204 Python model (scripts/opt_ref.py verify_model), which is
itself cross-checked against dilithium-py on every case (dilithium-py's known
divergence: it accepts a repeated hint index inside a row; only a strict
mismatch outside that case is an error).

Usage: python3 scripts/opt_fuzz.py [--glam] NN COUNT SEED [OUT.tsv]
--glam fuzzes the Glamsterdam variant MlDsaOpt/NN/glam/opt.hex with EIP-8024.
Each case: fresh or reused key, random message length, then one mutation
(none, bit flip in pk / c-tilde / z / hint / message, hint byte set, z
coefficient at the norm boundary, truncation, extension).
"""
from __future__ import annotations

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", ".ref", "pylib"))

from dilithium_py.ml_dsa import ML_DSA_44, ML_DSA_65, ML_DSA_87  # noqa: E402

import opt_evm  # noqa: E402
import opt_ref  # noqa: E402

LIBS = {44: ML_DSA_44, 65: ML_DSA_65, 87: ML_DSA_87}


def set_z(sig, p, poly, idx, raw):
    """Set the raw zbits-bit field of z[poly][idx] to raw."""
    off = p["ctb"] + p["zbytes"] * poly
    v = int.from_bytes(sig[off:off + p["zbytes"]], "little")
    zb = p["zbits"]
    v &= ~(((1 << zb) - 1) << (zb * idx))
    v |= raw << (zb * idx)
    return sig[:off] + v.to_bytes(p["zbytes"], "little") + sig[off + p["zbytes"]:]


def repeated_hint(nn, cd):
    p = opt_ref.derived(nn)
    h = cd[p["pklen"] + p["ctb"] + p["l"] * p["zbytes"]:p["pklen"] + p["siglen"]]
    idx = 0
    for i in range(p["k"]):
        b = h[p["omega"] + i]
        row = h[idx:b] if idx <= b <= p["omega"] else b""
        if len(set(row)) != len(row):
            return True
        idx = max(idx, b)
    return False


def main():
    glam = sys.argv[1:2] == ["--glam"]
    if glam:
        del sys.argv[1]
    nn, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else None
    rng = random.Random(seed)
    lib = LIBS[nn]
    p = opt_ref.derived(nn)
    code = bytes.fromhex(open(os.path.join(HERE, "..", "MlDsaOpt", str(nn), *(["glam"] if glam else []), "opt.hex")).read().strip())
    keys = []
    bad = 0
    acc = 0
    rows = []
    for case in range(count):
        if not keys or rng.random() < 0.3:
            keys.append(lib.keygen())
        pk, sk = rng.choice(keys)
        mlen = rng.choice([0, 1, 32, 33, 69, 70, 135, 136, 205, 206, rng.randrange(0, 1200)])
        msg = bytes(rng.getrandbits(8) for _ in range(mlen))
        sig = lib.sign(sk, msg, deterministic=rng.random() < 0.5)
        kind = rng.choice(["none", "none", "pk", "ct", "z", "hint", "msg", "hintbyte", "zbound",
                           "trunc", "extend"])
        hoff = p["ctb"] + p["l"] * p["zbytes"]
        if kind == "pk":
            i = rng.randrange(len(pk) * 8)
            pk = bytearray(pk); pk[i // 8] ^= 1 << (i % 8); pk = bytes(pk)
        elif kind == "ct":
            i = rng.randrange(p["ctb"] * 8)
            sig = bytearray(sig); sig[i // 8] ^= 1 << (i % 8); sig = bytes(sig)
        elif kind == "z":
            i = rng.randrange(p["l"] * p["zbytes"] * 8) + p["ctb"] * 8
            sig = bytearray(sig); sig[i // 8] ^= 1 << (i % 8); sig = bytes(sig)
        elif kind == "hint":
            i = rng.randrange((p["omega"] + p["k"]) * 8) + hoff * 8
            sig = bytearray(sig); sig[i // 8] ^= 1 << (i % 8); sig = bytes(sig)
        elif kind == "msg" and mlen:
            i = rng.randrange(mlen * 8)
            msg = bytearray(msg); msg[i // 8] ^= 1 << (i % 8); msg = bytes(msg)
        elif kind == "hintbyte":
            i = rng.randrange(p["omega"] + p["k"])
            sig = bytearray(sig); sig[hoff + i] = rng.randrange(256); sig = bytes(sig)
        elif kind == "zbound":
            g1, beta = p["g1"], p["beta"]
            raw = rng.choice([beta, beta + 1, 2 * g1 - beta - 1, 2 * g1 - beta, 0, (1 << p["zbits"]) - 1])
            sig = set_z(sig, p, rng.randrange(p["l"]), rng.choice([0, 1, 255, rng.randrange(256)]), raw)
        cd = pk + sig + msg
        if kind == "trunc":
            cd = cd[:rng.randrange(len(cd))]
        elif kind == "extend":
            cd = cd + bytes(rng.getrandbits(8) for _ in range(rng.randrange(1, 64)))
        exp, _ = opt_ref.verify_model(nn, cd)
        if len(cd) >= p["pklen"] + p["siglen"]:
            hd = p["pklen"] + p["siglen"]
            dpy = int(lib.verify(cd[:p["pklen"]], cd[hd:], cd[p["pklen"]:hd]))
            if dpy != exp and not (dpy == 1 and repeated_hint(nn, cd)):
                print(f"MODEL/DPY DISAGREE case {case} kind {kind}", flush=True)
                bad += 1
        r = opt_evm.run(code, cd, fork="glamsterdam" if glam else "osaka")
        got = int.from_bytes(r["ret"], "big") if r["status"] == "return" and len(r["ret"]) == 32 else None
        acc += exp
        rows.append(f"{nn}\t{case}\t{kind}\t{len(cd)}\t{exp}\t{got}\t{r['gas_used']}")
        if got != exp:
            bad += 1
            print(f"MISMATCH case {case} kind {kind} len {len(cd)} exp {exp} got {got} {r['status']}",
                  flush=True)
            with open(os.path.join(HERE, "..", ".lake", "tmp", f"opt_fuzz_fail_{nn}.txt"), "a") as f:
                f.write(f"{cd.hex()} {exp} {kind}\n")
    if out:
        with open(out, "w") as f:
            f.write("\n".join(rows) + "\n")
    print(f"set {nn}: {count} cases, {acc} accepted, {bad} failures")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
