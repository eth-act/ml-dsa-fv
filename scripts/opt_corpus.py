#!/usr/bin/env python3
"""Verdicts and gas of optimised verifier builds on a set's corpus (Python EVM).

  python3 scripts/opt_corpus.py NN V[,V...] [JOBS]

Corpus: ML-DSA-44 = foundry/fixtures/vectors.txt + foundry/fixtures/fuzz/*.txt
(the 3,639 cases opt_forge.sh replays in revm); 65 / 87 = the vector file
vectors/mldsa{65,87}/calldata.txt. V is v3 (MlDsaOpt/NN/), v4 or glam
(MlDsaOpt/NN/v4|glam/) or a directory holding NN/opt.hex; a V containing
"glam" runs with EIP-8024 (fork glamsterdam). Prints per build: mismatches, and gas median /
mean / max over all cases and over the accepted ones.
"""
from __future__ import annotations

import glob
import multiprocessing
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
sys.path.insert(0, HERE)

import opt_evm  # noqa: E402

CODES = {}


def corpus(nn):
    if nn == 44:
        files = [os.path.join(ROOT, "foundry/fixtures/vectors.txt")] + \
            sorted(glob.glob(os.path.join(ROOT, "foundry/fixtures/fuzz/*.txt")))
    else:
        files = [os.path.join(ROOT, f"vectors/mldsa{nn}/calldata.txt")]
    out = []
    for f in files:
        for line in open(f):
            p = line.split()
            if p:
                out.append((b"" if p[0] == "-" else bytes.fromhex(p[0]), int(p[1])))
    return out


def load(nn, v):
    d = os.path.join(v, str(nn)) if os.path.isdir(v) else \
        os.path.join(ROOT, "MlDsaOpt", str(nn), *([] if v == "v3" else [v]))
    return bytes.fromhex(open(os.path.join(d, "opt.hex")).read().strip())


def run(case):
    cd, exp = case
    res = []
    for v, code in CODES.items():
        r = opt_evm.run(code, cd, fork="glamsterdam" if "glam" in v else "osaka")
        got = int.from_bytes(r["ret"], "big") if r["status"] == "return" and len(r["ret"]) == 32 else None
        res.append((v, exp, got, r["gas_used"]))
    return res


def med(xs):
    xs = sorted(xs)
    n = len(xs)
    return xs[n // 2] if n % 2 else (xs[n // 2 - 1] + xs[n // 2]) // 2


def main(argv):
    nn, vs = int(argv[0]), argv[1].split(",")
    jobs = int(argv[2]) if len(argv) > 2 else os.cpu_count()
    for v in vs:
        CODES[v] = load(nn, v)
    cases = corpus(nn)
    with multiprocessing.Pool(jobs) as pool:
        results = pool.map(run, cases, chunksize=8)
    bad = 0
    for i, v in enumerate(vs):
        rs = [r[i] for r in results]
        mism = sum(exp != got for _, exp, got, _ in rs)
        bad += mism
        allg = [g for *_, g in rs]
        accg = [g for _, exp, got, g in rs if exp == 1]
        print(f"set {nn} {v}: {len(rs)} cases, {mism} mismatches; all: median {med(allg):,} "
              f"mean {sum(allg) // len(allg):,} max {max(allg):,}; accepted ({len(accg)}): "
              f"median {med(accg):,} mean {sum(accg) // len(accg):,} max {max(accg):,}", flush=True)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv[1:])
