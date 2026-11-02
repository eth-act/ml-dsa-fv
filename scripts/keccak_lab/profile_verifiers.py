"""Per-subroutine self gas, call counts and code size of the v4 and glam
verifiers on the valid empty-message vector (line 1 of each calldata.txt).
Input for model.py. Prints a JSON blob."""
from __future__ import annotations

import functools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))

import gen_opt  # noqa: E402
import opt_evm  # noqa: E402

VEC = {44: "vectors/calldata.txt", 65: "vectors/mldsa65/calldata.txt", 87: "vectors/mldsa87/calldata.txt"}


def profile(nn, version):
    if version == "glam":
        import gen_glam
        g, code = gen_glam.build(nn)
        run = functools.partial(opt_evm.run, fork=gen_glam.FORK)
    else:
        g = gen_opt.Gen(gen_opt.Layout(nn, version))
        code = g.build()
        run = opt_evm.run
    cd = bytes.fromhex(open(os.path.join(HERE, "..", "..", VEC[nn])).readline().split()[0])
    r = run(code, cd, profile=True)
    assert r["status"] == "return", r["status"]
    rp = g.a.region_pcs + [(len(code), "END")]
    out = {"total": r["gas_used"], "size": len(code), "regions": {}}
    for (a, n), (b, _) in zip(rp, rp[1:]):
        calls = r["cnt"][g.a.labels[n]] if n in g.a.labels else None
        out["regions"][n] = {"gas": sum(r["prof"][a:b]), "calls": calls, "bytes": b - a}
    return out


if __name__ == "__main__":
    res = {f"{v}/{nn}": profile(nn, v) for v in ("v4", "glam") for nn in (44, 65, 87)}
    print(json.dumps(res, indent=1))
