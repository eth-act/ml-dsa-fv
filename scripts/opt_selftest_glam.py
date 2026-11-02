#!/usr/bin/env python3
"""Self-tests for the Glamsterdam variant (scripts/gen_glam.py).

  python3 scripts/opt_selftest_glam.py [quick]

1. The EIP-8024 test cases (eips.ethereum.org/EIPS/eip-8024) on opt_evm.
2. Stack-resident Keccak-f kernels (kf4 interleaved, kf1 replicated) vs the
   reference permutation on random and all-ones states, with their gas per
   call next to the v3 kernels'.
3. The 4 + 4 NTT's forward bias bounds (Shoup on layers 1-4); v2 / v3
   (SHA-256 pins) and v4 artifacts are still byte-identical.
4. Every vector of all three sets on MlDsaOpt/NN/glam/opt.hex, and valid /
   flipped-message signatures at mu's block boundaries (opt_selftest).
5. Forced sixth squeeze (debug build, as in opt_selftest.py).
"quick" skips 4 and 5.
"""
from __future__ import annotations

import functools
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_glam  # noqa: E402
import gen_opt  # noqa: E402
import opt_evm  # noqa: E402
import opt_ref  # noqa: E402
import opt_selftest  # noqa: E402
from opt_asm import Asm  # noqa: E402
from opt_keccak import gen_keccak_f, rc_table, COMPLEMENTED, REP  # noqa: E402
from opt_keccak_glam import gen_keccak_stack  # noqa: E402

ROOT = os.path.join(HERE, "..")
glam_run = functools.partial(opt_evm.run, fork=gen_glam.FORK)


def test_eip8024():
    def r(h):
        x = glam_run(bytes.fromhex(h))
        return x["status"], x["stack"]
    s, st = r("60016000808080808080808080808080808080e680")
    assert s == "stop" and len(st) == 18 and st[-1] == 1 and st[0] == 1 and sum(st) == 2
    s, st = r("600160008080808080808080808080808080806002e780")
    assert len(st) == 18 and st[-1] == 1 and st[0] == 2 and sum(st) == 3
    s, st = r("600260008080808080600160008080808080808080e8")
    assert len(st) == 17 and st[0] == 1 and st[-10] == 2 and sum(st) == 3
    assert r("600060016002e88e")[1] == [1, 0, 2]
    s, st = r("600080808080808080808080808080808080808080808080808080808060016002e88f")
    assert len(st) == 30 and st[-1] == 2 and st[0] == 1 and sum(st) == 3
    assert r("e75b")[0].startswith("error")
    assert r("600456e65b")[0] == "stop"
    assert r("60008080e88e15")[1] == [0, 0, 1]
    assert r("e852")[0].startswith("error")
    assert r("6000808080808080808080808080808080e680")[0].startswith("error")
    assert opt_evm.run(bytes.fromhex("e680"))["status"].startswith("error")   # undefined before Glamsterdam
    print("eip-8024: test cases ok")


def test_keccak():
    ST, BT, RCT, KZ = 0, 0x320, 0x640, 0x940
    rng = random.Random(3)

    def harness(gen):
        a = Asm()
        a.pushl("done")
        a.jump("kf")
        a.label("done")
        a.op("STOP")
        gen(a)
        return a.assemble()
    for scale in (4, 1):
        gas = {}
        for kind in ("v3", "glam"):
            if kind == "v3":
                code = harness(lambda a: gen_keccak_f(a, "kf", ST, BT, RCT, 2, scale,
                                                      kz_addr=KZ if scale == 1 else None))
            else:
                code = harness(lambda a: gen_keccak_stack(a, "kf", ST, scale))
            for t in range(4):
                n = 4 if scale == 4 else 1
                states = [[rng.getrandbits(64) if t else opt_ref.M64 for _ in range(25)] for _ in range(n)]
                mem = bytearray(KZ + 25 * 32)
                for i in range(25):
                    w = opt_ref.interleave([s[i] for s in states]) if scale == 4 else states[0][i] * REP
                    if i in COMPLEMENTED:
                        w ^= opt_ref.M256
                    mem[ST + 32 * i:ST + 32 * i + 32] = w.to_bytes(32, "big")
                if kind == "v3":
                    for i, v in enumerate(rc_table(scale)):
                        mem[RCT + 32 * i:RCT + 32 * i + 32] = v.to_bytes(32, "big")
                r = glam_run(code, b"", memory=mem)
                assert r["status"] == "stop" and r["stack"] == [], r["status"]
                out = [int.from_bytes(r["memory"][32 * i:32 * i + 32], "big")
                       ^ (opt_ref.M256 if i in COMPLEMENTED else 0) for i in range(25)]
                exp = [opt_ref.keccak_f(s) for s in states]
                if scale == 4:
                    assert all(opt_ref.deinterleave(out[i]) == [e[i] for e in exp] for i in range(25))
                else:
                    assert all(out[i] == exp[0][i] * REP for i in range(25))
                if kind == "glam":
                    assert r["memory"][25 * 32:] == mem[25 * 32:], "kernel wrote outside the state"
            # harness: PUSH2 + JUMP + JUMPDEST (+ 3 to match the per-call profile convention)
            gas[kind] = r["gas_used"] - 15
        print(f"keccak: kf{4 if scale == 4 else 1} stack-resident ok, {gas['glam']:,} gas per call "
              f"(v3 {gas['v3']:,}, {100 * (gas['glam'] - gas['v3']) / gas['v3']:+.1f}%)")


def test_ntt_bounds():
    """v4's forward-NTT bias bounds (opt_selftest.test_constants) with the
    glam pass split: Shoup (immediate zetas) on layers 1-4, Montgomery on 5-8."""
    Q = opt_ref.Q
    for nn in (44, 65, 87):
        p = opt_ref.derived(nn)
        lo, hi = p["g1"] + 9 * Q - (1 << p["zbits"]) + 1, p["g1"] + 9 * Q
        for layer in range(8):
            t = hi * (Q - 1)
            assert t < 1 << 64 and hi < 1 << 32
            umax = Q + (hi * Q >> 32) + 1 if layer < 4 else (t >> 32) + Q
            lo, hi = lo - umax, hi + umax
            assert lo >= 0 and hi < 1 << 28
    print("ntt 4+4: forward bias bounds hold with Shoup on layers 1-4")


def test_base_unchanged():
    opt_selftest.test_proved_reproducible()
    for nn in (44, 65, 87):
        code = gen_opt.Gen(gen_opt.Layout(nn, "v4")).build()
        with open(os.path.join(ROOT, "MlDsaOpt", str(nn), "opt.hex")) as f:
            assert f.read().strip() == code.hex(), f"v4 {nn} changed"
    print("v4: artifacts unchanged")


def test_bytecode(force6=False):
    opt_selftest.opt_evm = type("E", (), {"run": staticmethod(glam_run)})   # run_vectors on Glamsterdam
    for nn in (44, 65, 87):
        g, code = gen_glam.build(nn, **({"dbg_force6": True} if force6 else {}))
        assert len(code) <= gen_glam.CODE_LIMIT
        if not force6:
            with open(os.path.join(ROOT, "MlDsaOpt", str(nn), "glam", "opt.hex")) as f:
                assert f.read().strip() == code.hex(), "glam artifact is stale: run gen_glam.py"
        bad, ext = opt_selftest.run_vectors(nn, code, g if force6 else None)
        assert bad == 0, (nn, bad)
        print(f"glam bytecode{' (forced 6th squeeze)' if force6 else ''}: {nn} ok"
              + (f", {ext} vectors with 6th-block checks" if force6 else ""))
    opt_selftest.opt_evm = opt_evm


def main():
    quick = sys.argv[1:] == ["quick"]
    test_eip8024()
    test_keccak()
    test_ntt_bounds()
    test_base_unchanged()
    if not quick:
        test_bytecode()
        opt_selftest.test_mu_lengths("glam", build=lambda nn: gen_glam.build(nn)[1], run=glam_run)
        opt_selftest.test_c2(build=lambda **d: gen_glam.build(44, **d), run=glam_run, label="glam")
        os.environ["OPT_DBG_NO_OVERLAY"] = "1"
        test_bytecode(force6=True)
    print("all glam self-tests passed")


if __name__ == "__main__":
    main()
