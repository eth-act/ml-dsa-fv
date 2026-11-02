#!/usr/bin/env python3
"""Worst-case gas of MlDsaOpt/NN/opt.hex over adversarial inputs.

Control flow depends on data only in four places:
  * RejNTTPoly fix-ups (`fix`, `gfix`) and the 6th squeeze;
  * SampleInBall's byte loop (<= 264 bytes);
  * HintBitUnpack's loops (<= omega indices);
  * mu's block count (a function of the message length only).
Everything else is straight-line or has data-independent loop counts. So
for a fixed calldata length

  worst = typical - (fix + gfix + SampleInBall + hint gas of the typical run)
        + worst(fix, gfix) + worst(SampleInBall) + worst(hint).

The routine worst cases are measured in isolation (start_pc + crafted
memory) with patterns that take the most expensive path:
  * fix: every flag word of the slot set (scalar path), 256 accepted plus
    80 rejected candidates over all 42 groups, the 6th squeeze paid once per
    group; per-group and per-candidate costs are solved from three crafted
    runs, the 6th squeeze is measured;
  * SampleInBall: 264 - tau rejected bytes, then tau accepted bytes that hit
    an existing nonzero position (the "moved" branch);
  * hints: all omega indices in one row, strictly decreasing (every index
    takes the failing order check).
Usage: python3 scripts/opt_worstcase.py [--version v3|v4|glam] [NN ...]
  glam: the Glamsterdam variant MlDsaOpt/NN/glam/ (scripts/gen_glam.py, v4
        with stack-resident Keccak), run with EIP-8024.
"""
from __future__ import annotations

import functools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_opt  # noqa: E402
import opt_evm  # noqa: E402
import opt_ref  # noqa: E402

Q = opt_ref.Q
VEC = {44: "vectors/calldata.txt", 65: "vectors/mldsa65/calldata.txt", 87: "vectors/mldsa87/calldata.txt"}


def regions(g, code, prof):
    rp = g.a.region_pcs + [(len(code), "END")]
    return {n: sum(prof[a:b]) for (a, n), (b, _) in zip(rp, rp[1:])}


def analyse(nn, version="v4"):
    if version == "glam":
        import gen_glam
        g, code = gen_glam.build(nn)
        L = g.L
        run = functools.partial(opt_evm.run, fork=gen_glam.FORK)
    else:
        L = gen_opt.Layout(nn, version)
        g = gen_opt.Gen(L)
        code = g.build()
        run = opt_evm.run
    sub = (version,) if version in ("v2", "v3", "glam") else ()
    with open(os.path.join(HERE, "..", "MlDsaOpt", str(nn), *sub, "opt.hex")) as f:
        assert f.read().strip() == code.hex(), "stale artifact"
    lab = g.a.labels
    hcode = code + b"\x5b\x00"            # harness return target: JUMPDEST STOP
    RET = len(code)
    cd = bytes.fromhex(open(os.path.join(HERE, "..", VEC[nn])).readline().split()[0])
    base = run(code, cd, profile=True)
    reg = regions(g, code, base["prof"])
    mem0 = base["memory"]
    W = lambda m, a: int.from_bytes(m[a:a + 32], "big")  # noqa: E731

    def put(m, a, v):
        m[a:a + 32] = (v & opt_ref.M256).to_bytes(32, "big")

    # ── fix: scalar path over flagged groups ─────────────────────────────
    def fix_run(rej, nflag=42, keep_ext=False):
        m = bytearray(mem0)
        put(m, L.MISC + 0x1E0, 0)
        for t in range(336):
            put(m, L.ABUF + 32 * t, (Q if t in rej else 5))
        for c in range(42):
            put(m, L.FL + 32 * c, (1 << 23) if c < nflag else 0)
        r = run(hcode, b"", memory=m, stack=[RET, 0], start_pc=lab["fix"], profile=True)
        assert r["status"] == "stop", r["status"]
        return r
    gA = fix_run(set())["gas_used"]                                  # 32 groups, 256 accepts
    gB = fix_run({8 * c for c in range(8)})["gas_used"]              # 33 groups, 8 rejects
    gC = fix_run({8 * c for c in range(24)})["gas_used"]             # 35 groups, 24 rejects
    # gB - gA = go + 8 r ; gC - gB = 2 go + 16 r  -> consistent; take per-candidate cost of a
    # flagged group of 8 rejections as an upper bound for the remaining groups
    go_8r = gB - gA
    # 6th squeeze: force it (70 rejections in the first 35 groups)
    rx = fix_run({8 * c + d for c in range(35) for d in (0, 1)})
    regx = regions(g, hcode, rx["prof"])
    ext = regx["kf4"] + regx["blk"] + 2 * (3 + 3 * 25) + 40
    # worst path: 42 flagged groups, 256 accepts + 80 rejects, + the 6th squeeze
    fix_worst = gA + 10 * go_8r + ext                # 32 + 10 groups; 80 rejects <= 10 * 8
    fix_worst_noext = fix_worst - ext

    # ── gfix own cost with every slot flagged (fix calls excluded) ────────
    m = bytearray(mem0)
    put(m, L.MISC + 0x1E0, 1)                        # HAVE6 set: no squeeze inside
    for t in range(336):
        put(m, L.ABUF + 32 * t, 5 | 5 << 64 | 5 << 128 | 5 << 192)
    flag = sum(1 << (23 + 64 * s) for s in range(4))
    for c in range(42):
        put(m, L.FL + 32 * c, flag)
    r = run(hcode, b"", memory=m, stack=[RET, 15], start_pc=lab["gfix"], profile=True)
    rg = regions(g, hcode, r["prof"])
    gfix_worst = rg["gfix"]

    groups = g.schedule
    nact = [sum(1 for x in gr["slots"] if x and x[0] == "A") for gr in groups]
    fix_total_worst = sum(gfix_worst + ext + n * fix_worst_noext for n in nact)

    # ── SampleInBall ─────────────────────────────────────────────────────
    tau = L.p["tau"]
    if g.simd_c():
        m = bytearray(mem0)
        for a_ in range(L.CW, L.CW + 0x2000, 32):
            put(m, a_, 0)
        for a_ in range(L.IDX, L.IDX + 0x100, 32):
            put(m, a_, 0)
        put(m, L.MISC + 0x1C0, 0)
        put(m, L.MISC + 0x1A0, 0)
        stream = bytearray(272)
        for p in range(8, 272 - tau):
            stream[p] = 0xFF
        lanes = opt_ref.bytes_to_lanes(bytes(stream))
        for x, v in enumerate(lanes):
            put(m, L.CB + 32 * x, v)
        if g.c_saved:
            # R4-7 (44): the second block is squeezed on demand from c's saved
            # state, which would replace the crafted bytes; measure the byte
            # loop on a build without that squeeze and add its cost (kf4,
            # cext of 17 lanes, the 25-word state copy and the limit update)
            if version == "glam":
                gd, dcode = gen_glam.build(nn, dbg_c2_off=True)
            else:
                gd = gen_opt.Gen(gen_opt.Layout(nn, version))
                gd.dbg_c2_off = True
                dcode = gd.build()
            dcode += b"\x5b\x00"
            r = run(dcode, b"", memory=m, stack=[len(dcode) - 2], start_pc=gd.a.labels["sib"])
            assert r["status"] == "stop" and r["stack"][-1] == 1
            cext17 = run(hcode, b"", memory=bytearray(mem0), stack=[RET, L.CB + 17 * 32, 0, 17],
                         start_pc=lab["cext"])["gas_used"]
            sib_worst = r["gas_used"] + reg["kf4"] // base["cnt"][lab["kf4"]] + cext17 + 3 * 3 + 3 + 3 * 25 + 60
        else:
            r = run(hcode, b"", memory=m, stack=[RET], start_pc=lab["sib"])
            assert r["status"] == "stop" and r["stack"][-1] == 1
            sib_worst = r["gas_used"]
    elif g.wc_sib:
        # v4 kf1 variant (lane-unrolled loop): exact, in three segments:
        # block 1 (128 rejected bytes) up to the 2nd squeeze, the squeeze,
        # block 2 ((136 - tau) rejected, then tau accepted bytes, j = 0)
        loop = [k for k in lab if k.startswith("sibloop")][0]
        sq = [k for k in lab if k.startswith("sibsq")][0]
        nok = [k for k in lab if k.startswith("sibnok")][0]

        def crafted(stream):
            m = bytearray(mem0)
            for a_ in range(L.CW, L.CW + 0x2000, 32):
                put(m, a_, 0)
            for a_ in range(L.IDX, L.IDX + 0x100, 32):
                put(m, a_, 0)
            put(m, L.MISC + 0x1C0, 0)
            put(m, L.MISC + 0x1A0, 0)
            for x, v in enumerate(opt_ref.bytes_to_lanes(bytes(stream))):
                put(m, L.KS + 32 * x, v * gen_opt.REP)
            return m
        r = run(hcode, cd, memory=bytearray(mem0), stack=[RET], start_pc=lab["sib"],
                        stop_pc=lab[loop])
        assert r["status"] == "break"
        setup = r["gas_used"]
        r1 = run(hcode, b"", memory=crafted(bytes(8) + b"\xff" * 128), stack=[RET, 0, 256 - tau, 32],
                         start_pc=lab[loop], stop_pc=lab[sq])
        assert r1["status"] == "break" and r1["stack"][-1] == 17 * 32
        r2 = run(hcode, b"", memory=bytearray(mem0), stack=[RET, 0, 256 - tau, 17 * 32],
                         start_pc=lab[sq], stop_pc=lab[nok])
        assert r2["status"] == "break"
        r3 = run(hcode, b"", memory=crafted(b"\xff" * (136 - tau) + bytes(tau)),
                         stack=[RET, 0, 256 - tau, 17 * 32], start_pc=lab[nok])
        assert r3["status"] == "stop" and r3["stack"][-1] == 1
        sib_worst = setup + r1["gas_used"] + r2["gas_used"] + r3["gas_used"]
    else:
        # kf1 variant: per-iteration costs from two crafted block-1 runs, then
        # 264 iterations + the second squeeze
        loop = [k for k in lab if k.startswith("sibloop")][0]

        def sib_loop(nrej, nacc):
            m = bytearray(mem0)
            for a_ in range(L.CW, L.CW + 0x2000, 32):
                put(m, a_, 0)
            for a_ in range(L.IDX, L.IDX + 0x100, 32):
                put(m, a_, 0)
            put(m, L.MISC + 0x1C0, 0)
            put(m, L.MISC + 0x1A0, 0)
            stream = bytearray(136)
            for p in range(8, 8 + nrej):
                stream[p] = 0xFF
            for x, v in enumerate(opt_ref.bytes_to_lanes(bytes(stream))):
                put(m, L.KS + 32 * x, v * gen_opt.REP)
            r = run(hcode, b"", memory=m, stack=[RET, 0, 256 - nacc, 8], start_pc=lab[loop])
            assert r["status"] == "stop"
            return r["gas_used"]
        s1 = sib_loop(100, 10)
        s2 = sib_loop(110, 10)
        s3 = sib_loop(100, 20)
        rej_c = (s2 - s1) / 10
        acc_c = (s3 - s1) / 10
        fixed = s1 - 100 * rej_c - 10 * acc_c
        r = run(hcode, cd, memory=bytearray(mem0), stack=[RET], start_pc=lab["sib"],
                        stop_pc=lab[loop])
        assert r["status"] == "break"
        setup = r["gas_used"]
        kf1 = reg["kf1"] / base["cnt"][lab["kf1"]]
        sib_worst = setup + (264 - tau) * rej_c + tau * acc_c + fixed + kf1 + 30 + 8 * 15

    # ── hints ────────────────────────────────────────────────────────────
    hoff = L.H0
    om = L.p["omega"]
    hb = bytearray(cd[hoff:hoff + om + L.k])
    for i in range(om):
        hb[i] = 255 - i
    for i in range(L.k):
        hb[om + i] = om
    cdh = cd[:hoff] + bytes(hb) + cd[hoff + om + L.k:]
    rh = run(code, cdh, profile=True)
    hint_worst = regions(g, code, rh["prof"])["decode_hint"]

    typical = base["gas_used"]
    datadep = reg["fix"] + reg["gfix"] + reg["sample_in_ball"] + reg["decode_hint"]
    if not g.simd_c():
        datadep += 0
    if "blkt" in lab:
        # v4: the last block's tail (blkt) is made only for groups with a
        # fix-up; the worst case makes it in every group
        rt = run(hcode, b"", memory=bytearray(mem0), stack=[RET], start_pc=lab["blkt"])
        assert rt["status"] == "stop"
        ntail = base["cnt"][lab["blkt"]]
        fix_total_worst += (len(groups) - ntail) * rt["gas_used"]
    worst = typical - datadep + fix_total_worst + sib_worst + hint_worst
    return dict(nn=nn, typical=typical, worst=int(worst), fix_typ=reg["fix"] + reg["gfix"],
                fix_worst=fix_total_worst, sib_typ=reg["sample_in_ball"], sib_worst=int(sib_worst),
                hint_typ=reg["decode_hint"], hint_worst=hint_worst, ext=ext,
                per_instance=fix_worst_noext, groups=len(groups), instances=sum(nact))


def main(argv):
    version = "v4"
    if argv[:1] == ["--version"]:
        version, argv = argv[1], argv[2:]
    for nn in [int(x) for x in argv] or [44, 65, 87]:
        r = analyse(nn, version)
        print(f"ML-DSA-{nn} {version}: typical {r['typical']:,}  worst {r['worst']:,}  (|M| = 0)")
        print(f"  fix-ups: typical {r['fix_typ']:,}  worst {r['fix_worst']:,} "
              f"({r['instances']} instances x {r['per_instance']:,} + {r['groups']} groups x 6th squeeze {r['ext']:,})")
        print(f"  SampleInBall: typical {r['sib_typ']:,}  worst {r['sib_worst']:,}")
        print(f"  HintBitUnpack: typical {r['hint_typ']:,}  worst {r['hint_worst']:,}")


if __name__ == "__main__":
    main(sys.argv[1:])
