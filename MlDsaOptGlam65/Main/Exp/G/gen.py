"""Generate `Grp3.lean` … `Grp6.lean`, the four inline ExpandA groups of calls 15–34
(glam ML-DSA-65), from `MlDsaOptGlam65/listing.tsv`.

Regenerate (from the repository root) with

    for g in 3 4 5 6; do python3 MlDsaOptGlam65/Main/Exp/G/gen.py $g > MlDsaOptGlam65/Main/Exp/G/Grp$g.lean; done

Groups 3, 4: row `4`, `5` (slot `k` = column `3 − k`), `ginit`, five `kf4` + `blk` / `blkh`,
`gfix 15`, copy to `ACC + 0x2000`, `SB`. Groups 5, 6: `tr` in slot 0 (blocks `0 … 4`, `5 … 9`),
rows `0 … 2` of column `3`, `4` in slots `1 … 3`, five `trabs` + `kf4` + `blk` / `blkh`, `gfix 14`,
copy to `ACC`, `SB + 0x2000`. The lemmas used are in `G/Defs.lean` and `Exp/Round.lean`.
"""
import os
import sys

L = [l.rstrip('\n').split('\t')
     for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../listing.tsv'))][1:]
L = [(int(a), int(b), c) for a, b, c in L]
byidx = {a: (b, c) for a, b, c in L}
idx_of_pc = {b: a for a, b, c in L}
GAS = {'JUMPDEST': 1, 'JUMP': 8, 'MSTORE': 3, 'AND': 3, 'PUSH0': 2}


def gas(i):
    op = byidx[i][1].split()[0]
    if op.startswith('PUSH') and op != 'PUSH0':
        return 3
    return GAS[op]


def block(pc):
    """Indices from `pc` up to and including the next `JUMP` (or up to an `MCOPY`, exclusive),
    their gas, and the pc after the block."""
    out = []
    i = idx_of_pc[pc]
    while True:
        op = byidx[i][1].split()[0]
        if op == 'MCOPY':
            break
        out.append(i)
        if op == 'JUMP':
            break
        i += 1
    return out, sum(gas(j) for j in out), byidx[out[-1]][0] + 1


def L_(lst):
    return '[' + ', '.join(map(str, lst)) + ']'


CD = 's.executionEnv.calldata'
# group: (start pc, kind, row / col, j0, destination, destination unfold names)
GROUPS = {
    3: (2588, 'row', 4, None, '(ACC + 8192)', 'ACC'),
    4: (2748, 'row', 5, None, 'SB', 'SB'),
    5: (2909, 'tr', 3, 0, 'ACC', 'ACC'),
    6: (3306, 'tr', 4, 5, '(SB + 8192)', 'SB'),
}


def gen(g):
    pcS, kind, rc, j0, dst, dname = GROUPS[g]
    initb, initc, r_init = block(pcS)
    l4 = [byidx[i][1].split()[1] for i in initb if byidx[i][1].startswith('PUSH11')][0]
    pc = r_init
    rounds = []
    for b in range(5):
        if kind == 'tr':
            b0, c0, r0 = block(pc)
            pc = r0
        else:
            b0, c0, r0 = None, None, None
        b1, c1, r1 = block(pc)
        b2, c2, r2 = block(r1)
        rounds.append((pc if kind == 'row' else None, b0, c0, r0, b1, c1, r1, b2, c2, r2))
        pc = r2
    # the start pc of each round
    starts = []
    p = r_init
    for r in rounds:
        starts.append(p)
        p = r[9]
    bg, cg, rg = block(pc)
    ba, ca, _ = block(rg)
    mc_idx = ba[-1] + 1
    mc_pc = byidx[mc_idx][0]
    assert byidx[mc_idx][1] == 'MCOPY'
    pcE = mc_pc + 1
    o = []
    if kind == 'row':
        st = f"XR {CD} {rc}"
        flag = f"okRow {CD} {rc}"
        rcost = [f"({r[5]} + Gas.kf4 + {r[8]} + " + ("Gas.blkh)" if bi == 4 else "Gas.blk)")
                 for bi, r in enumerate(rounds)]
        nfix = 4
    else:
        st = f"XT {CD} {rc} {j0}"
        flag = f"okCol3 {CD} {rc}"
        rcost = [f"({r[2]} + Gas.trabs 5 + ({r[5]} + Gas.kf4 + {r[8]} + " + ("Gas.blkh))" if bi == 4 else "Gas.blk))")
                 for bi, r in enumerate(rounds)]
        nfix = 3
    cost = f"{initc} + Gas.ginit + " + " + ".join(rcost) + f" + ({cg} + Gas.gfix {nfix}) + {ca} + 771"
    o.append(f"/-- The static cost of group {g}: glue constants and the calls. -/\ndef cost{g} : Nat := {cost}\n")
    frame = (f"[(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800), "
             f"({dst}, {dst} + 8192)]")
    if kind == 'row':
        post = f"RowBuf m' {dst} {CD} {rc}"
        hyps = ""
    else:
        post = f"KS4 m' ({st} 5) ∧ Col3Hi m' {dst} {CD} {rc}"
        hyps = "" if g == 5 else f"\n    (hks : KS4 m (XT {CD} 3 0 5))"
    o.append(f"""set_option maxHeartbeats 1000000 in
theorem grp{g} {{s : State}} (hs : Ctx s) (hcd : HDR ≤ {CD}.size) {{m : ByteArray}} {{b : Bool}}
    (hrc : RC4Table m) (hrho : Rho1At m {CD}){hyps} :
    ∃ m', {post} ∧
      FrameExcept m m' {frame} ∧
      Reach (callState s {pcS} [flag b] m) (callState s {pcE} [flag (b && {flag})] m') cost{g} := by
  have hsz := hs.sized
  unfold memWords at hsz
  have hcdN : 5261 ≤ {CD}.size := hcd
  clear hcd
  have hcdC : CTOFF ≤ {CD}.size := by unfold CTOFF; omega
  have hcd32 : 32 ≤ {CD}.size := by omega
  have htl : [flag b].length ≤ 8 := by simp
""")
    if kind == 'row':
        o.append(f"""  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_row hs hcd32 hrho (row := {rc}) (pc0 := {pcS}) (r := {r_init})
    (c0 := {initc}) (l4 := {l4}) (b := b) (by norm_num) (by decide +kernel)
    (by glam65_rreach {L_(initb)} with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
""")
    elif g == 5:
        o.append(f"""  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcd32 hrho (S := {st} 0) (keep := 0) (kmask := 0)
    (j0 := {j0}) (col := {rc}) (il_eq_zero fun k _ => by simp).symm
    (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
    (fun k _ _ => by simp) (fun h => by simp at h) (fun _ => rfl) (by norm_num)
    (pc0 := {pcS}) (r := {r_init}) (c0 := {initc}) (l4 := {l4}) (b := b) (by decide +kernel)
    (by glam65_rreach {L_(initb)} with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
""")
    else:
        o.append(f"""  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcd32 hrho (S := XT {CD} 3 0 5) (kmask := 1)
    (j0 := {j0}) (col := {rc}) keep1 (fun x hx => by rw [keep1]; exact ks4_and_keep hks 1 hx)
    (fun k hk1 hk4 => by interval_cases k <;> decide) (fun _ => by unfold XT; simp)
    (fun h => absurd h (by decide)) (by norm_num)
    (pc0 := {pcS}) (r := {r_init}) (c0 := {initc}) (l4 := {l4}) (b := b) (by decide +kernel)
    (by glam65_rreach {L_(initb)} with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
""")
    o.append("  have hrc1 := RC4Table.frame hrc hf1 (by expg_frame)\n")
    prevB = "(HBlocks.zero _ _ _ _)"
    for bi, r in enumerate(rounds):
        _, b0, c0, r0, b1, c1, r1, b2, c2, r2 = r
        pc0 = starts[bi]
        mi, mo = f"m{bi + 1}", f"m{bi + 2}"
        blkpc = 10193 if bi == 4 else 10187
        if kind == 'row':
            lemma = "kbh_round" if bi == 4 else "kb_round"
            bpart = "" if bi == 4 else f"(b := {bi}) (by norm_num) "
            o.append(f"""  obtain ⟨{mo}, hks{bi + 2}', hB{bi + 2}, hrc{bi + 2}, hf{bi + 2}, hR{bi + 2}⟩ := {lemma} hs htl (m := {mi})
    (stk := [flag b]) (pc0 := {pc0}) (r1 := {r1}) (r2 := {r2}) (c1 := {c1}) (c2 := {c2}) {bpart}bufOK_abuf
    (by glam65_rreach {L_(b1)})
    (fun _ => by glam65_rreach {L_(b2)} with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc{bi + 1} (XR_sized _ {rc} {bi}) hks{bi + 1} {prevB} (St := fun b k => {st} (b + 1) k)
    (fun k _ => (permute_XR _ {rc} {bi} k).symm)
  have hks{bi + 2} : KS4 {mo} ({st} {bi + 1}) := KS4.congr hks{bi + 2}' fun k _ => permute_XR _ {rc} {bi} k
""")
        else:
            lemma = "absorb_round_h" if bi == 4 else "absorb_round"
            bpart = "" if bi == 4 else f"(b := {bi}) "
            bproof = "" if bi == 4 else "(by norm_num) "
            j = j0 + bi
            o.append(f"""  obtain ⟨{mo}, hks{bi + 2}', hB{bi + 2}, hrc{bi + 2}, hf{bi + 2}, hR{bi + 2}⟩ := {lemma} hs hcdC htl (m := {mi})
    (pc0 := {pc0}) (r0 := {r0}) (r1 := {r1}) (r2 := {r2}) (c0 := {c0}) (c1 := {c1}) (c2 := {c2})
    {bpart}(j := {j}) (off := {136 * j}) (sh := 0) {bproof}(by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam65_rreach {L_(b0)})
    (fun _ => by glam65_rreach {L_(b1)})
    (fun _ => by glam65_rreach {L_(b2)} with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc{bi + 1} (XT_sized _ {rc} {j0} {bi}) hks{bi + 1} {prevB} (St := fun b k => {st} (b + 1) k)
    (fun k hk => (permute_upd_XT _ {rc} {j0} {bi} hk).symm)
  have hks{bi + 2} : KS4 {mo} ({st} {bi + 1}) := KS4.congr hks{bi + 2}' fun k hk => permute_upd_XT _ {rc} {j0} {bi} hk
""")
        prevB = f"hB{bi + 2}"
    o.append("""  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
  have h6L : word m6 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by expg_frame) le_rfl le_rfl]; exact h61
  have hfA := FrameExcept.trans hf1 hfB
""")
    if kind == 'row':
        o.append(f"""  -- gfix 15
  obtain ⟨m8, hl8, hf8, hR8⟩ := gfix_row (row := {rc}) (pc := {pc}) (r := {rg}) (c := {cg}) hs hcd32 (m := m6)
    (by glam65_rreach {L_(bg)})
    (by simp only [isValidJumpDest_lit]) (by norm_num) hrc6 hks6 hB6 h6L
""")
    else:
        o.append(f"""  -- gfix 14
  obtain ⟨m8, hl8, hks8, hf8, hR8⟩ := gfix_tr (col := {rc}) (j0 := {j0}) (pc := {pc}) (r := {rg}) (c := {cg}) hs hcd32
    (m := m6) (by glam65_rreach {L_(bg)})
    (by simp only [isValidJumpDest_lit]) (by norm_num) hrc6 hks6 hB6 h6L
""")
    copy = "rowBuf_mcopy" if kind == 'row' else "col3Hi_mcopy"
    ks = "" if kind == 'row' else "KS4.frame hks8 hfM (by expg_frame), "
    o.append(f"""  -- AND, copy ABUF to {dst}
  have gA : Reach (callState s {rg} [flag ({flag}), flag b] m8)
      (callState s {mc_pc} [wd {dst}, wd ABUF, wd 8192, flag (b && {flag})] m8) {ca} := by
    glam65_rreach {L_(ba)} with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, {dname}]
  have hmc := reach_mcopy hs ⟨{mc_idx}, by norm_num⟩ (pc := {mc_pc}) (d := {dst}) (src := ABUF) (n := 8192)
    (rest := [flag (b && {flag})]) (m := m8)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold {dname}; norm_num)
    (by unfold ABUF; norm_num) (by norm_num) (by norm_num) (by unfold {dname}; omega) (by unfold ABUF; omega)
    (by simp)
  have hfM := FrameExcept.mcopy m8 ABUF {dst} 8192
  refine ⟨_, {ks}{copy} hl8,
    ((FrameExcept.trans (FrameExcept.trans hfA hf8) hfM).mono (by decide)), ?_⟩
  have hR := (((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans hR8).trans gA).trans hmc
  refine hR.mono (le_of_eq ?_)
  unfold cost{g}
  generalize Gas.ginit = a1; generalize Gas.trabs 5 = a2; generalize Gas.kf4 = a4; generalize Gas.blk = a5
  generalize Gas.blkh = a6; generalize Gas.gfix {nfix} = a8
  omega
""")
    return "\n".join(o)


HDR = """import MlDsaOptGlam65.Main.Exp.G.Defs
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # ExpandA group {g} (glam ML-DSA-65; generated by `Exp/G/gen.py`, do not edit) -/

namespace MlDsaOptGlam65.Proofs.Exp.G

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Rho1At Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

"""

if __name__ == '__main__':
    g = int(sys.argv[1])
    print(HDR.replace('{g}', str(g)) + gen(g) + "\nend MlDsaOptGlam65.Proofs.Exp.G")
