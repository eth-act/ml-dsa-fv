"""Generate `GrpA.lean`, `GrpB.lean` (the long-message schedule's two `tr`-rider groups, glam 44) from
`MlDsaOptGlam44/listing.tsv`: `python3 MlDsaOptGlam44/Main/Alt/gen.py G > MlDsaOptGlam44/Main/Alt/Grp{A,B}.lean` for G = 0, 1."""
import re,sys
import os
L=[l.rstrip('\n').split('\t') for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../listing.tsv'))][1:]
L=[(int(a),int(b),c) for a,b,c in L]
byidx={a:(b,c) for a,b,c in L}
idx_of_pc={b:a for a,b,c in L}
G={'JUMPDEST':1,'JUMP':8,'MSTORE':3,'MLOAD':3,'XOR':3,'AND':3,'POP':2,'PUSH0':2}
def gas(i):
    op=byidx[i][1].split()[0]
    if op.startswith('PUSH') and op!='PUSH0': return 3
    return G[op]
def block(i0):
    # from index i0 up to and including the next JUMP (or MCOPY exclusive)
    out=[];i=i0
    while True:
        op=byidx[i][1].split()[0]
        if op=='MCOPY': break
        out.append(i)
        if op=='JUMP': break
        i+=1
    return out
def show(pc):
    i=idx_of_pc[pc]; b=block(i)
    return b, sum(gas(j) for j in b), byidx[b[-1]][0]+1 if byidx[b[-1]][1].startswith('JUMP') else None

def L_(lst): return '[' + ', '.join(map(str,lst)) + ']'

def gen_group(g):
    col, j0 = 2 + g, 5 * g
    dst = ['SB', '(SB + 8192)'][g]
    pcS = [3953, 4357][g]
    initb, initc, _ = show(pcS)
    r_init = byidx[initb[-1]][0] + 1
    pc = r_init; rounds = []
    for b in range(5):
        b0, c0, _ = show(pc); r0 = byidx[b0[-1]][0] + 1
        b1, c1, _ = show(r0); r1 = byidx[b1[-1]][0] + 1
        b2, c2, _ = show(r1); r2 = byidx[b2[-1]][0] + 1
        rounds.append((pc, b0, c0, r0, b1, c1, r1, b2, c2, r2))
        pc = r2
    extra = []
    if g == 1:
        bc, cc, _ = show(pc); rc = byidx[bc[-1]][0] + 1
        extra = (pc, bc, cc, rc); pc = rc
    bg, cg, _ = show(pc); rg = byidx[bg[-1]][0] + 1
    d = dict(g=g, col=col, j0=j0, dst=dst, pcS=pcS, initb=initb, initc=initc, r_init=r_init,
             rounds=rounds, extra=extra, gpc=pc, bg=bg, cg=cg, rg=rg)
    d['l4'] = [byidx[i][1].split()[1] for i in initb if byidx[i][1].startswith('PUSH11')][0]
    ba, ca, _ = show(rg)
    d.update(ba=ba, ca=ca, mc_idx=ba[-1] + 1, mc_pc=byidx[ba[-1] + 1][0], pcE=byidx[ba[-1] + 1][0] + 1)
    return d

def emit(d):
    g = d['g']; col = d['col']; j0 = d['j0']; N = 'AB'[g]
    cd = 's.executionEnv.calldata'
    o = []
    last13 = g == 1
    buf = d['dst']
    post = f"Col3Lo m' {buf} {cd} {col}"
    if True:
        frame = (f"[(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800), "
                 f"({d['dst']}, {d['dst']} + 8192)" + (", (TRL, TRL + 256)]" if last13 else "]"))
    rc = []
    for bi, r in enumerate(d['rounds']):
        if last13 and bi == 4:
            rc.append(f"({r[2]} + Gas.trabs 3 + ({r[5]} + Gas.kf4 + {r[8]} + Gas.blkh))")
        else:
            rc.append(f"({r[2]} + Gas.trabs 5 + ({r[5]} + Gas.kf4 + {r[8]} + " + ("Gas.blkh))" if bi == 4 else "Gas.blk))"))
    ex = f" + ({d['extra'][2]} + Gas.cext 8)" if last13 else ""
    tailc = f" + {d['ca']} + 771"
    cost = f"{d['initc']} + Gas.ginit + " + " + ".join(rc) + ex + f" + ({d['cg']} + Gas.gfix 3)" + tailc
    o.append(f"def cost{N} : Nat := {cost}\n")
    hyps = "" if g == 0 else f"\n    (hks : KS4 m (XT {cd} {col - 1} {j0 - 5} 5))"
    flag = f"okCol3 {cd} {col}"
    if True:
        endst = f"(callState s {d['pcE']} [flag (b && {flag})] m')"
    o.append(f"""set_option maxHeartbeats 1000000 in
theorem grp{N} {{s : State}} (hs : Ctx s) (hcd : HDR ≤ {cd}.size) {{m : ByteArray}} {{b : Bool}}
    (hrc : RC4Table m) (hrho : Rho1At m {cd}){hyps} :
    ∃ m', KS4 m' (XT {cd} {col} {j0} 5) ∧ {post} ∧""" + (f"\n      (∀ x, x < 8 → word m' (TRL + 32 * x) = le64 (trOf {cd}) (8 * x)) ∧" if last13 else "") + f"""
      RC4Table m' ∧ FrameExcept m m' {frame} ∧
      Reach (callState s {d['pcS']} [flag b] m)
        {endst}
        cost{N} := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 3732 ≤ {cd}.size := hcd
  clear hcd
  have hcdC : 1312 ≤ {cd}.size := by omega
  have hcd32 : 32 ≤ {cd}.size := by omega
  have htl : [flag b].length ≤ 8 := by simp
""")
    if g == 0:
        o.append(f"""  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcdN hrho (S := XT {cd} 2 0 0) (keep := 0) (kmask := 0)
    (j0 := 0) (col := {col}) (il_eq_zero fun k _ => by simp).symm
    (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
    (fun k _ => by simp) (fun h => by simp at h) (fun _ => rfl) (by norm_num)
    (pc0 := {d['pcS']}) (r := {d['r_init']}) (c0 := {d['initc']}) (l4 := {d['l4']}) (b := b) (by decide +kernel)
    (by glam44_rreach {L_(d['initb'])} with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
""")
    else:
        o.append(f"""  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcdN hrho (S := XT {cd} {col - 1} {j0 - 5} 5) (kmask := 8)
    (j0 := {j0}) (col := {col}) keep8 (fun x hx => by rw [keep8]; exact ks4_and_keep hks 8 hx)
    (fun k hk => by interval_cases k <;> decide) (fun _ => by unfold XT; rw [if_neg (by decide)])
    (fun h => absurd h (by decide)) (by norm_num)
    (pc0 := {d['pcS']}) (r := {d['r_init']}) (c0 := {d['initc']}) (l4 := {d['l4']}) (b := b) (by decide +kernel)
    (by glam44_rreach {L_(d['initb'])} with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
""")
    o.append("  have hrc1 := RC4Table.frame hrc hf1 (by alt_frame)\n")
    prevB = "(HBlocks.zero _ _ _ _)"
    for bi, r in enumerate(d['rounds']):
        pc0, b0, c0, r0, b1, c1, r1, b2, c2, r2 = r
        mi, mo = f"m{bi+1}", f"m{bi+2}"
        if last13 and bi == 4:
            o.append(f"""  -- the last block of pk (9) and its padding
  have g30 : Reach (callState s {pc0} [flag b] {mi}) (callState s 18792
      [wd 0, wd 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000, wd 3, wd 3, wd 1224,
        wd {r0}, flag b] {mi}) {c0} := by
    glam44_rreach {L_(b0)}
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := {r0}) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) {mi}
    (off := 1224) (sh := 3) (n4 := 3) (lm := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000)
    (kp := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lmL_top3 (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s {r0} [flag b] mt) (callState s 42887 [wd {r1}, flag b]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512))
      {c1} := by
    glam44_rreach {L_(b1)} with [KS]
  have hwp := fun x (hx : x < 25) => pad_words (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(352, 352 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp := ks4_trabs_last hcdC (XT_sized _ {col} {j0} 4) hks{bi+1} fun x hx => by
    rw [hwp x hx, trabs_norm hwt x hx]
  have hBp := (hB{bi+1}.frame hft (by alt_frame) (by alt_frame)).frame hfp (by alt_frame) (by alt_frame)
  obtain ⟨{mo}, hks{bi+2}', hB{bi+2}, hrc{bi+2}, hf{bi+2}, hR{bi+2}⟩ := kbh_round hs htl (stk := [wd {r1}, flag b])
    (m := Mp) (pc0 := 42887) (r1 := {r1}) (r2 := {r2}) (c1 := 0) (c2 := {c2}) bufOK_abuf (Reach.refl _)
    (fun _ => by glam44_rreach {L_(b2)} with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame (RC4Table.frame hrc{bi+1} hft (by alt_frame)) hfp (by alt_frame))
    (upd_sized (XT_sized _ {col} {j0} 4) (by rw [xorBlock_size]; exact XT_sized _ {col} {j0} 4 3 (by norm_num)))
    hksp hBp (St := fun b k => XT {cd} {col} {j0} (b + 1) k)
    (fun k hk => (permute_upd_XT _ {col} {j0} 4 hk).symm)
  have hks{bi+2} : KS4 {mo} (XT {cd} {col} {j0} 5) := KS4.congr hks{bi+2}' fun k hk => permute_upd_XT _ {col} {j0} 4 hk
  have hf{bi+2}x := FrameExcept.trans (FrameExcept.trans hft hfp) hf{bi+2}
  have hR{bi+2}x := ((g30.trans hct).trans gpad).trans hR{bi+2}
""")
            continue
        lemma = "absorb_round_h" if bi == 4 else "absorb_round"
        bpart = "" if bi == 4 else f"(b := {bi}) "
        bproof = "" if bi == 4 else "(by norm_num) "
        o.append(f"""  obtain ⟨{mo}, hks{bi+2}', hB{bi+2}, hrc{bi+2}, hf{bi+2}, hR{bi+2}⟩ := {lemma} hs hcdC htl (m := {mi})
    (pc0 := {pc0}) (r0 := {r0}) (r1 := {r1}) (r2 := {r2}) (c0 := {c0}) (c1 := {c1}) (c2 := {c2})
    {bpart}(j := {j0+bi}) (off := {136*(j0+bi)}) (sh := 3) {bproof}(by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam44_rreach {L_(b0)})
    (fun _ => by glam44_rreach {L_(b1)})
    (fun _ => by glam44_rreach {L_(b2)} with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc{bi+1} (XT_sized _ {col} {j0} {bi}) hks{bi+1} {prevB} (St := fun b k => XT {cd} {col} {j0} (b + 1) k)
    (fun k hk => (permute_upd_XT _ {col} {j0} {bi} hk).symm)
  have hks{bi+2} : KS4 {mo} (XT {cd} {col} {j0} {bi+1}) := KS4.congr hks{bi+2}' fun k hk => permute_upd_XT _ {col} {j0} {bi} hk
  have hf{bi+2}x := hf{bi+2}
  have hR{bi+2}x := hR{bi+2}
""")
        prevB = f"hB{bi+2}"
    last = "m6"; hB = "hB6"; hks = "hks6"; hrcL = "hrc6"
    if last13:
        pcx, bx, cx, rx = d['extra']
        o.append(f"""  -- tr into TRL
  have gC : Reach (callState s {pcx} [flag b] m6) (callState s 19241 [wd 8, wd 3, wd TRL, wd {rx}, flag b] m6)
      {cx} := by
    glam44_rreach {L_(bx)} with [TRL]
  obtain ⟨m7, htrl, hf7, hc7⟩ := cext_call hs (ret := {rx}) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := TRL) (sh := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have hks7 := KS4.frame hks6 hf7 (by alt_frame)
  have hB7 := hB6.frame hf7 (by alt_frame) (by alt_frame)
  have hrc7 := RC4Table.frame hrc6 hf7 (by alt_frame)
""")
        last = "m7"; hB = "hB7"; hks = "hks7"; hrcL = "hrc7"
    allf = "hf2x"
    for k in range(3, 7): allf = f"(FrameExcept.trans {allf} hf{k}x)"
    if last13: allf = f"(FrameExcept.trans {allf} hf7)"
    Rs = "hR1"
    for k in range(2, 7): Rs = f"({Rs}.trans hR{k}x)"
    if last13: Rs = f"(({Rs}.trans gC).trans hc7)"
    o.append(f"""  have hfB := {allf}
  have h6L : word {last} HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by alt_frame) le_rfl le_rfl]; exact h61
  have hfA := FrameExcept.trans hf1 hfB
  -- gfix 7
  obtain ⟨m8, hl8, hks8, hf8, hR8⟩ := gfix_trio (col := {col}) (j0 := {j0}) (pc := {d['gpc']}) (r := {d['rg']})
    (c := {d['cg']}) hs hcd32 (m := {last})
    (by glam44_rreach {L_(d['bg'])})
    (by simp only [isValidJumpDest_lit]) (by norm_num) {hrcL} {hks} {hB} h6L
""")
    dc = 'SB'
    o.append(f"""  -- AND, copy ABUF to {d['dst']}
  have gA : Reach (callState s {d['rg']} [flag ({flag}), flag b] m8)
      (callState s {d['mc_pc']} [wd {d['dst']}, wd ABUF, wd 8192, flag (b && {flag})] m8) {d['ca']} := by
    glam44_rreach {L_(d['ba'])} with [flag, ite01_land, ABUF, SB]
  have hmc := reach_mcopy hs ⟨{d['mc_idx']}, by norm_num⟩ (pc := {d['mc_pc']}) (d := {d['dst']}) (src := ABUF) (n := 8192)
    (rest := [flag (b && {flag})]) (m := m8)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold {dc}; norm_num)
    (by unfold ABUF; norm_num) (by norm_num) (by norm_num) (by unfold {dc}; omega) (by unfold ABUF; omega)
    (by simp)
  have hfM := FrameExcept.mcopy m8 ABUF {d['dst']} 8192
  refine ⟨_, KS4.frame hks8 hfM (by alt_frame), col3Lo_mcopy hl8,""" + (" ?_," if last13 else "") + f"""
    (RC4Table.frame (RC4Table.frame {hrcL} hf8 (by alt_frame)) hfM (by alt_frame)),
    ((FrameExcept.trans (FrameExcept.trans hfA hf8) hfM).mono (by decide)), ?_⟩""" + (f"""
  · intro x hx
    rw [word_frame (FrameExcept.trans hf8 hfM) (lo := TRL) (hi := TRL + 256) (by alt_frame) (by omega) (by omega),
      htrl x (by omega), cext_lane hks6 (by norm_num) (by omega), le64_trOf hcdC hx]
    unfold XT; simp only [show ¬ (3 : Nat) < 3 by decide, if_false]; rfl""" if last13 else "") + f"""
  · have hR := ((({Rs}.trans hR8).trans gA).trans hmc)
    refine hR.mono (le_of_eq ?_)
    unfold cost{N}
    generalize Gas.ginit = a1; generalize Gas.trabs 5 = a2; generalize Gas.trabs 3 = a3
    generalize Gas.kf4 = a4; generalize Gas.blk = a5; generalize Gas.blkh = a6; generalize Gas.cext 8 = a7
    generalize Gas.gfix 3 = a8
    omega
""")
    return "\n".join(o)

hdr = """import MlDsaOptGlam44.Main.Alt.Defs
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # The long-message schedule's `tr`-rider group (generated by `Main/Alt/gen.py`; see `Main/SegAlt.lean`) -/

namespace MlDsaOptGlam44.Proofs.Alt

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs
open MlDsaOptGlam44.Proofs.Ex
open MlDsaOptGlam44.Proofs.Infra

"""
g = int(sys.argv[1])
print(hdr + emit(gen_group(g)) + "\nend MlDsaOptGlam44.Proofs.Alt")
