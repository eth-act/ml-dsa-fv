"""WP S1 generator, `seg_fin` part (see `gen_s1.py`): `MlDsaOptNN/Main/S1/FinBlocks.lean`."""
from gen_s1 import Listing, CFG, N256, M64, header, pre


def fin_cfg(nn):
    X = Listing(nn); cf = CFG[nn]
    s = X.idx[cf['fin']]
    ret = next(i for i in range(s, s + 500) if X.op(i) == 'RETURN')
    jumps = [i for i in range(s, ret) if X.op(i) == 'JUMP']
    netends = [i + 1 for i in range(s, ret)
               if X.op(i) == 'OR' and X.op(i - 1) == 'SHL' and X.op(i - 2) == 'PUSH1 0x20']
    cdl = [i - 1 for i in range(s, ret) if X.op(i) == 'CALLDATALOAD']
    assert len(jumps) == 2 and len(netends) == 2 and len(cdl) == 2
    assert X.op(s + 82) == 'JUMPDEST' and X.op(s + 236) == 'JUMP' and X.op(s + 245) == 'POP'
    kf1 = int(X.op(jumps[0] - 1).split()[1], 16)
    FIN = cf['FIN']; NB = cf['nblk']
    d = dict(X=X, S=X.pc(s), H=X.pc(s + 82), AJ=s + 236, J=X.pc(s + 237), JI=s + 244, PS=X.pc(s + 245),
             PJ=jumps[1], R2=X.pc(jumps[1] + 1), N1=X.pc(netends[0]), C1=X.pc(cdl[1]), N2=X.pc(netends[1]),
             RET=ret, RETpc=X.pc(ret), KF1=kf1, FIN=FIN, NB=NB, BOUND=FIN + 544 * NB,
             XS={65: 832, 87: 1088}[nn], L={65: 48, 87: 64}[nn], NL={65: 6, 87: 8}[nn])
    assert int(X.op(s + 81).split()[1], 16) == FIN
    assert X.op(cdl[0]) == f'PUSH2 0x{cf["CTOFF"]:04x}' and X.op(cdl[1]) == f'PUSH2 0x{cf["CTOFF"] + 32:04x}'
    assert int(X.op(s + 244 - 3).split()[1], 16) == d['BOUND']
    return d


def gen_finblocks(nn):
    d = fin_cfg(nn); X = d['X']; cf = CFG[nn]
    N = str(N256)
    P = pre(nn)
    Lx = lambda a, b: ', '.join(str(i) for i in range(a, b + 1))     # indices, inclusive
    cx = lambda a, b: sum(X.c(i) for i in range(a, b + 1))
    S, H, J, PS, R2, N1, C1, N2 = (d[k] for k in ('S', 'H', 'J', 'PS', 'R2', 'N1', 'C1', 'N2'))
    FIN, BOUND, KF1 = d['FIN'], d['BOUND'], d['KF1']
    FR = '''  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _'''
    src = header(nn, [f'MlDsaOpt{nn}.Main.S1.Tac', 'MlDsaOpt44.Main.Fin.Proof'],
                 f'# `seg_fin` blocks (ML-DSA-{nn}): zeroing `KS`, the {d["NB"]}-visit absorbing loop over\n'
                 f'`FIN`, the padding block, the {d["L"]}-byte c̃ comparison (two calldata words).')
    src += '''open MlDsaOpt44.Proofs (muK finW frame_wr xor_mod_lit word_lt_lit bswapNet bsw8 bsw16 bsw32)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
'''
    c_init = X.cost(S, H)
    c_abs = cx(X.idx[H], d['AJ'])
    c_back = cx(X.idx[J], d['JI'])
    c_pad = cx(X.idx[PS], d['PJ'])
    if nn == 65:
        tail = (f'if x = 0 then word M {BOUND} else if x = 1 then word M {BOUND + 32} else if x = 2 then rep 31\n'
                '  else if x = 16 then rep (2 ^ 63) else 0')
    else:
        tail = 'if x = 0 then rep 31 else if x = 16 then rep (2 ^ 63) else 0'
    src += f'''
theorem fin_init {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = rep (cpl x 0)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s {S} [flag b] M) (callState s {H} [wd {FIN}, flag b] M') {c_init} := by
{P}  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt{nn}_reach [{X.L(S, H)}] with [word_mstore_disjoint]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> chain_facts
    all_goals (try simp [cpl, complemented])
    all_goals (try norm_num [rep, REP, pack4])
{FR}

theorem fin_abs {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) {{p : Nat}}
    (hp1 : {FIN} ≤ p) (hp2 : p + 544 ≤ {BOUND}) :
    ∃ M', (∀ x, x < 17 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ word M (32 * x + p)) ∧
      FrameExcept M M' [(KS, KS + 544)] ∧
      Reach (callState s {H} [wd p, flag b] M) (callState s {KF1} [wd {J}, wd p, flag b] M') {c_abs} := by
{P}  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt{nn}_reach [{Lx(X.idx[H], d['AJ'])}] with [word_mstore_disjoint]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] <;>
      chain_facts <;> rw [xor_mod_lit (word_lt_lit _ _) (word_lt_lit _ _)]
{FR}

theorem fin_back {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) {{p : Nat}} (hp : 544 + p < {BOUND}) :
    Reach (callState s {J} [wd p, flag b] M) (callState s {H} [wd (544 + p), flag b] M) {c_back} := by
{P}  opt{nn}_reach [{Lx(X.idx[J], d['JI'])}]

theorem fin_last {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) {{p : Nat}} (hp : 544 + p = {BOUND}) :
    Reach (callState s {J} [wd p, flag b] M) (callState s {PS} [wd (544 + p), flag b] M) {c_back} := by
{P}  opt{nn}_reach [{Lx(X.idx[J], d['JI'])}]

/-- What the padding-block code xors into lane `x`. -/
def finTail (M : ByteArray) (x : Nat) : Nat :=
  {tail}

theorem fin_pad {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) (q : Nat) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ finTail M x) ∧
      FrameExcept M M' [(KS, KS + 544)] ∧
      Reach (callState s {PS} [wd q, flag b] M) (callState s {KF1} [wd {R2}, flag b] M') {c_pad} := by
{P}  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt{nn}_reach [{Lx(X.idx[PS], d['PJ'])}] with [word_mstore_disjoint]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, finTail, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add,
      Nat.reduceEqDiff, ite_true, ite_false, ↓reduceIte] <;> chain_facts
    all_goals (try simp only [Nat.xor_zero])
    all_goals (try norm_num only [rep, REP, pack4])
    all_goals (try rw [xor_mod_lit (word_lt_lit _ _) (word_lt_lit _ _)])
    all_goals (try rw [xor_mod_lit (word_lt_lit _ _) (by norm_num)])
{FR}

theorem fin_net {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s {R2} [flag b] M)
      (callState s {N1} (wd (bswapNet (word s.executionEnv.calldata {cf["CTOFF"]})) :: muK b) M)
      {X.cost(R2, N1)} := by
{P}  opt{nn}_reach [{X.L(R2, N1)}] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem ite_land (b : Bool) (P : Prop) [Decidable P] :
    ((if b = true then 1 else 0) &&& (if P then 1 else 0)) = if (b && decide P) = true then 1 else 0 := by
  cases b <;> by_cases h : P <;> simp [h]

theorem ite_land_mod (b : Bool) (P : Prop) [Decidable P] :
    ((if b = true then 1 else 0) &&& (if P then 1 else 0)) % {N} =
      if (b && decide P) = true then 1 else 0 := by
  cases b <;> by_cases h : P <;> simp [h]

/-- The first compare: c̃ lanes `0 … 3` against the first four squeezed lanes. -/
theorem fin_cmp1 {{s : State}} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < {N}) (M : ByteArray) :
    Reach (callState s {N1} (wd Y :: muK b) M)
      (callState s {C1} (muK (b && decide (finW M % {N} = Y))) M) {X.cost(N1, C1)} := by
{P}  opt{nn}_reach [{X.L(N1, C1)}] with [muK, flag, ofNat_land, ite_land, finW]
  rfl

theorem fin_net2 {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s {C1} (muK b) M)
      (callState s {N2} (wd (bswapNet (word s.executionEnv.calldata {cf["CTOFF"] + 32})) :: muK b) M)
      {X.cost(C1, N2)} := by
{P}  opt{nn}_reach [{X.L(C1, N2)}] with [muK, bswapNet, bsw8, bsw16, bsw32]
'''
    M64s = str(M64)
    if nn == 65:
        w2 = f'{M64s} &&& word M 160 ||| ({M64s} &&& word M 128) * 18446744073709551616'
        rhs = 'Y / 340282366920938463463374607431768211456'
        doc = 'c̃ lanes `4, 5` (the top half of the second word) against squeezed lanes `4, 5`'
    else:
        w2 = (f'{M64s} &&& word M 224 |||\n    (({M64s} &&& word M 192) * 18446744073709551616 |||\n'
              f'      (({M64s} &&& word M 160) * 340282366920938463463374607431768211456 |||\n'
              f'        ({M64s} &&& word M 128) * 6277101735386680763835789423207666416102355444464034512896))')
        rhs = 'Y'
        doc = 'c̃ lanes `4 … 7` against squeezed lanes `4 … 7`'
    c_cmp2 = cx(X.idx[N2], d['RET'])
    src += f'''
/-- The word the second compare builds from `KS` ({doc}). -/
def finW2 (M : ByteArray) : Nat :=
  {w2}

theorem finalState_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) (v : Nat) :
    (finalState s pc stk m v).activeWords = s.activeWords := rfl

theorem callState_aw' (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState s pc stk m).activeWords = s.activeWords := rfl

theorem fin_cmp2 {{s : State}} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < {N}) (M : ByteArray) :
    Reach (callState s {N2} (wd Y :: muK b) M)
      (finalState s {d["RETpc"]} [] M (if (b && decide (finW2 M % {N} = {rhs})) = true then 1 else 0))
      {c_cmp2} := by
{P}  have h := reach_block_pot ((hs.ctx0).callState {N2} (wd Y :: muK b) M) (cost := {c_cmp2})
    (t := finalState s {d["RETpc"]} [] M (if (b && decide (finW2 M % {N} = {rhs})) = true then 1 else 0))
    [{Lx(X.idx[N2], d['RET'])}] (by decide +kernel) ?run
  · rw [finalState_aw, callState_aw', Nat.add_sub_cancel] at h
    exact h
  case run =>
    opt{nn}_block [muK, flag, finalState, ofNat_land, ite_land_mod, finW2]
    exact ⟨rfl, rfl⟩

end MlDsaOpt{nn}.Proofs.S1
'''
    tail_cost = c_back + c_pad + X.cost(R2, N1) + X.cost(N1, C1) + X.cost(C1, N2) + c_cmp2
    print(nn, 'fin costs: init', c_init, 'loop', c_abs + c_back, 'tail', tail_cost)
    return src


GENS = {'FinBlocks': gen_finblocks}


def gen_fin(nn):
    d = fin_cfg(nn); X = d['X']; cf = CFG[nn]
    N = str(N256)
    S, H, J, PS, R2 = (d[k] for k in ('S', 'H', 'J', 'PS', 'R2'))
    FIN, BOUND, NB, XS, L, NL = (d[k] for k in ('FIN', 'BOUND', 'NB', 'XS', 'L', 'NL'))
    cx = lambda a, b: sum(X.c(i) for i in range(a, b + 1))
    c_init = X.cost(S, H)
    c_abs = cx(X.idx[H], d['AJ'])
    c_back = cx(X.idx[J], d['JI'])
    c_pad = cx(X.idx[PS], d['PJ'])
    A = f'(by s1_avoids{nn})'
    F2 = 'MlDsa44.Fips202'
    src = header(nn, [f'MlDsaOpt{nn}.Main.S1.FinBlocks', f'MlDsaOpt{nn}.Fn.Keccak'],
                 f'# `seg_fin` (ML-DSA-{nn}): {NB} absorbed blocks of `FIN`, the padding block, the\n'
                 f'{L}-byte c̃ comparison.')
    src += f'''open MlDsaOpt44.Proofs (muK finW absorbPre absorbPre_zero absorbPre_succ absorbPre_size
  laneOf_emptyState laneOf_xorBlock xorBlock_size rep_cpl_xor le64_pad_full le64_pad_last padLane
  padLane_lt absorb_eq pad_size land_rep or4_eq finW_eq pack4_inj ba_beq_eq le64_beyond bswapNet_word
  bswapNet bswapNet_lt le64_shake256 le64_congr le64_lt laneOf_lt byteN byteN_le64 rep_zero shake_size
  byteAt_extract pack4_lt')
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- After `j` blocks: every well-formed `FIN` content `X` has been absorbed `j` times. -/
structure FinInv (m M : ByteArray) (j : Nat) : Prop where
  rc1 : RC1Table M
  fr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)]
  ks : ∀ X : ByteArray, X.size = {XS} → FinAt m X →
    KS1 M (absorbPre 136 ({F2}.pad 136 0x1F X) j)

theorem fin_frame_word {{m M : ByteArray}} (h : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)])
    {{a : Nat}} (ha : FIN ≤ a) (ha' : a + 32 ≤ TOP) : word M a = word m a :=
  FrameExcept.word h (by simp only [avoids_cons, avoids_nil, and_true, KS, KB, KZ, FIN, TOP] at *; omega)

theorem fin_start {{s : State}} (hs : Ctx s) (b : Bool) {{m : ByteArray}} (hrc : RC1Table m) :
    ∃ M, FinInv m M 0 ∧
      Reach (callState s {S} [flag b] m) (callState s {H} [wd {FIN}, flag b] M) {c_init} := by
  obtain ⟨M, f, fr, r⟩ := fin_init hs b m
  refine ⟨M, ⟨RC1Table.frame hrc fr {A}, fr.mono ?_, fun X _ _ x hx => ?_⟩, r⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [KS, KB, KZ]
  · rw [f x hx, absorbPre_zero, laneOf_emptyState]

/-- One absorbing iteration, up to the return of `kf1`. -/
theorem fin_iter {{s : State}} (hs : Ctx s) (b : Bool) {{m M : ByteArray}} (j : Nat) (hj : j < {NB})
    (hI : FinInv m M j) :
    ∃ M', FinInv m M' (j + 1) ∧
      Reach (callState s {H} [wd ({FIN} + 544 * j), flag b] M)
        (callState s {J} [wd ({FIN} + 544 * j), flag b] M') ({c_abs} + Gas.kf1) := by
  obtain ⟨M1, f1, fr1, r1⟩ := fin_abs hs b M (p := {FIN} + 544 * j) (by omega) (by omega)
  obtain ⟨M2, hk2, hf2, hc2⟩ := kf1_call hs (ret := {J}) (tail := [wd ({FIN} + 544 * j), flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M1
    (RC1Table.frame hI.rc1 fr1 {A})
  rw [call_iff] at hc2
  have hfr : FrameExcept m M2 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] := by
    refine ((hI.fr.trans fr1).trans hf2).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, KZ]
  refine ⟨M2, ⟨RC1Table.frame (RC1Table.frame hI.rc1 fr1 {A}) hf2 {A}, hfr, fun X hX hF => ?_⟩,
    (r1.trans hc2).mono (by omega)⟩
  set St := absorbPre 136 ({F2}.pad 136 0x1F X) j
  set S' := {F2}.xorBlock 136 ({F2}.pad 136 0x1F X) (j * 136) St
  have hS' : S'.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M1 S' := fun x hx => by
    rw [laneOf_xorBlock _ _ (absorbPre_size _ _ j) (by norm_num) x]
    by_cases h : x < 17
    · rw [f1 x h, hI.ks X hX hF x hx, if_pos (by omega),
        fin_frame_word hI.fr (by unfold FIN; omega) (by unfold TOP; omega),
        show 32 * x + ({FIN} + 544 * j) = FIN + 32 * (17 * j + x) by unfold FIN; ring,
        hF _ (by omega), rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _),
        le64_pad_full _ (by rw [hX]; omega), show 8 * (17 * j + x) = j * 136 + 8 * x by ring]
    · rw [if_neg (by omega), ← hI.ks X hX hF x hx]
      exact FrameExcept.word fr1 (by simp only [avoids_cons, avoids_nil, and_true, KS]; omega)
  have := hk2 S' hS' hK
  rwa [← absorbPre_succ] at this

theorem fin_loop {{s : State}} (hs : Ctx s) (b : Bool) {{m M0 : ByteArray}} (hI0 : FinInv m M0 0) :
    ∀ j, j ≤ {NB - 1} → ∃ M, FinInv m M j ∧
      Reach (callState s {H} [wd {FIN}, flag b] M0)
        (callState s {H} [wd ({FIN} + 544 * j), flag b] M) (j * ({c_abs + c_back} + Gas.kf1))
  | 0, _ => ⟨M0, hI0, by simpa using Reach.refl _⟩
  | j + 1, hj => by
    obtain ⟨M, hI, hR⟩ := fin_loop hs b hI0 j (by omega)
    obtain ⟨M', hI', hR'⟩ := fin_iter hs b j (by omega) hI
    have hb := fin_back hs b M' (p := {FIN} + 544 * j) (by omega)
    rw [show 544 + ({FIN} + 544 * j) = {FIN} + 544 * (j + 1) by ring] at hb
    exact ⟨M', hI', ((hR.trans hR').trans hb).mono (by rw [Nat.succ_mul]; omega)⟩
'''
    if nn == 65:
        src += f'''
/-- The last block of an {XS}-byte input: what `fin_pad` xors in. -/
theorem finTail_eq {{m M : ByteArray}} (hfr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)])
    {{X : ByteArray}} (hX : X.size = {XS}) (hF : FinAt m X) {{x : Nat}} (hx : x < 25) :
    finTail M x = rep (if x < 17 then le64 ({F2}.pad 136 0x1F X) (816 + 8 * x) else 0) := by
  have hl : ∀ x, x < 17 → le64 ({F2}.pad 136 0x1F X) (816 + 8 * x) =
      le64 X (816 + 8 * x) ^^^ padLane 16 x := fun x hx => by
    have := le64_pad_last X hx
    rwa [hX] at this
  have w0 : word M {BOUND} = rep (le64 X 816) := by
    rw [fin_frame_word hfr (by unfold FIN; omega) (by unfold TOP; omega),
      show ({BOUND} : Nat) = FIN + 32 * 102 by rfl, hF 102 (by omega)]
  have w1 : word M {BOUND + 32} = rep (le64 X 824) := by
    rw [fin_frame_word hfr (by unfold FIN; omega) (by unfold TOP; omega),
      show ({BOUND + 32} : Nat) = FIN + 32 * 103 by rfl, hF 103 (by omega)]
  have z : ∀ x, 2 ≤ x → le64 X (816 + 8 * x) = 0 := fun x hx => le64_beyond X (by omega)
  unfold finTail
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 16 ∨ (3 ≤ x ∧ x < 16) ∨ 17 ≤ x) with h | h | h | h | h | h
  · subst h
    rw [if_pos rfl, if_pos (by norm_num), hl 0 (by norm_num), w0]; unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_pos rfl, if_pos (by norm_num), hl 1 (by norm_num), w1]
    unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, if_pos (by norm_num), hl 2 (by norm_num),
      z 2 (by norm_num)]
    unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl,
      if_pos (by norm_num), hl 16 (by norm_num), z 16 (by norm_num)]
    unfold padLane; norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      hl x (by omega), z x (by omega)]
    unfold padLane
    rw [if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero, rep_zero]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      rep_zero]
'''
        LB = 816
    else:
        src += f'''
/-- The last block of a {XS}-byte input (pure padding): what `fin_pad` xors in. -/
theorem finTail_eq {{m M : ByteArray}} (hfr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)])
    {{X : ByteArray}} (hX : X.size = {XS}) (hF : FinAt m X) {{x : Nat}} (hx : x < 25) :
    finTail M x = rep (if x < 17 then le64 ({F2}.pad 136 0x1F X) ({XS} + 8 * x) else 0) := by
  have hl : ∀ x, x < 17 → le64 ({F2}.pad 136 0x1F X) ({XS} + 8 * x) =
      le64 X ({XS} + 8 * x) ^^^ padLane 0 x := fun x hx => by
    have := le64_pad_last X hx
    rwa [hX] at this
  have z : ∀ x, le64 X ({XS} + 8 * x) = 0 := fun x => le64_beyond X (by omega)
  unfold finTail
  rcases (by omega : x = 0 ∨ x = 16 ∨ (x < 17 ∧ x ≠ 0 ∧ x ≠ 16) ∨ 17 ≤ x) with h | h | h | h
  · subst h
    rw [if_pos rfl, if_pos (by norm_num), hl 0 (by norm_num), z 0]; unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_pos rfl, if_pos (by norm_num), hl 16 (by norm_num), z 16]
    unfold padLane; norm_num
  · rw [if_neg h.2.1, if_neg h.2.2, if_pos h.1, hl x h.1, z x]
    unfold padLane
    rw [if_neg (by omega), if_neg h.2.2, Nat.xor_zero, Nat.xor_zero, rep_zero]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), rep_zero]
'''
        LB = XS
    src += f'''
/-- The last block, the final permutation. -/
theorem fin_last_block {{s : State}} (hs : Ctx s) (b : Bool) {{m M : ByteArray}} (hI : FinInv m M {NB}) :
    ∃ M', RC1Table M' ∧
      (∀ X : ByteArray, X.size = {XS} → FinAt m X →
        KS1 M' ({F2}.absorb 136 ({F2}.pad 136 0x1F X))) ∧
      Reach (callState s {PS} [wd {BOUND}, flag b] M) (callState s {R2} [flag b] M') ({c_pad} + Gas.kf1) := by
  obtain ⟨M3, f3, fr3, r3⟩ := fin_pad hs b M {BOUND}
  obtain ⟨M4, hk4, hf4, hc4⟩ := kf1_call hs (ret := {R2}) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M3
    (RC1Table.frame hI.rc1 fr3 {A})
  rw [call_iff] at hc4
  refine ⟨M4, RC1Table.frame (RC1Table.frame hI.rc1 fr3 {A}) hf4 {A}, fun X hX hF => ?_,
    (r3.trans hc4).mono (by omega)⟩
  set St := absorbPre 136 ({F2}.pad 136 0x1F X) {NB}
  set S'' := {F2}.xorBlock 136 ({F2}.pad 136 0x1F X) ({NB} * 136) St
  have hS'' : S''.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M3 S'' := fun x hx => by
    have hpl : padLane 16 x < 2 ^ 64 := padLane_lt _ _
    rw [f3 x hx, hI.ks X hX hF x hx, finTail_eq hI.fr hX hF hx,
      laneOf_xorBlock _ _ (absorbPre_size _ _ {NB}) (by norm_num) x]
    by_cases h : x < 17
    · rw [if_pos h, if_pos (by omega), rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _)]
    · rw [if_neg h, if_neg (by omega), rep_zero, Nat.xor_zero]
  have hP : ({F2}.pad 136 0x1F X).size = {NB + 1} * 136 := by rw [pad_size _ _ (by norm_num), hX]
  rw [absorb_eq _ _ {NB + 1} (by norm_num) hP, absorbPre_succ]
  exact hk4 S'' hS'' hK

/-! ## The comparison -/

theorem s1_eq_of_le64 {{A B : ByteArray}} {{n : Nat}} (hA : A.size = 8 * n) (hB : B.size = 8 * n)
    (h : ∀ k, k < n → le64 A (8 * k) = le64 B (8 * k)) : A = B := by
  have hb : ∀ i, i < 8 * n → byteAt A i = byteAt B i := fun i hi => by
    have := congrArg (byteN · (i % 8)) (h (i / 8) (by omega))
    simp only [byteN_le64 _ _ (Nat.mod_lt i (by omega : 8 > 0))] at this
    rwa [show 8 * (i / 8) + i % 8 = i by omega] at this
  apply ByteArray.ext
  apply Array.ext (by change A.size = B.size; omega)
  intro i h1 h2
  have := hb i (by change i < A.size at h1; omega)
  unfold byteAt at this
  rw [dif_pos (by change i < A.size at h1; exact h1), dif_pos (by change i < B.size at h2; exact h2)] at this
  exact UInt8.toNat_inj.mp this

theorem s1_ctOf_size {{cd : ByteArray}} (hcd : HDR ≤ cd.size) : (ctOf cd).size = {L} := by
  unfold ctOf Z0 CTOFF; unfold HDR at hcd; simp [ByteArray.size_extract]; omega

theorem s1_le64_ctOf {{cd : ByteArray}} (hcd : HDR ≤ cd.size) {{k : Nat}} (hk : k < {NL}) :
    le64 (ctOf cd) (8 * k) = le64 cd (CTOFF + 8 * k) :=
  le64_congr fun i hi => by
    unfold ctOf
    rw [byteAt_extract _ _ _ _ (by unfold HDR Z0 at *; omega), if_pos (by unfold Z0 CTOFF; omega),
      Nat.add_assoc]

theorem s1_le64_H (X : ByteArray) {{k : Nat}} (hk : k < {NL}) :
    le64 (Fips204.H X {L}) (8 * k) = laneOf ({F2}.absorb 136 ({F2}.pad 136 0x1F X)) k := by
  have := le64_shake256 X (n := {L}) (j := 0) (x := k) (by omega) (by omega)
  simpa [Fips204.H, {F2}.shake256] using this

/-- The commitment check, lane by lane. -/
theorem s1_cmp (cd X : ByteArray) (hcd : HDR ≤ cd.size) :
    (ctOf cd == Fips204.H X {L}) = true ↔ ∀ k, k < {NL} →
      laneOf ({F2}.absorb 136 ({F2}.pad 136 0x1F X)) k = le64 cd (CTOFF + 8 * k) := by
  rw [ba_beq_eq, decide_eq_true_iff]
  constructor
  · intro h k hk
    rw [← s1_le64_H X hk, ← h, s1_le64_ctOf hcd hk]
  · intro h
    refine s1_eq_of_le64 (A := ctOf cd) (B := Fips204.H X {L}) (n := {NL}) (s1_ctOf_size hcd)
      (shake_size _ (by norm_num)) fun k hk => ?_
    rw [s1_le64_ctOf hcd hk, s1_le64_H X hk, h k hk]
'''
    if nn == 65:
        src += f'''
theorem s1_or_mul {{a b : Nat}} (ha : a < 18446744073709551616) :
    (a ||| b * 18446744073709551616) = a + b * 18446744073709551616 := by
  rw [show (18446744073709551616 : Nat) = 2 ^ 64 by norm_num, ← Nat.shiftLeft_eq, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using ha), Nat.add_comm]

theorem s1_lohi {{a b c d : Nat}} (ha : a < 18446744073709551616) (hc : c < 18446744073709551616) :
    a + b * 18446744073709551616 = c + d * 18446744073709551616 ↔ a = c ∧ b = d := by omega

theorem s1_hi2 (v : Nat → Nat) (h : ∀ k, k < 4 → v k < 2 ^ 64) :
    pack4 v / 340282366920938463463374607431768211456 = v 2 + v 3 * 18446744073709551616 := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  unfold pack4; norm_num at h0 h1 ⊢; omega

/-- The second compared word: squeezed lanes `4, 5`. -/
theorem finW2_eq {{M : ByteArray}} {{S : {F2}.SpongeState}} (hK : KS1 M S) :
    finW2 M % {N} = laneOf S 5 + laneOf S 4 * 18446744073709551616 := by
  have k4 := hK 4 (by omega); have k5 := hK 5 (by omega)
  simp only [KS, cpl, complemented] at k4 k5
  norm_num at k4 k5
  unfold finW2
  rw [k4, k5]
  simp only [land_rep (laneOf_lt S _)]
  have h4 := laneOf_lt S 4; have h5 := laneOf_lt S 5
  rw [s1_or_mul (by simpa using h5)]
  exact Nat.mod_eq_of_lt (by norm_num at h4 h5 ⊢; omega)

/-- The two compare bits are the lane equalities `0 … 5`. -/
theorem s1_flags {{M : ByteArray}} {{S : {F2}.SpongeState}} (hK : KS1 M S) (cd : ByteArray) :
    (decide (finW M % {N} = bswapNet (word cd CTOFF)) &&
      decide (finW2 M % {N} = bswapNet (word cd (CTOFF + 32)) / 340282366920938463463374607431768211456)) =
      true ↔ ∀ k, k < 6 → laneOf S k = le64 cd (CTOFF + 8 * k) := by
  rw [finW_eq hK, finW2_eq hK, bswapNet_word, bswapNet_word,
    s1_hi2 _ (fun _ _ => le64_lt _ _)]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [pack4_inj (fun _ _ => laneOf_lt _ _) (fun _ _ => le64_lt _ _)]
  have l4 := laneOf_lt S 4; have l5 := laneOf_lt S 5
  have c1 := le64_lt cd (CTOFF + 32 + 8 * (3 - 2))
  have c0 := le64_lt cd (CTOFF + 32 + 8 * (3 - 3))
  norm_num at l4 l5 c0 c1
  constructor
  · rintro ⟨h1, h2⟩ k hk
    have h2' := (s1_lohi l5 (by simpa using c1)).mp h2
    interval_cases k
    · simpa using h1 3 (by omega)
    · simpa using h1 2 (by omega)
    · simpa using h1 1 (by omega)
    · simpa using h1 0 (by omega)
    · simpa [Nat.add_assoc] using h2'.2
    · simpa [Nat.add_assoc] using h2'.1
  · intro h
    refine ⟨fun k hk => h (3 - k) (by omega), (s1_lohi l5 (by simpa using c1)).mpr ⟨?_, ?_⟩⟩
    · simpa [Nat.add_assoc] using h 5 (by omega)
    · simpa [Nat.add_assoc] using h 4 (by omega)
'''
        rhs2 = 'bswapNet (word s.executionEnv.calldata (CTOFF + 32)) / 340282366920938463463374607431768211456'
    else:
        src += f'''
/-- The second compared word: squeezed lanes `4 … 7`. -/
theorem finW2_eq {{M : ByteArray}} {{S : {F2}.SpongeState}} (hK : KS1 M S) :
    finW2 M % {N} = pack4 fun k => laneOf S (4 + (3 - k)) := by
  have k4 := hK 4 (by omega); have k5 := hK 5 (by omega)
  have k6 := hK 6 (by omega); have k7 := hK 7 (by omega)
  simp only [KS, cpl, complemented] at k4 k5 k6 k7
  norm_num at k4 k5 k6 k7
  unfold finW2
  rw [k4, k5, k6, k7]
  simp only [land_rep (laneOf_lt S _)]
  have := or4_eq (fun k => laneOf S (4 + k)) (fun _ _ => laneOf_lt _ _)
  simp only [Nat.reduceAdd] at this
  rw [this]
  exact Nat.mod_eq_of_lt (by
    have := pack4_lt' (v := fun k => laneOf S (4 + (3 - k))) (fun _ _ => laneOf_lt _ _)
    norm_num at this ⊢; exact this)

/-- The two compare bits are the lane equalities `0 … 7`. -/
theorem s1_flags {{M : ByteArray}} {{S : {F2}.SpongeState}} (hK : KS1 M S) (cd : ByteArray) :
    (decide (finW M % {N} = bswapNet (word cd CTOFF)) &&
      decide (finW2 M % {N} = bswapNet (word cd (CTOFF + 32)))) =
      true ↔ ∀ k, k < 8 → laneOf S k = le64 cd (CTOFF + 8 * k) := by
  rw [finW_eq hK, finW2_eq hK, bswapNet_word, bswapNet_word]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [pack4_inj (fun _ _ => laneOf_lt _ _) (fun _ _ => le64_lt _ _),
    pack4_inj (fun _ _ => laneOf_lt _ _) (fun _ _ => le64_lt _ _)]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    interval_cases k
    · simpa using h1 3 (by omega)
    · simpa using h1 2 (by omega)
    · simpa using h1 1 (by omega)
    · simpa using h1 0 (by omega)
    · simpa [Nat.add_assoc] using h2 3 (by omega)
    · simpa [Nat.add_assoc] using h2 2 (by omega)
    · simpa [Nat.add_assoc] using h2 1 (by omega)
    · simpa [Nat.add_assoc] using h2 0 (by omega)
  · intro h
    refine ⟨fun k hk => h (3 - k) (by omega), fun k hk => ?_⟩
    rw [show CTOFF + 32 + 8 * (3 - k) = CTOFF + 8 * (4 + (3 - k)) by omega]
    exact h _ (by omega)
'''
        rhs2 = 'bswapNet (word s.executionEnv.calldata (CTOFF + 32))'
    src += f'''
theorem seg_fin_proof {{s : State}} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {{m : ByteArray}} (hrc : RC1Table m) (b : Bool) :
    ∃ E : Bool, ∃ pc stk m',
      (∀ X : ByteArray, X.size = {XS} → FinAt m X →
        E = (ctOf s.executionEnv.calldata == Fips204.H X {L})) ∧
      Reach (callState s {S} [flag b] m)
        (finalState s pc stk m' (if (b && E) = true then 1 else 0)) Gas.pFin := by
  obtain ⟨M0, hI0, r0⟩ := fin_start hs b hrc
  obtain ⟨M5, hI5, r1⟩ := fin_loop hs b hI0 {NB - 1} le_rfl
  obtain ⟨M6, hI6, r2⟩ := fin_iter hs b {NB - 1} (by omega) hI5
  have r3 := fin_last hs b M6 (p := {FIN} + 544 * {NB - 1}) (by norm_num)
  obtain ⟨M7, hrc7, hK7, r4⟩ := fin_last_block hs b hI6
  have r5 := fin_net hs b M7
  have r6 := fin_cmp1 hs b _ (bswapNet_lt (word s.executionEnv.calldata {cf["CTOFF"]})) M7
  have r7 := fin_net2 hs (b && decide (finW M7 % {N} =
    bswapNet (word s.executionEnv.calldata {cf["CTOFF"]}))) M7
  have r8 := fin_cmp2 hs (b && decide (finW M7 % {N} =
    bswapNet (word s.executionEnv.calldata {cf["CTOFF"]}))) _
    (bswapNet_lt (word s.executionEnv.calldata {cf["CTOFF"] + 32})) M7
  refine ⟨decide (finW M7 % {N} = bswapNet (word s.executionEnv.calldata CTOFF)) &&
      decide (finW2 M7 % {N} = {rhs2}),
    {d["RETpc"]}, [], M7, fun X hX hF => ?_, ?_⟩
  · exact Bool.eq_iff_iff.mpr ((s1_flags (hK7 X hX hF) _).trans (s1_cmp _ X hcd).symm)
  · rw [← Bool.and_assoc]
    exact ((((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).mono
      (by unfold Gas.pFin; omega)

end MlDsaOpt{nn}.Proofs.S1
'''
    return src


GENS['Fin'] = gen_fin
