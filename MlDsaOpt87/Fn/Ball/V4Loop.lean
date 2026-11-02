import MlDsaOpt87.Fn.Ball.V4Scan
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (v4, ML-DSA-87): the scan over the stream and the contract body

`sib_loop` recurses over the stream positions `p = 8 … 272` with the potential
`pot p i` (rejected bytes still ahead, `353` per coefficient still to place, the
failure exit, and the second block's squeeze while `p ≤ 136`). At a lane start the
head's visit (`b_nok`, or `sq_step` at `p = 136`) precedes the byte test; `KS` holds the
current block (`KSU`). `sib_main` is the contract body: the absorption prologue
(`V4Prologue`), the first `kf1`, the scan. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

namespace Ball4

open MlDsaOptCommon.BallScan (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
  ballFold_inv sampleInBallOf_eq)

/-- Cost potential at stream position `p` with index `i`. -/
def pot (p i : Nat) : Nat := rs p + 353 * (256 - i) + 43 + (if p ≤ 136 then sqX else 0)

theorem rlOf_jd (r : Nat) (hr : r < 8) :
    Decode.isValidJumpDest MlDsaOpt87.optBytecode (rlOf r) = true := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [rlOf, Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit]

theorem rs_ge (p : Nat) (hp : p < 272) : rc (p % 8) ≤ rs p := by
  rw [rs_succ hp]; omega

/-- The block index of the `KS` contents after the visit of `p`. -/
theorem blk_idx {p : Nat} (hp : p < 272) (h136 : p ≠ 136) :
    (if p ≤ 136 then 1 else 2) = p / 136 + 1 := by
  split <;> omega

theorem blk_idx_succ {p : Nat} (hp : p < 272) :
    (if p + 1 ≤ 136 then 1 else 2) = p / 136 + 1 := by
  split <;> omega

/-- Potential steps (stated with only the bounds they need). -/
theorem pot_rej {p i : Nat} (hp : p < 272) (h : rs p = rc (p % 8) + rs (p + 1)) :
    ((if p % 8 = 0 then 48 else 0) + if p = 136 then sqX else 0) + tc (p % 8) + pot (p + 1) i ≤
      pot p i := by
  unfold pot tc rc at *; split_ifs at * <;> omega

theorem pot_acc {p i : Nat} (hp : p < 272) (hi : i < 256) (h : rs p = rc (p % 8) + rs (p + 1)) :
    ((if p % 8 = 0 then 48 else 0) + if p = 136 then sqX else 0) + acost (p % 8) + 336 +
        (if p % 8 = 7 then 22 else 0) + pot (p + 1) (i + 1) ≤ pot p i := by
  unfold pot acost rc at *; split_ifs at * <;> omega

theorem pot_last {p i : Nat} (hp : p < 272) (hi : i + 1 = 256) (h : rc (p % 8) ≤ rs p) :
    ((if p % 8 = 0 then 48 else 0) + if p = 136 then sqX else 0) + acost (p % 8) + 350 ≤ pot p i := by
  unfold pot acost rc at *; split_ifs at * <;> omega

section
variable {s : State} {ret : Nat} {tail : List UInt256}

/- Keep `KSU` folded while elaborating the recursion (see the v3 `sib_loop`). -/
attribute [local irreducible] KSU

set_option maxHeartbeats 1000000 in
theorem sib_loop (hs : Ctx s) (hr : RetOK Stack.sib ret tail) (htail : tail.length ≤ 960)
    (hsized : 2897 ≤ s.activeWords.toNat) {cd : ByteArray} (hcd : Z0 ≤ cd.size)
    (m : ByteArray) (hrc : RC1Table m) :
    ∀ n p z M, n = 272 - p → 8 ≤ p → p ≤ 272 → (ballFold P (cStream cd) (p - 8)).2 < 256 →
      SInv m M (ballFold P (cStream cd) (p - 8)).1 (ballFold P (cStream cd) (p - 8)).2 →
      KSU M (permN (if p ≤ 136 then 1 else 2) (S0 cd)) →
      ∃ M' k', k' ≤ 264 ∧
        SInv m M' (ballFold P (cStream cd) k').1 (ballFold P (cStream cd) k').2 ∧
        ballFold P (cStream cd) 264 = ballFold P (cStream cd) k' ∧
        Reach (posSt s ret tail (cStream cd) p (ballFold P (cStream cd) (p - 8)).2 z M)
          (callState s ret (wd (if (ballFold P (cStream cd) 264).2 < 256 then 0 else 1) :: tail) M')
          (pot p (ballFold P (cStream cd) (p - 8)).2)
  | 0, p, z, M, hn, hp8, hp, hlt, hinv, _ => by
    have hp272 : p = 272 := by omega
    subst hp272
    refine ⟨M, 264, le_rfl, hinv, rfl, ?_⟩
    rw [if_pos hlt]
    unfold posSt
    rw [if_pos (by norm_num)]
    exact (b_fail hs htail hsized M hr.jumpdest hr.small _ _).mono (by unfold pot; omega)
  | n + 1, p, z, M, hn, hp8, hp, hlt, hinv, hK => by
    have hp272 : p < 272 := by omega
    obtain ⟨hsz, hi1, hi2, -⟩ := ballFold_inv P (cStream cd) (p - 8)
    simp only [tau_eq] at hi1
    have hhigh := ballFold_high (cStream cd) (p - 8)
    have hsucc := ballFold_succ P (cStream cd) (p - 8)
    rw [show 8 + (p - 8) = p by omega, show p - 8 + 1 = p + 1 - 8 by omega] at hsucc
    rcases hF : ballFold P (cStream cd) (p - 8) with ⟨c, i⟩
    rw [hF] at hsz hi1 hi2 hhigh hsucc hlt hinv
    simp only at hsz hi1 hi2 hhigh hlt hinv ⊢
    -- the head's visit (and the second block at `p = 136`)
    have hstep0 : ∃ M0, SInv m M0 c i ∧ KSU M0 (permN (p / 136 + 1) (S0 cd)) ∧
        Reach (posSt s ret tail (cStream cd) p i z M) (tstSt s ret tail (cStream cd) p i z M0)
          ((if p % 8 = 0 then 48 else 0) + if p = 136 then sqX else 0) := by
      by_cases h136 : p = 136
      · subst h136
        rw [if_pos (by norm_num)] at hK
        obtain ⟨M1, hK1, hf1, hr1⟩ := sq_step hs hr htail (rc1_of_frame hrc hinv.frame) hK i
          (sgw (cStream cd) i)
        refine ⟨M1, sinv_frameKS hinv hi2 hf1, hK1, ?_⟩
        unfold posSt tstSt
        rw [if_pos (by norm_num), if_pos (by norm_num)]
        exact hr1.mono (by norm_num)
      · rw [blk_idx hp272 h136] at hK
        refine ⟨M, hinv, hK, ?_⟩
        rw [if_neg h136]
        unfold posSt tstSt
        by_cases h8 : p % 8 = 0
        · rw [if_pos h8, if_pos h8, if_pos h8]
          exact (b_nok hs htail hsized M (4 * p) i _ (by omega) (by omega)).mono (by omega)
        · rw [if_neg h8, if_neg h8, if_neg h8]
          exact Reach.refl _
    obtain ⟨M0, hinv0, hK0, hr0⟩ := hstep0
    have hw : p % 8 = 0 → word M0 (4 * p % 544) = rep (le64 (cStream cd) p) := fun h8 =>
      ksu_stream_lane hcd hp272 h8 hK0
    have hrs := rs_succ hp272
    by_cases hacc : (cStream cd)[p]!.toNat ≤ i
    · -- accept
      have hst : ballFold P (cStream cd) (p + 1 - 8) =
          (ballSet P (cStream cd) c i (cStream cd)[p]!.toNat, i + 1) := by
        rw [hsucc]; unfold ballStep; rw [if_pos ⟨hlt, hacc⟩]
      have hA := byte_acc (ret := ret) (z := z) hs htail hsized (cStream cd) M0 hp272 hw hacc hlt
      obtain ⟨M', hK', hinv', hmid, hend⟩ := acc_chain (ret := ret) (rl := rlOf (p % 8))
        (w := rep (le64 (cStream cd) (p - p % 8))) (o := 4 * (p - p % 8)) hs htail hsized
        hr.jumpdest hr.small (cStream cd) hinv0 hsz hi1 hlt hacc hhigh
        (rlOf_jd _ (Nat.mod_lt _ (by norm_num))) (by simp only [rlOf]; omega)
      have hinv'' : SInv m M' (ballFold P (cStream cd) (p + 1 - 8)).1
          (ballFold P (cStream cd) (p + 1 - 8)).2 := by
        rw [hst]; exact hinv'
      by_cases hlast : i + 1 < 256
      · have hKn : KSU M' (permN (if p + 1 ≤ 136 then 1 else 2) (S0 cd)) := by
          rw [blk_idx_succ hp272]; exact hK' _ hK0
        obtain ⟨M'', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr htail hsized hcd m hrc n
          (p + 1) (rlOf (p % 8)) M' (by omega) (by omega) (by omega) (by rw [hst]; exact hlast)
          hinv'' hKn
        rw [hst] at hreach
        refine ⟨M'', k', hk', hinvF, hfold, ?_⟩
        have hB := acc_back (ret := ret) (i := i) hs htail hsized (cStream cd) M' hp272
        exact ((hr0.trans (hA.trans ((hmid hlast).trans (hB.trans hreach))))).mono
          (by have := pot_acc (i := i) hp272 hlt hrs; simp only; omega)
      · have hfold : ballFold P (cStream cd) 264 = ballFold P (cStream cd) (p + 1 - 8) := by
          have := ballFold_stop (cStream cd) (p + 1 - 8) (by rw [hst]; simp only; omega)
            (264 - (p + 1 - 8))
          rwa [show p + 1 - 8 + (264 - (p + 1 - 8)) = 264 by omega] at this
        refine ⟨M', p + 1 - 8, by omega, hinv'', hfold, ?_⟩
        rw [hfold, hst, if_neg (by simp only; omega)]
        have hi255 : i + 1 = 256 := by omega
        have hpl := pot_last hp272 hi255 (rs_ge p hp272)
        have hfin := hr0.trans (hA.trans (hend hi255))
        refine hfin.mono ?_
        rw [← Nat.add_assoc]
        exact hpl
    · -- reject
      have hst : ballFold P (cStream cd) (p + 1 - 8) = (c, i) := by
        rw [hsucc]; unfold ballStep; rw [if_neg (fun h => hacc h.2)]
      have hR := byte_rej (ret := ret) (z := z) hs htail hsized (cStream cd) M0 hp272 hw
        (by omega) hlt
      have hKn : KSU M0 (permN (if p + 1 ≤ 136 then 1 else 2) (S0 cd)) := by
        rw [blk_idx_succ hp272]; exact hK0
      obtain ⟨M', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr htail hsized hcd m hrc n
        (p + 1) (cStream cd)[p]!.toNat M0 (by omega) (by omega) (by omega) (by rw [hst]; exact hlt)
        (by rw [hst]; exact hinv0) hKn
      rw [hst] at hreach
      refine ⟨M', k', hk', hinvF, hfold, ?_⟩
      exact (hr0.trans (hR.trans hreach)).mono (by have := pot_rej (i := i) hp272 hrs; simp only; omega)

end

end Ball4

open Ball4 MlDsaOptCommon.BallScan in
/-- The `sib` contract body (`sib_call`). -/
theorem sib_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (hrc : RC1Table m)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hz : SibFresh m) :
    ∃ m', (∀ c, cOf s.executionEnv.calldata = some c → CRep m' c) ∧
      (∀ i, i < P.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (CW, CW + 8192), (BASES, BASES + 2048),
        (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (okC s.executionEnv.calldata)] m' Gas.sib := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.sib, Stack.kf1, Stack.leaf] at this; omega
  have hsized : 2897 ≤ s.activeWords.toNat := hs.sized
  have hcd' : Z0 ≤ s.executionEnv.calldata.size := by unfold Z0; unfold HDR at hcd; omega
  -- the absorption prologue
  obtain ⟨M1, h1, f1, r1⟩ := sib_zero hs (ret := ret) htail m
  obtain ⟨M2, h2, f2, r2⟩ := sib_absW0 hs (ret := ret) htail M1
  obtain ⟨M3, h3, f3, r3⟩ := sib_absW1 hs (ret := ret) htail M2
  obtain ⟨M4, h4, f4, r4⟩ := sib_pad hs (ret := ret) htail M3
  have hK4 : KS1 M4 (S0 s.executionEnv.calldata) := by
    intro x hx
    rw [h4 x hx, h3 x hx, h2 x hx, h1 x hx, Ball.laneOf_ctSeed hcd' hx]
    split_ifs <;> first
      | (exfalso; omega)
      | rfl
      | (rw [MlDsaOpt87.Proofs.Ball4.r4_rep_cpl_xor _ (by norm_num) (by first | with_reducible exact le64_lt _ _ | norm_num),
          Nat.zero_xor])
  have hav : ∀ a, a < 24 → Avoids [(KS, KS + 800)] (RC1 + 32 * a) (RC1 + 32 * a + 32) := fun a ha => by
    simp only [avoids_cons, avoids_nil, and_true, KS, RC1]; omega
  have hrc4 : RC1Table M4 := fun a ha => by
    rw [f4.word (hav a ha), f3.word (hav a ha), f2.word (hav a ha), f1.word (hav a ha)]
    exact hrc a ha
  obtain ⟨M5, h5, f5, c5⟩ := kf1_call hs (ret := 8696) (tail := [wd ret] ++ tail)
    (hr.callee (by simp [Stack.sib, Stack.kf1, Stack.leaf]) (by simp only [isValidJumpDest_lit])
      (by norm_num)) M4 hrc4
  rw [call_iff] at c5
  have hK5 : KS1 M5 (permN 1 (S0 s.executionEnv.calldata)) :=
    h5 _ (MlDsaOpt44.Proofs.seedState_size _ _) hK4
  obtain ⟨M6, h6, f6, r6⟩ := sib_post hs (ret := ret) htail M5
  have hK6 : KSU M6 (permN 1 (S0 s.executionEnv.calldata)) := ksu_of_flip hK5 h6
  have hsg : 18446744073709551615 &&& word M5 0 = sgw (cStream s.executionEnv.calldata) 196 := by
    have k0 := hK5 0 (by omega)
    simp only [KS, Nat.mul_zero, Nat.add_zero] at k0
    rw [k0, show cpl 0 (laneOf (permN 1 (S0 s.executionEnv.calldata)) 0) =
      laneOf (permN 1 (S0 s.executionEnv.calldata)) 0 by unfold cpl; simp [complemented],
      land_rep (MlDsaOpt44.Proofs.laneOf_lt _ _), sgw, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    exact (Ball.le64_cStream hcd' (j := 0) (x := 0) (by omega) (by omega)).symm
  rw [hsg] at r6
  have hfr6 : FrameExcept m M6 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] := by
    refine (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> simp
  -- the scan
  have h0 : SInv m M6 (ballFold P (cStream s.executionEnv.calldata) (8 - 8)).1
      (ballFold P (cStream s.executionEnv.calldata) (8 - 8)).2 := by
    rw [show 8 - 8 = 0 from rfl, MlDsaOptCommon.BallScan.ballFold_zero P]
    exact sinv_frameKS (sinv_init m hz) (by omega) hfr6
  obtain ⟨M', k', hk', hinv, hfold, hreach⟩ := sib_loop hs hr htail hsized hcd' m hrc 264 8 0 M6
    rfl (by omega) (by omega)
    (by rw [show 8 - 8 = 0 from rfl, MlDsaOptCommon.BallScan.ballFold_zero P]; decide) h0
    (by rw [if_pos (by norm_num)]; exact hK6)
  rw [show 8 - 8 = 0 from rfl, MlDsaOptCommon.BallScan.ballFold_zero P] at hreach
  refine ⟨M', fun c hc => ?_, fun i hi => bases_le hinv i (by simpa [tau_eq] using hi),
    hinv.frame, ?_⟩
  · have hc' : Fips204.sampleInBallOf P (cStream s.executionEnv.calldata) = some c := hc
    rw [MlDsaOptCommon.BallScan.sampleInBallOf_eq P] at hc'
    split at hc'
    · exact absurd hc' (by simp)
    · rename_i hge
      simp only [Option.some.injEq] at hc'
      subst hc'
      rw [hfold] at hge ⊢
      have hi2 := (MlDsaOptCommon.BallScan.ballFold_inv P (cStream s.executionEnv.calldata) k').2.2.1
      have h256 : (ballFold P (cStream s.executionEnv.calldata) k').2 = 256 := by omega
      rw [h256] at hinv
      exact crep_of_sinv hinv
  · rw [call_iff, Entry.sib]
    have hflag : flag (okC s.executionEnv.calldata) =
        wd (if (ballFold P (cStream s.executionEnv.calldata) 264).2 < 256 then 0 else 1) := by
      show flag (Fips204.sampleInBallOf P (cStream s.executionEnv.calldata)).isSome = _
      rw [MlDsaOptCommon.BallScan.sampleInBallOf_eq P]
      by_cases h : (ballFold P (cStream s.executionEnv.calldata) 264).2 < 256 <;>
        simp [h, flag]
    rw [hflag]
    have hst : posSt s ret tail (cStream s.executionEnv.calldata) 8 (256 - P.tau) 0 M6 =
        headSt s ret tail 32 196 (sgw (cStream s.executionEnv.calldata) 196) M6 := by
      unfold posSt
      rw [if_pos (by norm_num)]
      rfl
    rw [hst] at hreach
    exact ((((((r1.trans r2).trans r3).trans r4).trans c5).trans r6).trans hreach).mono
      (by unfold pot Gas.sib sqX; rw [rs_8]; simp only [tau_eq, Gas.kf1]; norm_num)

end MlDsaOpt87.Proofs
