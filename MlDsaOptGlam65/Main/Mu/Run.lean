import MlDsaOptGlam65.Main.Mu.Long
import MlDsaOptGlam65.Main.Mu.Cext
import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Main.Inv
import MlDsaOptGlam65.Fn.Keccak
import MlDsaOptGlam65.Fn.Sponge
import MlDsaOpt44.Math.SpongeG234
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Hand-written: `MlDsaOpt65/Main/Mu/Run.lean` ported by `scripts/proofgen_port.py --glam 65`
(relocated indices and pcs), then adapted by hand (`mu_setup`: the `MCOPY` from `MUIMG`,
μ's sponge after block 0, block 1); not in `port.py`'s `FILES`. -/
set_option warningAsError true
/-! # `seg_mu` (Glamsterdam ML-DSA-65): composition of the blocks with `cext`, `kf1` and `absorb17`

Long path (`|M| ≥ 70`): the sponge after block `0` is slot 2 of the kf4 state
image at `MUIMG` (`MuKs`); `MCOPY` restores it into `KS`, it is extracted in
place and replicated (`KS1` of `absorbPre 1`); block 1 is absorbed by
`absorb17` at `0x14d3`; the loop head then holds the raw lanes of block `j`
xored into `absorbPre j` (`MuInv j`, `j ≥ 1`), with the next block's calldata
offset `5331 + 136 j` on the stack. -/

namespace MlDsaOptGlam65.Proofs.S6Mu

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs hiding ACC AccAt AccAt.frame BASES BK CB CRep CRep.frame CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN FinAt FinMu FinMu.frame H0 HDR HP HPAt HPAt.frame IDX Inv0 Inv1 Inv2 Inv3 Inv4 Inv6 Inv7 Inv8 Inv9 InvH InvW KZ MU RC1Table.frame RC4Table.frame RHO1 RetOK Rho1At Rho1At.frame SP SibFresh SibFresh.frame TOP TRL TTable TblAt.frame Z0 ZAt ZAt.frame ZHatAt ZHatAt.frame ZeroOn.frame ZeroOn.mono aD aOf azRow baseOf byteAt_muMsgW cD cOf cStream codeOf ctOf finBytes finalState ginitWord hintD hintOf le64_muMsgW_64 le64_muMsgW_hi le64_muMsgW_lo le64_muOf_absorb memWords mlenOf msgOf muBlock muMsgW muMsgW_size muOf muPad nNeg negCount ok2 ok3 okA okC okH okZ optAccepts padMu padPk pkOf rawZ retOK_main rhoOf sPrime sigOf sized sized_activeWords sized_ctx spOff t1Of t1v tEntry trOf trOf_sizeW w1Of wRow word_frame zHat zHi zLane zLo zPolys
open MlDsaOptGlam65.Proofs.Infra

/-- Lanes at the loop head after `j` permutations: block `j`'s raw lanes xored in. -/
def muLanes (cd : ByteArray) (j x : Nat) : Nat :=
  laneOf (absorbPre 136 (muPad cd) j) x ^^^ (if x < 17 then le64 (muMsgW cd) (136 * j + 8 * x) else 0)

structure MuInv (cd m M : ByteArray) (j : Nat) : Prop where
  rc1 : RC1Table M
  fr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)]
  ks : ∀ x, x < 25 → word M (KS + 32 * x) = rep (cpl x (muLanes cd j x))

theorem muLanes_lt (cd : ByteArray) (j x : Nat) : muLanes cd j x < 2 ^ 64 := by
  unfold muLanes
  apply Nat.xor_lt_two_pow (laneOf_lt _ _)
  split
  · exact le64_lt _ _
  · norm_num

/-- Frames inside the three Keccak buffers. -/
theorem frame3_mono {m m' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m m' rs)
    (hrs : ∀ r ∈ rs, (KS ≤ r.1 ∧ r.2 ≤ KS + 800) ∨ (KB ≤ r.1 ∧ r.2 ≤ KB + 800) ∨
      (KZ ≤ r.1 ∧ r.2 ≤ KZ + 800)) :
    FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] :=
  h.mono fun r hr => by
    rcases hrs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩

/-- One loop visit absorbing the next full block. -/
theorem mu_iter {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m M : ByteArray} (j : Nat) (hj : 136 * (j + 1) ≤ (muMsgW s.executionEnv.calldata).size)
    (hI : MuInv s.executionEnv.calldata m M j) :
    ∃ M', MuInv s.executionEnv.calldata m M' (j + 1) ∧
      Reach (callState s 5636 [wd ((muMsgW s.executionEnv.calldata).size - 136 * j),
          wd (5331 + 136 * j), flag b] M)
        (callState s 5636 [wd ((muMsgW s.executionEnv.calldata).size - 136 * (j + 1)),
          wd (5331 + 136 * (j + 1)), flag b] M') (Gas.kf1 + Gas.absorb17 + 88) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hL := muMsgW_size s.executionEnv.calldata hcd
  set L := (muMsgW s.executionEnv.calldata).size
  have h1 := mu_loop1 hs b M (len := L - 136 * j) (off := 5331 + 136 * j) (by omega) (by omega)
  set S' := Fips202.xorBlock 136 (muPad s.executionEnv.calldata) (j * 136)
    (absorbPre 136 (muPad s.executionEnv.calldata) j)
  have hS' : S'.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M S' := fun x hx => by
    rw [hI.ks x hx, laneOf_xorBlock _ _ (absorbPre_size _ _ j) (by norm_num) x]
    unfold muLanes
    by_cases h : x < 17
    · rw [if_pos (by omega), if_pos h, show muPad s.executionEnv.calldata =
        Fips202.pad 136 0x1F (muMsgW s.executionEnv.calldata) from rfl, le64_pad_full _ (by omega),
        show j * 136 + 8 * x = 136 * j + 8 * x by ring]
    · rw [if_neg (by omega), if_neg h, Nat.xor_zero]
  obtain ⟨M1, hk1, hf1, hc1⟩ := kf1_call hs (ret := 5652)
    (tail := [wd (L - 136 * j), wd (5331 + 136 * j), flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M hI.rc1
  have hK1 : KS1 M1 (absorbPre 136 (muPad s.executionEnv.calldata) (j + 1)) := by
    rw [absorbPre_succ]; exact hk1 S' hS' hK
  have h2 := mu_loop2 hs b M1 (len := L - 136 * j) (off := 5331 + 136 * j)
  obtain ⟨M2, ha2, hf2, hc2⟩ := WP4.absorb17_call_aux hs (ret := 5662)
    (tail := [wd (5331 + 136 * j), wd (L - 136 * j), flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M1
    (off := 5331 + 136 * j) (by omega)
  have h3 := mu_loop3 hs b M2 (len := L - 136 * j) (off := 5331 + 136 * j) (by omega) (by omega)
  rw [show L - 136 * j - 136 = L - 136 * (j + 1) by omega,
    show 136 + (5331 + 136 * j) = 5331 + 136 * (j + 1) by ring] at h3
  rw [call_iff] at hc1 hc2
  have hfr : FrameExcept m M2 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] :=
    frame3_mono ((hI.fr.trans hf1).trans hf2) (by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, KZ])
  refine ⟨M2, ⟨(hI.rc1.frame hf1 (by avoids_tac)).frame hf2 (by avoids_tac), hfr, fun x hx => ?_⟩, ?_⟩
  · rw [ha2 x hx, hK1 x hx]
    unfold muLanes
    split
    · rw [rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _),
        le64_muMsgW_hi _ (a := 136 * (j + 1) + 8 * x) (by omega),
        show 5195 + (136 * (j + 1) + 8 * x) = 5331 + 136 * j + 8 * x by ring]
    · rw [Nat.xor_zero]
  · exact ((((h1.trans hc1).trans h2).trans hc2).trans h3).mono (by omega)

theorem mu_loop {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m M0 : ByteArray} {j0 : Nat} (hI0 : MuInv s.executionEnv.calldata m M0 j0) :
    ∀ k, 136 * (j0 + k) ≤ (muMsgW s.executionEnv.calldata).size →
      ∃ M, MuInv s.executionEnv.calldata m M (j0 + k) ∧
        Reach (callState s 5636 [wd ((muMsgW s.executionEnv.calldata).size - 136 * j0),
            wd (5331 + 136 * j0), flag b] M0)
          (callState s 5636 [wd ((muMsgW s.executionEnv.calldata).size - 136 * (j0 + k)),
            wd (5331 + 136 * (j0 + k)), flag b] M) (k * (Gas.kf1 + Gas.absorb17 + 88))
  | 0, _ => ⟨M0, hI0, by simpa using Reach.refl _⟩
  | k + 1, hk => by
    obtain ⟨M, hI, hR⟩ := mu_loop hs hcd b hI0 k (by omega)
    obtain ⟨M', hI', hR'⟩ := mu_iter hs hcd b (j0 + k) (by rw [Nat.add_assoc]; exact hk) hI
    exact ⟨M', hI', (hR.trans hR').mono (by rw [Nat.succ_mul])⟩

theorem padLane_hi {r x : Nat} (hr : r < 136) (hx : 17 ≤ x) : padLane r x = 0 := by
  unfold padLane; rw [if_neg (by omega), if_neg (by omega), Nat.xor_zero]

/-- Exit: padding, the final permutation and the copy of μ's lanes to `FIN`. -/
theorem mu_finish {s : State} (hs : Ctx s) (b : Bool)
    {m M : ByteArray}
    (hI : MuInv s.executionEnv.calldata m M ((muMsgW s.executionEnv.calldata).size / 136)) :
    ∃ M', FinMu M' s.executionEnv.calldata ∧ RC1Table M' ∧
      FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] ∧
      Reach (callState s 5636 [wd ((muMsgW s.executionEnv.calldata).size -
          136 * ((muMsgW s.executionEnv.calldata).size / 136)),
          wd (5331 + 136 * ((muMsgW s.executionEnv.calldata).size / 136)), flag b] M)
        (callState s 5843 [flag b] M') (23 + 100 + Gas.kf1 + 102) := by
  set cd := s.executionEnv.calldata with hcdef
  set L := (muMsgW cd).size
  set n := L / 136
  have hr : L - 136 * n = L % 136 := by omega
  have hr' : L % 136 < 136 := Nat.mod_lt _ (by norm_num)
  have h1 := mu_exit hs b M (len := L - 136 * n) (off := 5331 + 136 * n) (by omega)
  obtain ⟨M5, f5, fr5, r5⟩ := mu_pad hs b M (len := L - 136 * n) (off := 5331 + 136 * n) (by omega)
  set S'' := Fips202.xorBlock 136 (muPad cd) (L / 136 * 136) (absorbPre 136 (muPad cd) n)
  have hS'' : S''.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M5 S'' := fun x hx => by
    rw [f5 x hx, hI.ks x hx, hr, rep_cpl_xor _ (muLanes_lt _ _ _) (padLane_lt _ _),
      laneOf_xorBlock _ _ (absorbPre_size _ _ n) (by norm_num) x]
    unfold muLanes
    by_cases h : x < 17
    · rw [if_pos (by omega), if_pos h, show muPad cd =
        Fips202.pad 136 0x1F (muMsgW cd) from rfl, le64_pad_last _ h, Nat.xor_assoc,
        show 136 * n = L / 136 * 136 by ring]
    · rw [if_neg (by omega), if_neg h, Nat.xor_zero, padLane_hi hr' (by omega), Nat.xor_zero]
  obtain ⟨M6, hk6, hf6, hc6⟩ := kf1_call hs (ret := 5777) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M5
    ((hI.rc1).frame fr5 (by avoids_tac))
  have hP : (muPad cd).size = (n + 1) * 136 := by
    rw [show muPad cd = Fips202.pad 136 0x1F (muMsgW cd) from rfl, pad_size _ _ (by norm_num)]
  have hK6 : KS1 M6 (Fips202.absorb 136 (muPad cd)) := by
    rw [absorb_eq _ _ (n + 1) (by norm_num) hP, absorbPre_succ,
      show n * 136 = L / 136 * 136 from rfl]
    exact hk6 S'' hS'' hK
  obtain ⟨M7, f7, fr7, r7⟩ := mu_copy hs b M6
  rw [call_iff] at hc6
  have hfr : FrameExcept m M7 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] := by
    refine (((hI.fr.trans fr5).trans hf6).trans fr7).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, KZ, FIN]
  refine ⟨M7, fun x hx => ?_, ((hI.rc1.frame fr5 (by avoids_tac)).frame hf6 (by avoids_tac)).frame fr7
    (by avoids_tac), hfr, (((h1.trans r5).trans hc6).trans r7).mono (by omega)⟩
  rw [f7 x hx, hK6 x (by omega), le64_muOf_absorb cd hx]
  have hl := laneOf_lt (Fips202.absorb 136 (muPad cd)) x
  split
  · rename_i h
    exact not_rep_cpl (by rcases h with rfl | rfl <;> decide) hl
  · rename_i h
    unfold cpl
    rw [if_neg (by interval_cases x <;> simp_all [complemented])]

/-- Lanes `[a, b)` of the replication blocks read the extracted lanes. -/
theorem rep_hT {M2 M : ByteArray} {S : Fips202.SpongeState} {rs : List (Nat × Nat)}
    (hv : ∀ x, x < 25 → word M2 (KS + 32 * x) = laneOf S x) (hf : FrameExcept M2 M rs)
    {a b : Nat} (hab : b ≤ 25) (havoid : ∀ x, a ≤ x → x < b → Avoids rs (KS + 32 * x) (KS + 32 * x + 32)) :
    ∀ x, a ≤ x → x < b → word M (KS + 32 * x) < 2 ^ 64 := fun x h1 h2 => by
  rw [FrameExcept.word hf (havoid x h1 h2), hv x (by omega)]; exact laneOf_lt _ _

/-- `muPad` is the padded μ input of the invariant `MuKs`. -/
theorem muPad_eq (cd : ByteArray) : muPad cd = padMu cd := rfl

set_option maxHeartbeats 400000 in
/-- The long path's setup (`5017 … 5636`): μ's sponge after block `0` from slot 2
of the state image at `MUIMG` (copied back to `KS`), as a `kf1` state, with block
1's raw lanes absorbed. -/
theorem mu_setup {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m : ByteArray} (hks : MlDsaOptGlam65.Proofs.MuKs m s.executionEnv.calldata) (hrc : RC1Table m)
    (hl : 5331 ≤ s.executionEnv.calldata.size) :
    ∃ M, MuInv s.executionEnv.calldata m M 1 ∧
      Reach (callState s 5017 [flag b] m)
        (callState s 5636 [wd ((muMsgW s.executionEnv.calldata).size - 136 * 1),
          wd (5331 + 136 * 1), flag b] M) (24 + 6971) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hsz : 3384 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  obtain ⟨S, -, hst, hS1⟩ := hks
  have r0 := mu_chk_long hs b m hfit hl
  have r1 := mu_cpy hs b m
  have hmc := reach_mcopy hs ⟨1803, by norm_num⟩ (pc := 5336) (d := KS) (src := MUIMG) (n := 800)
    (rest := [flag b]) (m := m) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by unfold KS; omega) (by unfold MUIMG; omega) (by omega) (by omega) (by unfold KS; omega)
    (by unfold MUIMG; omega) (by simp)
  have hf1 := FrameExcept.mcopy m MUIMG KS 800
  have hks4 : KS4 (MachineState.writeBytes m (MachineState.readPadded m MUIMG 800) KS) S :=
    fun x hx => by
      rw [word_mcopy _ (by unfold KS; omega) (by unfold KS; omega),
        show MUIMG + (KS + 32 * x - KS) = MUIMG + 32 * x by unfold KS; omega]
      exact hst x hx
  generalize MachineState.writeBytes m (MachineState.readPadded m MUIMG 800) KS = m1 at hmc hf1 hks4
  have r2 := mu_cext_pre hs b m1
  obtain ⟨m2, hc2, hf2, hcall2⟩ := cext_inplace_call hs (ret := 5350) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (sh := 2) (n := 25) (by norm_num) (by norm_num) (by norm_num)
  have hv2 : ∀ x, x < 25 → word m2 (KS + 32 * x) = laneOf (S 2) x := fun x hx => by
    rw [hc2 x hx]; exact cext_lane hks4 (by norm_num) hx
  obtain ⟨m3, hA, rA⟩ := mu_repA hs b m2 (rep_hT hv2 (FrameExcept.refl _ []) (by norm_num)
    (fun _ _ _ => by simp))
  obtain ⟨m4, hB, rB⟩ := mu_repB hs b m3 (rep_hT hv2 hA.2 (by norm_num)
    (fun x h1 _ => by simp only [avoids_cons, avoids_nil, and_true]; omega))
  have hAB := hA.trans hB (by norm_num) (by norm_num)
  obtain ⟨m5, hC, rC⟩ := mu_repC hs b m4 (rep_hT hv2 hAB.2 (by norm_num)
    (fun x h1 _ => by simp only [avoids_cons, avoids_nil, and_true]; omega))
  have hAC := hAB.trans hC (by norm_num) (by norm_num)
  obtain ⟨m6, hD, rD⟩ := mu_repD hs b m5 (rep_hT hv2 hAC.2 (by norm_num)
    (fun x h1 _ => by simp only [avoids_cons, avoids_nil, and_true]; omega))
  have hAD := hAC.trans hD (by norm_num) (by norm_num)
  have hK1 : ∀ x, x < 25 → word m6 (KS + 32 * x) =
      rep (cpl x (laneOf (absorbPre 136 (muPad s.executionEnv.calldata) 1) x)) := fun x hx => by
    rw [hAD.1 x (Nat.zero_le _) hx, hv2 x hx, hS1, muPad_eq]
  have r3 := mu_abs1 hs b m6
  obtain ⟨m7, ha7, hf7, hc7⟩ := WP4.absorb17_call_aux hs (ret := 5627) (tail := [wd 5331, flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (off := 5331) (by norm_num)
  have r4 := mu_head0 hs b m7 hfit hl
  have hL := muMsgW_size s.executionEnv.calldata hcd
  rw [show s.executionEnv.calldata.size - 5331 = (muMsgW s.executionEnv.calldata).size - 136 * 1 by
    omega, show (5467 : Nat) = 5331 + 136 * 1 by rfl] at r4
  rw [call_iff] at hcall2 hc7
  have hfr := (((hf1.trans hf2).trans hAD.2).trans hf7)
  refine ⟨m7, ⟨hrc.frame hfr (by avoids_tac), frame3_mono hfr (by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [KS]), fun x hx => ?_⟩, ?_⟩
  · rw [ha7 x hx, hK1 x hx]
    unfold muLanes
    split
    · rw [rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _),
        le64_muMsgW_hi _ (a := 136 * 1 + 8 * x) (by omega),
        show 5195 + (136 * 1 + 8 * x) = 5331 + 8 * x by ring]
    · rw [Nat.xor_zero]
  · refine (((((((((((r0.trans r1).trans hmc).trans r2).trans hcall2).trans rA).trans rB).trans
      rC).trans rD).trans r3).trans hc7).trans r4).mono ?_
    norm_num [Gas.cext, Gas.absorb17]

end MlDsaOptGlam65.Proofs.S6Mu
