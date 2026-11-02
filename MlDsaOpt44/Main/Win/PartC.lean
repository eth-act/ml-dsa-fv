import MlDsaOpt44.Main.Win.States
import MlDsaOpt44.Main.Win.Math
set_option warningAsError true
/-!
# Window part C: `4422 … 4544`

`ginit` (`c̃`'s seed in slot 0, an empty slot 1; row 3 kept), `mub0` (μ's
block 0 into slot 1), call 20, `cext` of `H(c̃)`'s first block into `CB` and of
μ into `MU`, the image `SC`.
-/

namespace MlDsaOpt44.Proofs.Ex

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

/-- The state `ginit` leaves before `mub0`. -/
def V3 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then C0 cd else if k = 1 then Fips202.emptyState else W2 cd 2 k

theorem winC_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrho : Rho1At m s.executionEnv.calldata) (hks : KS4 m (W2 s.executionEnv.calldata 2)) :
    ∃ m1, KS4 m1 (V3 s.executionEnv.calldata) ∧ FrameExcept m m1 [(KS, KS + 800)] ∧
      Reach (callState s 4422 [flag w] m) (callState s 4469 [flag w] m1) (25 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho hks
  have g0 : Reach (callState s 4422 [flag w] m)
      (callState s 10911 [wd 0x011111, wd 1, wd 0,
        wd 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, wd 4469, flag w] m) 25 := by
    opt44_reach [1412, 1413, 1414, 1415, 1416, 1417, 1418]
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 4469) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (keep := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) (amult := 0)
    (cmult := 1) (l4 := 0x011111)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hkeep : (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Nat) =
      il fun k => if (12 : Nat).testBit k then M64 else 0 := by decide +kernel
  have hks1 : KS4 m1 (V3 cd) :=
    ks4_ginit (kmask := 12) (L := fun k => if k = 0 then 31 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := W2 cd 2)
      (by norm_num) (by norm_num) hkeep (by decide +kernel)
      (fun x hx => (hrho x hx).1) (fun x hx => (hrho x hx).2)
      (fun x hx => by rw [hkeep]; exact ks4_and_keep hks 12 hx)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k hk h => by
        have : 2 ≤ k := by
          by_contra hne
          interval_cases k <;> exact absurd h (by decide)
        interval_cases k <;> exact ⟨by decide, by decide, by simp⟩)
      (fun k hk h => by
        have : 2 ≤ k := by
          by_contra hne
          interval_cases k <;> exact absurd h (by decide)
        interval_cases k <;> (unfold V3; simp))
      (fun k hk h x hx => by
        have : k < 2 := by
          by_contra hne
          interval_cases k <;> first | omega | exact absurd h (by decide)
        interval_cases k
        · have e : V3 cd 0 = seedState 136 (ctOf cd) := by unfold V3 C0; simp
          rw [e]
          exact freshLane_ctSeed (by unfold HDR at hcd; omega) (fun _ _ => rfl) (by decide) (by decide)
            (by simp) hx
        · have e : V3 cd 1 = Fips202.emptyState := by unfold V3; simp
          rw [e]
          exact freshLane_zero (by decide) (by decide) (by simp) x)
      hg
  exact ⟨m1, hks1, hf1, g0.trans hc1⟩

theorem trLanes_lt (cd : ByteArray) : (trOf cd).size = 64 := trOf_size cd

/-- `mub0`, including the `POP` of the short path. -/
theorem winC_mub0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (htrl : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x))
    (hks : KS4 m (V3 s.executionEnv.calldata)) :
    ∃ m1, KS4 m1 (W3 s.executionEnv.calldata) ∧ FrameExcept m m1 [(KS, KS + 800)] ∧
      Reach (callState s 4469 [flag w] m) (callState s 4484 [flag w] m1) (21 + Gas.mub0 + 3) := by
  have g0 : Reach (callState s 4469 [flag w] m)
      (callState s 12640 [wd 1, wd 4482, wd 4484, flag w] m) 21 := by
    opt44_reach [1419, 1420, 1421, 1422, 1423, 1424]
  obtain ⟨m1, hpost, hf1, hc1⟩ := mub0_call hs (rl := 4484) (rs := 4482) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num))
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (sh := 1) (by norm_num) hcd
  have hw := hpost (trOf s.executionEnv.calldata) (trOf_size _) htrl
  have hks1 : KS4 m1 (W3 s.executionEnv.calldata) := by
    have h := ks4_xor_slot (sh := 1) (by norm_num) hks
      (fun x => if x < 17 then le64 (mu0Bytes (trOf s.executionEnv.calldata) s.executionEnv.calldata) (8 * x)
        else 0)
      (fun x _ => by split; exact le64_lt _ _; norm_num)
      (fun x hx => by
        rw [hw x hx]
        split
        · rfl
        · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
      (Mu0 s.executionEnv.calldata) (fun x hx => by
        unfold Mu0
        rw [laneOf_xorBlock _ _ emptyState_size (by norm_num)]
        have hV : V3 s.executionEnv.calldata 1 = Fips202.emptyState := by unfold V3; simp
        rw [hV]
        split
        · rw [Nat.zero_add, le64_mu0Bytes hcd (by omega)]
        · rw [Nat.xor_zero])
    refine KS4.congr h fun k hk => ?_
    unfold W3 V3
    by_cases h0 : k = 0
    · subst h0; simp
    · by_cases h1 : k = 1
      · subst h1; simp
      · simp [h0, h1]
  have hm : Reach (callState s 12640 [wd 1, wd 4482, wd 4484, flag w] m) (callState s 4484 [flag w] m1)
      (Gas.mub0 + 3) := by
    by_cases hshort : mlenOf s.executionEnv.calldata ≤ 69
    · rw [if_pos hshort] at hc1
      have gp : Reach (callState s 4482 [wd 4484, flag w] m1) (callState s 4484 [flag w] m1) 3 := by
        opt44_reach [1425, 1426]
      exact hc1.trans gp
    · rw [if_neg hshort] at hc1
      exact hc1.mono (by omega)
  exact ⟨m1, hks1, hf1, (g0.trans hm).mono (le_of_eq (by omega))⟩

theorem W3_perm_sized (cd : ByteArray) : Sized4 fun k => Keccak.permute (W3 cd k) :=
  sized4_permute (W3_sized cd)

/-- Window part C. -/
theorem winC {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata)
    (hks : KS4 m (W2 s.executionEnv.calldata 2)) (hB : HBlocks m ABUF FL (EB s.executionEnv.calldata) 2)
    (htrl : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (W3 s.executionEnv.calldata k)) ∧
      HBlocks m' ABUF FL (EB s.executionEnv.calldata) 3 ∧
      (∀ x, x < 17 → word m' (CB + 32 * x) = le64 (cStream s.executionEnv.calldata) (8 * x)) ∧
      (mlenOf s.executionEnv.calldata ≤ 69 → ∀ x, x < 8 →
        word m' (MU + 32 * x) = le64 (muOf s.executionEnv.calldata) (8 * x)) ∧
      ScAt m' s.executionEnv.calldata ∧
      St4At m' SC (fun k => Keccak.permute (W3 s.executionEnv.calldata k)) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF + 1792 * 2, ABUF + 1792 * 2 + 1792),
        (FL + 224 * 2, FL + 224 * 2 + 224), (CB, CB + 544), (MU, MU + 256), (SC, SC + 800)] ∧
      Reach (callState s 4422 [flag w] m) (callState s 4544 [flag w] m')
        (25 + Gas.ginit + (21 + Gas.mub0 + 3) + (15 + Gas.kf4 + 21 + Gas.blk) + 23 + Gas.cext 17 +
          24 + Gas.cext 8 + 9 + 78) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 1344 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have htl : [flag w].length ≤ 8 := by simp
  obtain ⟨m1, hks1, hf1, hR1⟩ := winC_ginit hs hcd hrho hks (w := w)
  obtain ⟨m2, hks2, hf2, hR2⟩ := winC_mub0 hs hcd (w := w)
    (fun x hx => by rw [word_frame hf1 (lo := TRL) (hi := TRL + 256) (by avoids_tac) (by omega) (by omega)];
                    exact htrl x hx) hks1
  have hf12 := FrameExcept.trans hf1 hf2
  -- call 20
  obtain ⟨m3, hks3, hB3, hrc3, hf3, hR3⟩ := kb_round hs htl (stk := [flag w]) (m := m2)
    (pc0 := 4484) (r1 := 4492) (r2 := 4506) (c1 := 15) (c2 := 21) (b := 2) (by norm_num) bufOK_abuf
    (by opt44_reach [1427, 1428, 1429, 1430])
    (fun _ => by opt44_reach [1431, 1432, 1433, 1434, 1435, 1436] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (hrc.frame hf12 (by avoids_tac)) (W3_sized _) hks2
    (hB.frame hf12 (by avoids_tac) (by avoids_tac)) (St := EB s.executionEnv.calldata)
    (fun k _ => by unfold EB; simp)
  -- H(c̃)'s first block into CB
  have gC : Reach (callState s 4506 [flag w] m3) (callState s 12151 [wd 17, wd 0, wd CB, wd 4520, flag w] m3)
      23 := by
    opt44_reach [1437, 1438, 1439, 1440, 1441, 1442, 1443] with [CB]
  obtain ⟨m4, hcb, hf4, hc4⟩ := cext_call hs (ret := 4520) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := CB) (sh := 0) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hks4 := KS4.frame hks3 hf4 (by avoids_tac)
  -- μ into MU
  have gM : Reach (callState s 4520 [flag w] m4) (callState s 12151 [wd 8, wd 1, wd MU, wd 4535, flag w] m4)
      24 := by
    opt44_reach [1444, 1445, 1446, 1447, 1448, 1449, 1450] with [MU]
  obtain ⟨m5, hmu, hf5, hc5⟩ := cext_call hs (ret := 4535) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := MU) (sh := 1) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS MU; norm_num)
    (by unfold MU TOP; norm_num)
  have hks5 := KS4.frame hks4 hf5 (by avoids_tac)
  -- the image SC
  have g6 : Reach (callState s 4535 [flag w] m5) (callState s 4543 [wd SC, wd KS, wd 800, flag w] m5) 9 := by
    opt44_reach [1451, 1452, 1453, 1454] with [SC, KS]
  have hmc := reach_mcopy hs ⟨1455, by norm_num⟩ (pc := 4543) (d := SC) (src := KS) (n := 800)
    (rest := [flag w]) (m := m5)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold SC; norm_num)
    (by unfold KS; norm_num) (by norm_num) (by norm_num) (by unfold SC; omega) (by unfold KS; omega) (by simp)
  have hf6 := FrameExcept.mcopy m5 KS SC 800
  have hsc : St4At (MachineState.writeBytes m5 (MachineState.readPadded m5 KS 800) SC) SC
      (fun k => Keccak.permute (W3 s.executionEnv.calldata k)) := fun x hx => by
    rw [word_mcopy _ (by omega) (by omega), show KS + (SC + 32 * x - SC) = KS + 32 * x by omega]
    exact hks5 x hx
  refine ⟨_, KS4.frame hks5 hf6 (by avoids_tac),
    ((HBlocks.frame hB3 hf4 (by avoids_tac) (by avoids_tac)).frame hf5 (by avoids_tac) (by avoids_tac)).frame
      hf6 (by avoids_tac) (by avoids_tac),
    fun x hx => ?_, fun hshort x hx => ?_, ⟨_, W3_perm_sized _, hsc, ?_, ?_⟩, hsc,
    ((hrc3.frame hf4 (by avoids_tac)).frame hf5 (by avoids_tac)).frame hf6 (by avoids_tac), ?_, ?_⟩
  · rw [word_frame hf6 (lo := CB) (hi := CB + 544) (by avoids_tac) (by omega) (by omega),
      word_frame hf5 (lo := CB) (hi := CB + 544) (by avoids_tac) (by omega) (by omega), hcb x hx,
      cext_lane hks3 (by norm_num) (by omega)]
    have := le64_cStream hcd' (j := 0) (by norm_num) hx
    rw [show 8 * (17 * 0 + x) = 8 * x by omega] at this
    rw [this]; unfold W3 C0; simp; rfl
  · rw [word_frame hf6 (lo := MU) (hi := MU + 256) (by avoids_tac) (by omega) (by omega), hmu x hx,
      cext_lane hks4 (by norm_num) (by omega), le64_muOf hshort hx]
    unfold W3 Mu0 padMu seedState; simp; rfl
  · unfold W3 C0; simp; rfl
  · unfold W3 Mu0
    rw [absorbPre_succ, absorbPre_zero, Nat.zero_mul, if_neg (by decide), if_pos rfl]
  · have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf12 hf3) hf4) hf5) hf6
    exact hf.mono (by decide)
  · have hR := (((((((hR1.trans hR2).trans hR3).trans gC).trans hc4).trans gM).trans hc5).trans g6).trans hmc
    refine hR.mono (le_of_eq ?_)
    generalize Gas.ginit = a; generalize Gas.mub0 = c; generalize Gas.kf4 = d; generalize Gas.blk = e
    generalize Gas.cext 17 = f; generalize Gas.cext 8 = g
    omega

end MlDsaOpt44.Proofs.Ex
