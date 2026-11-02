import MlDsaOptGlam65.Main.Exp.WinA
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # The window, calls 35, 36 (`3739 … 3982`): see `WinA.lean` -/

namespace MlDsaOptGlam65.Proofs.Exp

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding Rho1At ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

/-- The slots after the first `ginit`: `A44`, `tr` (blocks 0 … 9), `A34`, `A33`. -/
def I1 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then sA cd 4 4 else if k = 1 then T cd 10 else if k = 2 then sA cd 3 4 else sA cd 3 3

theorem I1_sized (cd : ByteArray) : Sized4 (I1 cd) := fun k _ => by
  unfold I1
  by_cases h0 : k = 0
  · rw [if_pos h0]; exact sA_size _ _ _
  · rw [if_neg h0]; by_cases h1 : k = 1
    · rw [if_pos h1]; exact T_size _ _
    · rw [if_neg h1]; by_cases h2 : k = 2
      · rw [if_pos h2]; exact sA_size _ _ _
      · rw [if_neg h2]; exact sA_size _ _ _

theorem T_succ (cd : ByteArray) (j : Nat) :
    Keccak.permute (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (j * 136) (T cd j)) = T cd (j + 1) := by
  unfold T; rw [absorbPre_succ]

/-- Call 35: `W 0`. -/
theorem W_c35 (cd : ByteArray) {k : Nat} (_hk : k < 4) :
    W cd 0 k = Keccak.permute (upd (I1 cd) 1
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (10 * 136) (I1 cd 1)) k) := by
  unfold upd
  by_cases h1 : k = 1
  · subst h1; rw [if_pos rfl, show I1 cd 1 = T cd 10 from by unfold I1; simp, T_succ]
    unfold W; simp
  · rw [if_neg h1]
    unfold W I1
    rcases (by omega : k = 0 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;> simp [permN_succ, permN]

/-- Call 36: `W 1`. -/
theorem W_c36 (cd : ByteArray) {k : Nat} (_hk : k < 4) :
    W cd 1 k = Keccak.permute (upd (W cd 0) 1
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (11 * 136) (W cd 0 1)) k) := by
  unfold upd
  by_cases h1 : k = 1
  · subst h1; rw [if_pos rfl, show W cd 0 1 = T cd 11 from by unfold W; simp, T_succ]
    unfold W; simp
  · rw [if_neg h1]
    unfold W
    rcases (by omega : k = 0 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;> simp [permN_succ]


/-- Calls 35, 36 and the image `IMGA` (`3739 … 3992`). -/
def cW1 : Nat := 26 + Gas.kmove + 26 + Gas.ginit + (29 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) +
  (29 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) + 9 + 78

set_option maxHeartbeats 1000000 in
theorem win_1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : WinIn s.executionEnv.calldata m) (b : Bool) :
    ∃ m', KS4 m' (W s.executionEnv.calldata 1) ∧ St4At m' 0x14a00 (W s.executionEnv.calldata 1) ∧
      HBlocks m' ABUF FL (W s.executionEnv.calldata) 2 ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (0x14a00, 0x14a00 + 800)] ∧
      Reach (callState s 3739 [flag b] m) (callState s 3992 [flag b] m') cW1 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hcdC : CTOFF ≤ s.executionEnv.calldata.size := by unfold CTOFF; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  have htl : [flag b].length ≤ 8 := by simp
  obtain ⟨S0, hS0, hks0, h00⟩ := hI.tr
  -- kmove: tr to slot 1
  have g1 : Reach (callState s 3739 [flag b] m)
      (callState s 18099 [wd 0, wd 0x2222222222222222222222222222222222222222222222222222222222222222,
        wd 0, wd 1, wd 0, wd 3784, flag b] m) 26 := by
    glam65_rreach [1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405]
  obtain ⟨m1, hw1, hf1, hc1⟩ := kmove_call hs (ret := 3784) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (src := 0) (sl := 1) (sr := 0) (msk := 0x2222222222222222222222222222222222222222222222222222222222222222)
    (keep := 0) (Or.inl rfl) (by unfold TOP; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho1 := hI.rho.frame hf1 (by w_frame)
  -- ginit: A44, A34, A33 in slots 0, 2, 3
  have g2 : Reach (callState s 3784 [flag b] m1)
      (callState s 17659 [wd 0x0ddddd000001cc00000588, wd 0, wd 13,
        wd 0x2222222222222222222222222222222222222222222222222222222222222222, wd 3840, flag b] m1) 26 := by
    glam65_rreach [1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413]
  obtain ⟨m2, hks2, hf2, hR2⟩ := wginit hs hrho1 (S := fun k => if k = 1 then S0 0 else S0 k)
    (I := I1 s.executionEnv.calldata) (kmask := 2) (amult := 13) (cmult := 0) (l4 := 0x0ddddd000001cc00000588)
    (L := fun k => if k = 0 then 4 + 256 * 4 + 0x1F0000 else if k = 2 then 4 + 256 * 3 + 0x1F0000
      else if k = 3 then 3 + 256 * 3 + 0x1F0000 else 0)
    (by norm_num) (by norm_num) keep2
    (fun x hx => by
      have h1 := hw1 x hx
      have h0 := hks0 x hx
      simp only [KS, Nat.zero_add] at h1 h0 ⊢
      rw [h1, h0, kmove_01 _ (fun k _ => cpl_lt (laneOf_lt _ _)), keep2,
        and_keep (fun k _ => by split <;> first | exact cpl_lt (laneOf_lt _ _) | norm_num)]
      apply il_congr; intro k hk
      by_cases h1 : k = 1
      · subst h1; simp
      · rw [if_neg h1, show (2 : Nat).testBit k = false by
          interval_cases k <;> first | exact absurd rfl h1 | decide]
        simp)
    (by decide +kernel) (fun k _ => by split_ifs <;> omega)
    (fun k hk hb => by
      obtain rfl : k = 1 := by interval_cases k <;> first | rfl | exact absurd hb (by decide)
      exact ⟨by decide, by decide, by simp⟩)
    (fun k hk hb => by
      obtain rfl : k = 1 := by interval_cases k <;> first | rfl | exact absurd hb (by decide)
      simp only [if_true]; unfold I1; rw [h00]; rfl)
    (fun k hk hb x hx => by
      interval_cases k
      · show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 4 4)) x
        exact S4.freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
          (by decide) (by simp) hx
      · exact absurd hb (by decide)
      · show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 3 4)) x
        exact S4.freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
          (by decide) (by simp) hx
      · show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 3 3)) x
        exact S4.freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
          (by decide) (by simp) hx)
    g2 (by simp only [isValidJumpDest_lit]) (by norm_num)
  -- call 35: tr block 10 into slot 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdC htl (m := m2)
    (pc0 := 3840) (r0 := 3889) (r1 := 3897) (r2 := 3911) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 10) (off := 1360) (sh := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam65_rreach [1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422])
    (fun _ => by glam65_rreach [1423, 1424, 1425, 1426])
    (fun _ => by glam65_rreach [1427, 1428, 1429, 1430, 1431, 1432] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame (RC4Table.frame hI.rc4 hf1 (by w_frame)) hf2 (by w_frame)) (I1_sized _) hks2
    (HBlocks.zero _ _ _ _) (St := W s.executionEnv.calldata) (fun k hk => W_c35 _ hk)
  have hks3 : KS4 m3 (W s.executionEnv.calldata 0) := KS4.congr hks3' fun k hk => (W_c35 _ hk).symm
  -- call 36: tr block 11 into slot 1
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdC htl (m := m3)
    (pc0 := 3911) (r0 := 3960) (r1 := 3968) (r2 := 3982) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 11) (off := 1496) (sh := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam65_rreach [1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441])
    (fun _ => by glam65_rreach [1442, 1443, 1444, 1445])
    (fun _ => by glam65_rreach [1446, 1447, 1448, 1449, 1450, 1451] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (W_sized _ 0) hks3 hB3 (St := W s.executionEnv.calldata) (fun k hk => W_c36 _ hk)
  have hks4 : KS4 m4 (W s.executionEnv.calldata 1) := KS4.congr hks4' fun k hk => (W_c36 _ hk).symm
  -- IMGA
  have g5 : Reach (callState s 3982 [flag b] m4)
      (callState s 3991 [wd 0x14a00, wd 0, wd 800, flag b] m4) 9 := by
    glam65_rreach [1452, 1453, 1454, 1455]
  have hmc := reach_mcopy hs ⟨1456, by norm_num⟩ (pc := 3991) (d := 0x14a00) (src := 0) (n := 800)
    (rest := [flag b]) (m := m4) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by simp)
  have hfM := FrameExcept.mcopy m4 0 0x14a00 800
  refine ⟨_, KS4.frame hks4 hfM (by w_frame), fun x hx => ?_,
    hB4.frame hfM (by w_frame) (by w_frame), ?_, ?_⟩
  · rw [word_mcopy _ (by omega) (by omega), show 0 + (0x14a00 + 32 * x - 0x14a00) = KS + 32 * x by
      unfold KS; omega]
    exact hks4 x hx
  · exact ((((hf1.trans hf2).trans hf3).trans hf4).trans hfM).mono (by decide)
  · have hR := (((((g1.trans hc1).trans hR2).trans hR3).trans hR4).trans g5).trans hmc
    refine hR.mono (le_of_eq ?_)
    unfold cW1
    generalize Gas.ginit = a1; generalize Gas.trabs 5 = a2; generalize Gas.kmove = a3
    generalize Gas.kf4 = a4; generalize Gas.blk = a5
    omega

end MlDsaOptGlam65.Proofs.Exp
