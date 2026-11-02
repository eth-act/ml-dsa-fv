import MlDsaOpt65.Main.Exp.G8Path
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # Group 8, short μ (`|M| ≤ 69`, pc 5064 → `gfix`): see `G8Path.lean` -/

namespace MlDsaOpt65.Proofs.Exp

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs
open MlDsaOpt65.Proofs.Ex
open MlDsaOpt65.Proofs.Infra

/-- Glue, rounds, `cext`s of the short path (5064 → `gfix [1]`). -/
def cShort : Nat :=
  17 + Gas.kf4 + 21 + Gas.blk + (24 + Gas.cext 17) + (24 + Gas.cext 8) + (15 + Gas.kf4 + 21 + Gas.blk) +
    (24 + Gas.cext 17) + (15 + Gas.kf4 + 21 + Gas.blk) + (15 + Gas.kf4 + 21 + Gas.blk) +
    (15 + Gas.kf4 + 21 + Gas.blkh) + 18

/-- No further absorption: the slots before round `b + 1` are those after round `b`. -/
theorem ks_keep {cd m : ByteArray} (hN : muN cd = 1) {b : Nat} (h : KS4 m (St cd b)) :
    KS4 m (Sb cd (b + 1)) :=
  KS4.congr h fun k _ => (Sb_succ_keep cd (by omega) k).symm

set_option maxHeartbeats 1000000 in
theorem g8_short {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hmN : mlenOf s.executionEnv.calldata ≤ 69) {m : ByteArray} {b : Bool} (hrc : RC4Table m)
    (hks : KS4 m (Sb s.executionEnv.calldata 0)) (h6 : word m HAVE6 = 0) :
    ∃ m', G8Mid s.executionEnv.calldata m m' ∧
      Reach (callState s 5064 [wd 7066, flag b] m) (callState s 11577 [wd 1, wd 5233, flag b] m') cShort := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hN : muN s.executionEnv.calldata = 1 := muN_short.mpr hmN
  have htl : [flag b].length ≤ 8 := by simp
  -- round 0
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs htl (stk := [wd 7066, flag b]) (m := m)
    (pc0 := 5064) (r1 := 5073) (r2 := 5087) (c1 := 17) (c2 := 21) (b := 0) (by norm_num) bufOK_abuf
    (by opt65_reach [1649, 1650, 1651, 1652, 1653])
    (fun _ => by opt65_reach [1654, 1655, 1656, 1657, 1658, 1659] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc (Sb_sized _ 0) hks (HBlocks.zero _ _ _ _) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks3 : KS4 m3 (St s.executionEnv.calldata 0) := KS4.congr hks3' fun _ _ => rfl
  -- H(c̃) block 0
  have gC1 : Reach (callState s 5087 [flag b] m3)
      (callState s 12876 [wd 17, wd 1, wd CB, wd 5103, flag b] m3) 24 := by
    opt65_reach [1660, 1661, 1662, 1663, 1664, 1665, 1666] with [CB]
  obtain ⟨m4, hcb1, hf4, hc4⟩ := cext_call hs (ret := 5103) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := CB) (sh := 1) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hcbA := cb_lane hcdN (by norm_num) hks3 hcb1
  have hks4 := KS4.frame hks3 hf4 (by g57_frame)
  -- μ
  have gC2 : Reach (callState s 5103 [flag b] m4)
      (callState s 12876 [wd 8, wd 2, wd MU, wd 5119, flag b] m4) 24 := by
    opt65_reach [1667, 1668, 1669, 1670, 1671, 1672, 1673] with [MU]
  obtain ⟨m5, hmuw, hf5, hc5⟩ := cext_call hs (ret := 5119) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := MU) (sh := 2) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS MU; norm_num)
    (by unfold MU TOP; norm_num)
  have hmu5 : ∀ x, x < 8 → word m5 (MU + 32 * x) = le64 (muOf s.executionEnv.calldata) (8 * x) :=
    fun x hx => by
      rw [hmuw x hx, cext_lane hks4 (by norm_num) (by omega),
        le64_muOf_St _ hcdN (by rw [hN]) (by norm_num) hx]
  have hks5 := KS4.frame hks4 hf5 (by g57_frame)
  have hrc5 := RC4Table.frame (RC4Table.frame hrc3 hf4 (by g57_frame)) hf5 (by g57_frame)
  have hB5 := (hB3.frame hf4 (by g57_frame) (by g57_frame)).frame hf5 (by g57_frame) (by g57_frame)
  -- round 1
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs htl (stk := [flag b]) (m := m5)
    (pc0 := 5119) (r1 := 5127) (r2 := 5141) (c1 := 15) (c2 := 21) (b := 1) (by norm_num) bufOK_abuf
    (by opt65_reach [1674, 1675, 1676, 1677])
    (fun _ => by opt65_reach [1678, 1679, 1680, 1681, 1682, 1683] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (Sb_sized _ 1) (ks_keep hN hks5) hB5 (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks6 : KS4 m6 (St s.executionEnv.calldata 1) := KS4.congr hks6' fun _ _ => rfl
  -- H(c̃) block 1
  have gC3 : Reach (callState s 5141 [flag b] m6)
      (callState s 12876 [wd 17, wd 1, wd (CB + 544), wd 5157, flag b] m6) 24 := by
    opt65_reach [1684, 1685, 1686, 1687, 1688, 1689, 1690] with [CB]
  obtain ⟨m7, hcb2, hf7, hc7⟩ := cext_call hs (ret := 5157) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := CB + 544) (sh := 1) (n := 17) (by norm_num) (by norm_num) (by norm_num)
    (by unfold KS CB; norm_num) (by unfold CB TOP; norm_num)
  have hcbB := cb_lane hcdN (by norm_num) hks6 hcb2
  have hks7 := KS4.frame hks6 hf7 (by g57_frame)
  have hrc7 := RC4Table.frame hrc6 hf7 (by g57_frame)
  have hB7 := hB6.frame hf7 (by g57_frame) (by g57_frame)
  -- rounds 2, 3, 4
  obtain ⟨m8, hks8', hB8, hrc8, hf8, hR8⟩ := kb_round hs htl (stk := [flag b]) (m := m7)
    (pc0 := 5157) (r1 := 5165) (r2 := 5179) (c1 := 15) (c2 := 21) (b := 2) (by norm_num) bufOK_abuf
    (by opt65_reach [1691, 1692, 1693, 1694])
    (fun _ => by opt65_reach [1695, 1696, 1697, 1698, 1699, 1700] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc7 (Sb_sized _ 2) (ks_keep hN hks7) hB7 (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks8 : KS4 m8 (St s.executionEnv.calldata 2) := KS4.congr hks8' fun _ _ => rfl
  obtain ⟨m9, hks9', hB9, hrc9, hf9, hR9⟩ := kb_round hs htl (stk := [flag b]) (m := m8)
    (pc0 := 5179) (r1 := 5187) (r2 := 5201) (c1 := 15) (c2 := 21) (b := 3) (by norm_num) bufOK_abuf
    (by opt65_reach [1701, 1702, 1703, 1704])
    (fun _ => by opt65_reach [1705, 1706, 1707, 1708, 1709, 1710] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc8 (Sb_sized _ 3) (ks_keep hN hks8) hB8 (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks9 : KS4 m9 (St s.executionEnv.calldata 3) := KS4.congr hks9' fun _ _ => rfl
  obtain ⟨m10, hks10', hB10, hrc10, hf10, hR10⟩ := kbh_round hs htl (stk := [flag b]) (m := m9)
    (pc0 := 5201) (r1 := 5209) (r2 := 5223) (c1 := 15) (c2 := 21) bufOK_abuf
    (by opt65_reach [1711, 1712, 1713, 1714])
    (fun _ => by opt65_reach [1715, 1716, 1717, 1718, 1719, 1720] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc9 (Sb_sized _ 4) (ks_keep hN hks9) hB9 (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks10 : KS4 m10 (St s.executionEnv.calldata 4) := KS4.congr hks10' fun _ _ => rfl
  have gG : Reach (callState s 5223 [flag b] m10) (callState s 11577 [wd 1, wd 5233, flag b] m10) 18 := by
    opt65_reach [1721, 1722, 1723, 1724, 1725]
  -- frames
  have hfA := (((((((hf3.trans hf4).trans hf5).trans hf6).trans hf7).trans hf8).trans hf9).trans hf10)
  refine ⟨m10, ⟨hks10, hB10, hrc10, ?_, ?_, ?_, hfA.mono (by decide)⟩, ?_⟩
  · rw [word_frame hfA (lo := HAVE6) (hi := HAVE6 + 32) (by g57_frame) le_rfl le_rfl]; exact h6
  · exact cb_of hcbA hcbB ((((((hf5.trans hf6).trans hf7).trans hf8).trans hf9).trans hf10))
      (by g57_frame) (((hf8.trans hf9).trans hf10)) (by g57_frame)
  · intro _ x hx
    rw [word_frame (((((hf6.trans hf7).trans hf8).trans hf9).trans hf10)) (a := MU + 32 * x) (lo := MU)
      (hi := MU + 256) (by g57_frame) (by omega) (by omega)]
    exact hmu5 x hx
  · have hR := (((((((((((hR3.trans gC1).trans hc4).trans gC2).trans hc5).trans hR6).trans gC3).trans
      hc7).trans hR8).trans hR9).trans hR10).trans gG)
    refine hR.mono (le_of_eq ?_)
    unfold cShort
    generalize Gas.kf4 = a1; generalize Gas.blk = a2; generalize Gas.blkh = a3
    generalize Gas.cext 17 = a4; generalize Gas.cext 8 = a5
    omega

end MlDsaOpt65.Proofs.Exp
