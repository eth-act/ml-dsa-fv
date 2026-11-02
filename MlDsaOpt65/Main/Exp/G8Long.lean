import MlDsaOpt65.Main.Exp.G8Path
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # Group 8, long μ (`|M| > 69`, the out-of-line region at 7066 → `gfix`): see `G8Path.lean` -/

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

/-- Glue, rounds, `cext`s and `mub`s of the long path (7066 → `gfix [1]`). -/
def cLong : Nat :=
  15 + Gas.kf4 + 21 + Gas.blk + (24 + Gas.cext 17) + (21 + Gas.mub) + (15 + Gas.kf4 + 21 + Gas.blk) +
    (24 + Gas.cext 17) + (21 + Gas.mub) + (15 + Gas.kf4 + 21 + Gas.blk) + (21 + Gas.mub) +
    (15 + Gas.kf4 + 21 + Gas.blk) + (21 + Gas.mub) + (15 + Gas.kf4 + 21 + Gas.blkh) + (21 + Gas.mub) + 18

set_option maxHeartbeats 1000000 in
theorem g8_long {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hmN : ¬ mlenOf s.executionEnv.calldata ≤ 69) {m : ByteArray} {b : Bool} (hrc : RC4Table m)
    (hks : KS4 m (Sb s.executionEnv.calldata 0)) (h6 : word m HAVE6 = 0) :
    ∃ m', G8Mid s.executionEnv.calldata m m' ∧
      Reach (callState s 7066 [flag b] m) (callState s 11577 [wd 1, wd 5233, flag b] m') cLong := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hN : 2 ≤ muN s.executionEnv.calldata := by unfold muN; omega
  have htl : [flag b].length ≤ 8 := by simp
  have hret : ∀ r : Nat, Decode.isValidJumpDest optBytecode r = true → r < 2 ^ 16 →
      RetOK Stack.mub r [flag b] := fun r hj hr => retOK_main (by decide) (by simp) hj hr
  -- round 0
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs htl (stk := [flag b]) (m := m)
    (pc0 := 7066) (r1 := 7074) (r2 := 7088) (c1 := 15) (c2 := 21) (b := 0) (by norm_num) bufOK_abuf
    (by opt65_reach [2577, 2578, 2579, 2580])
    (fun _ => by opt65_reach [2581, 2582, 2583, 2584, 2585, 2586] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc (Sb_sized _ 0) hks (HBlocks.zero _ _ _ _) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks3 : KS4 m3 (St s.executionEnv.calldata 0) := KS4.congr hks3' fun _ _ => rfl
  -- H(c̃) block 0
  have gC1 : Reach (callState s 7088 [flag b] m3)
      (callState s 12876 [wd 17, wd 1, wd CB, wd 7104, flag b] m3) 24 := by
    opt65_reach [2587, 2588, 2589, 2590, 2591, 2592, 2593] with [CB]
  obtain ⟨m4, hcb1, hf4, hc4⟩ := cext_call hs (ret := 7104) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := CB) (sh := 1) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hcbA := cb_lane hcdN (by norm_num) hks3 hcb1
  have hks4 := KS4.frame hks3 hf4 (by g57_frame)
  have hrc4 := RC4Table.frame hrc3 hf4 (by g57_frame)
  have hB4 := hB3.frame hf4 (by g57_frame) (by g57_frame)
  -- mub 136
  have gM1 : Reach (callState s 7104 [flag b] m4)
      (callState s 13737 [wd (136 * (0 + 1)), wd 2, wd 7116, flag b] m4) 21 := by
    opt65_reach [2594, 2595, 2596, 2597, 2598, 2599]
  obtain ⟨m5, hks5, hmu5, hf5, hc5⟩ := mub_step hs hcdN (hret 7116 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 0) (by norm_num) hks4 (fun h => absurd h (by omega))
  have hrc5 := RC4Table.frame hrc4 hf5 (by g57_frame)
  have hB5 := hB4.frame hf5 (by g57_frame) (by g57_frame)
  -- round 1
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs htl (stk := [flag b]) (m := m5)
    (pc0 := 7116) (r1 := 7124) (r2 := 7138) (c1 := 15) (c2 := 21) (b := 1) (by norm_num) bufOK_abuf
    (by opt65_reach [2600, 2601, 2602, 2603])
    (fun _ => by opt65_reach [2604, 2605, 2606, 2607, 2608, 2609] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (Sb_sized _ 1) hks5 hB5 (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks6 : KS4 m6 (St s.executionEnv.calldata 1) := KS4.congr hks6' fun _ _ => rfl
  have hmu6 := hmu5.frame hf6 (by g57_frame)
  -- H(c̃) block 1
  have gC3 : Reach (callState s 7138 [flag b] m6)
      (callState s 12876 [wd 17, wd 1, wd (CB + 544), wd 7154, flag b] m6) 24 := by
    opt65_reach [2610, 2611, 2612, 2613, 2614, 2615, 2616] with [CB]
  obtain ⟨m7, hcb2, hf7, hc7⟩ := cext_call hs (ret := 7154) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := CB + 544) (sh := 1) (n := 17) (by norm_num) (by norm_num) (by norm_num)
    (by unfold KS CB; norm_num) (by unfold CB TOP; norm_num)
  have hcbB := cb_lane hcdN (by norm_num) hks6 hcb2
  have hks7 := KS4.frame hks6 hf7 (by g57_frame)
  have hrc7 := RC4Table.frame hrc6 hf7 (by g57_frame)
  have hB7 := hB6.frame hf7 (by g57_frame) (by g57_frame)
  have hmu7 := hmu6.frame hf7 (by g57_frame)
  -- mub 272
  have gM2 : Reach (callState s 7154 [flag b] m7)
      (callState s 13737 [wd (136 * (1 + 1)), wd 2, wd 7167, flag b] m7) 21 := by
    opt65_reach [2617, 2618, 2619, 2620, 2621, 2622]
  obtain ⟨m8, hks8, hmu8, hf8, hc8⟩ := mub_step hs hcdN (hret 7167 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 1) (by norm_num) hks7 hmu7
  -- round 2
  obtain ⟨m9, hks9', hB9, hrc9, hf9, hR9⟩ := kb_round hs htl (stk := [flag b]) (m := m8)
    (pc0 := 7167) (r1 := 7175) (r2 := 7189) (c1 := 15) (c2 := 21) (b := 2) (by norm_num) bufOK_abuf
    (by opt65_reach [2623, 2624, 2625, 2626])
    (fun _ => by opt65_reach [2627, 2628, 2629, 2630, 2631, 2632] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc7 hf8 (by g57_frame)) (Sb_sized _ 2) hks8 (hB7.frame hf8 (by g57_frame) (by g57_frame))
    (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks9 : KS4 m9 (St s.executionEnv.calldata 2) := KS4.congr hks9' fun _ _ => rfl
  -- mub 408
  have gM3 : Reach (callState s 7189 [flag b] m9)
      (callState s 13737 [wd (136 * (2 + 1)), wd 2, wd 7202, flag b] m9) 21 := by
    opt65_reach [2633, 2634, 2635, 2636, 2637, 2638]
  obtain ⟨m10, hks10, hmu10, hf10, hc10⟩ := mub_step hs hcdN (hret 7202 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 2) (by norm_num) hks9 (hmu8.frame hf9 (by g57_frame))
  -- round 3
  obtain ⟨m11, hks11', hB11, hrc11, hf11, hR11⟩ := kb_round hs htl (stk := [flag b]) (m := m10)
    (pc0 := 7202) (r1 := 7210) (r2 := 7224) (c1 := 15) (c2 := 21) (b := 3) (by norm_num) bufOK_abuf
    (by opt65_reach [2639, 2640, 2641, 2642])
    (fun _ => by opt65_reach [2643, 2644, 2645, 2646, 2647, 2648] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc9 hf10 (by g57_frame)) (Sb_sized _ 3) hks10
    (hB9.frame hf10 (by g57_frame) (by g57_frame)) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks11 : KS4 m11 (St s.executionEnv.calldata 3) := KS4.congr hks11' fun _ _ => rfl
  -- mub 544
  have gM4 : Reach (callState s 7224 [flag b] m11)
      (callState s 13737 [wd (136 * (3 + 1)), wd 2, wd 7237, flag b] m11) 21 := by
    opt65_reach [2649, 2650, 2651, 2652, 2653, 2654]
  obtain ⟨m12, hks12, hmu12, hf12, hc12⟩ := mub_step hs hcdN (hret 7237 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 3) (by norm_num) hks11 (hmu10.frame hf11 (by g57_frame))
  -- round 4
  obtain ⟨m13, hks13', hB13, hrc13, hf13, hR13⟩ := kbh_round hs htl (stk := [flag b]) (m := m12)
    (pc0 := 7237) (r1 := 7245) (r2 := 7259) (c1 := 15) (c2 := 21) bufOK_abuf
    (by opt65_reach [2655, 2656, 2657, 2658])
    (fun _ => by opt65_reach [2659, 2660, 2661, 2662, 2663, 2664] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc11 hf12 (by g57_frame)) (Sb_sized _ 4) hks12
    (hB11.frame hf12 (by g57_frame) (by g57_frame)) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks13 : KS4 m13 (St s.executionEnv.calldata 4) := KS4.congr hks13' fun _ _ => rfl
  -- mub 680
  have gM5 : Reach (callState s 7259 [flag b] m13)
      (callState s 13737 [wd (136 * (4 + 1)), wd 2, wd 7272, flag b] m13) 21 := by
    opt65_reach [2665, 2666, 2667, 2668, 2669, 2670]
  obtain ⟨m14, hks14, hmu14, hf14, hc14⟩ := mub_step hs hcdN (hret 7272 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 4) (by norm_num) hks13 (hmu12.frame hf13 (by g57_frame))
  have gG : Reach (callState s 7272 [flag b] m14) (callState s 11577 [wd 1, wd 5233, flag b] m14) 18 := by
    opt65_reach [2671, 2672, 2673, 2674, 2675]
  -- frames
  have hfA := (((((((((((hf3.trans hf4).trans hf5).trans hf6).trans hf7).trans hf8).trans hf9).trans
    hf10).trans hf11).trans hf12).trans hf13).trans hf14)
  refine ⟨m14, ⟨KS4.congr hks14 fun k _ => Sb_succ_keep _ (by omega) k,
    hB13.frame hf14 (by g57_frame) (by g57_frame), RC4Table.frame hrc13 hf14 (by g57_frame), ?_, ?_, ?_,
    hfA.mono (by decide)⟩, ?_⟩
  · rw [word_frame hfA (lo := HAVE6) (hi := HAVE6 + 32) (by g57_frame) le_rfl le_rfl]; exact h6
  · exact cb_of hcbA hcbB (((((((((hf5.trans hf6).trans hf7).trans hf8).trans hf9).trans hf10).trans
      hf11).trans hf12).trans hf13).trans hf14) (by g57_frame)
      (((((((hf8.trans hf9).trans hf10).trans hf11).trans hf12).trans hf13).trans hf14)) (by g57_frame)
  · intro h613 x hx
    exact hmu14 (by unfold muN; omega) x hx
  · have hR := (((((((((((((((((hR3.trans gC1).trans hc4).trans gM1).trans hc5).trans hR6).trans gC3).trans
      hc7).trans gM2).trans hc8).trans hR9).trans gM3).trans hc10).trans hR11).trans gM4).trans hc12).trans
      hR13).trans gM5).trans hc14
    refine (hR.trans gG).mono (le_of_eq ?_)
    unfold cLong
    generalize Gas.kf4 = a1; generalize Gas.blk = a2; generalize Gas.blkh = a3
    generalize Gas.cext 17 = a4; generalize Gas.mub = a5
    omega

end MlDsaOpt65.Proofs.Exp
