import MlDsaOpt87.Main.S5.Round
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# Mixed group 12 of ML-DSA-87 (`4430 … 4898`, WP S5)

Slots 0–2 squeeze `A[4][5]`, `A[5][5]`, `A[6][5]`; slot 3 (kept from the
previous group) absorbs blocks 10–14 of the padded public key. Then `gfix 7`
and `pass3m` (rows 4–6 of column 5 into `ACC + 0x2000`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs.Infra

/-- Group 12's cost: glue and its calls. -/
theorem s5_g12_cost :
    407 + Gas.ginit + 5 * (Gas.trabs 5 + Gas.kf4 + Gas.blk) + Gas.gfix 3 + Gas.pass3m = Gas.pG12 := by
  unfold Gas.pG12; ring

theorem s5_seg_g12 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvT s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 6 ∧
      Reach (callState s 4430 [flag b] m)
        (callState s 4898 [flag (b && okCol s.executionEnv.calldata 1 5 3)] m') Gas.pG12 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 2592 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S, -, hksS, hS3⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := s5_ginit_keep hs hcd hI.rho hksS (col := 5) (j0 := 10)
    (l4 := 0x0777770000074200000707) (pc0 := 4430) (ret := 4490) (c0 := 33) (by norm_num) (by decide +kernel) hS3 b
    (by opt87_reach [1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m1)
    (pc0 := 4490) (r0 := 4539) (r1 := 4547) (r2 := 4561) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 10) (off := 1360) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416])
    (fun _ => by opt87_reach [1417, 1418, 1419, 1420])
    (fun _ => by opt87_reach [1421, 1422, 1423, 1424, 1425, 1426] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (s5X_sized _ 5 10 0) hks1 (S5Blocks.zero _ _)
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 5 10 b k)) (fun k _ => rfl)
  have hks2 : KS4 m2 (s5X s.executionEnv.calldata 5 10 1) :=
    s5_KS4_congr hks2' fun k hk => s5_permute_Y _ 5 10 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m2)
    (pc0 := 4561) (r0 := 4610) (r1 := 4618) (r2 := 4632) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 11) (off := 1496) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435])
    (fun _ => by opt87_reach [1436, 1437, 1438, 1439])
    (fun _ => by opt87_reach [1440, 1441, 1442, 1443, 1444, 1445] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (s5X_sized _ 5 10 1) hks2 hB2
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 5 10 b k)) (fun k _ => rfl)
  have hks3 : KS4 m3 (s5X s.executionEnv.calldata 5 10 2) :=
    s5_KS4_congr hks3' fun k hk => s5_permute_Y _ 5 10 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m3)
    (pc0 := 4632) (r0 := 4681) (r1 := 4689) (r2 := 4703) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 12) (off := 1632) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454])
    (fun _ => by opt87_reach [1455, 1456, 1457, 1458])
    (fun _ => by opt87_reach [1459, 1460, 1461, 1462, 1463, 1464] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (s5X_sized _ 5 10 2) hks3 hB3
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 5 10 b k)) (fun k _ => rfl)
  have hks4 : KS4 m4 (s5X s.executionEnv.calldata 5 10 3) :=
    s5_KS4_congr hks4' fun k hk => s5_permute_Y _ 5 10 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m4)
    (pc0 := 4703) (r0 := 4752) (r1 := 4760) (r2 := 4774) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 13) (off := 1768) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473])
    (fun _ => by opt87_reach [1474, 1475, 1476, 1477])
    (fun _ => by opt87_reach [1478, 1479, 1480, 1481, 1482, 1483] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (s5X_sized _ 5 10 3) hks4 hB4
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 5 10 b k)) (fun k _ => rfl)
  have hks5 : KS4 m5 (s5X s.executionEnv.calldata 5 10 4) :=
    s5_KS4_congr hks5' fun k hk => s5_permute_Y _ 5 10 3 hk
  -- squeeze 4
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m5)
    (pc0 := 4774) (r0 := 4823) (r1 := 4831) (r2 := 4845) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 14) (off := 1904) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492])
    (fun _ => by opt87_reach [1493, 1494, 1495, 1496])
    (fun _ => by opt87_reach [1497, 1498, 1499, 1500, 1501, 1502] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (s5X_sized _ 5 10 4) hks5 hB5
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 5 10 b k)) (fun k _ => rfl)
  have hks6 : KS4 m6 (s5X s.executionEnv.calldata 5 10 5) :=
    s5_KS4_congr hks6' fun k hk => s5_permute_Y _ 5 10 4 hk
  -- gfix 7
  have hfS := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfS (lo := HAVE6) (hi := HAVE6 + 32) (by s5_frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 4845 [flag b] m6) (callState s 12615 [wd 7, wd 4855, flag b] m6) 18 := by
    opt87_reach [1503, 1504, 1505, 1506, 1507]
  obtain ⟨m7, hlanes, hks7, -, hf7, hc7⟩ := gfix_call hs (ret := 4855) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 7) (by norm_num) 3 (by decide) (s5X s.executionEnv.calldata 5 10 5) (s5X_sized _ 5 10 5) hks6
    (fun k => if k < 3 then seedState 168 (aSeed s.executionEnv.calldata (4 + k) 5) else Fips202.emptyState)
    h66
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      simp only [if_pos hsl3]
      refine hB6.pending hsl (fun b' hb' => ?_) h66 ?_
      · show Keccak.permute (s5Y _ 5 10 b' sl) = _
        rw [s5_permute_Y _ 5 10 b' hsl]; unfold s5X; rw [if_pos hsl3]
      · unfold s5X; rw [if_pos hsl3])
  rw [s5_gfix7_flag hcd32] at hc7
  -- pass3m (rows 4..6 of column 5)
  have gP : Reach (callState s 4855 [flag (okCol s.executionEnv.calldata 1 5 3), flag b] m7)
      (callState s 12229 [wd (2 ^ 192 - 1), wd (64 * 1), wd ZH2, wd (ACC + 0x2000), wd 4897,
        flag (b && okCol s.executionEnv.calldata 1 5 3)] m7) 30 := by
    opt87_reach [1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516] with [flag, ite01_land, ZH2, ACC]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3m_call hs (ret := 4897)
    (tail := [flag (b && okCol s.executionEnv.calldata 1 5 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    (k := 1) (by norm_num) (lm := 2 ^ 192 - 1) (by norm_num) (zh := ZH2) (acc := ACC + 0x2000)
    (by unfold ZH2 ACC; norm_num) (by omega) (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 4897 [flag (b && okCol s.executionEnv.calldata 1 5 3)] m8)
      (callState s 4898 [flag (b && okCol s.executionEnv.calldata 1 5 3)] m8) 1 := by
    opt87_reach [1517]
  -- frames
  have hfA : FrameExcept m m7 GroupP.gsFrame :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans (FrameExcept.trans hf1 hfS) hf7) (by s5_sub)
  have hfG : FrameExcept m m8 (groupFrame 1) :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans hfA hf8) (by s5_sub)
  have hfW := s5_frame_widen hfG
  refine ⟨m8, ⟨⟨s5_invE_frame hI.toInvE hfW, s5_acc0_frame hI.acc0 hfW, ?_⟩, ?_⟩, ?_⟩
  · -- rows 4..6 gain column 5
    refine s5_accMid_step (by norm_num) (by norm_num) hI.acc1
      (fun k hk t ht => (hI.zhat k hk t ht).1) (s5_zh_frame hfW) fun hrows t ht => ?_
    have e1 := s5_gs_acc1 hfA ht
    have e2 : lane (word m7 (ZH2 + 32 * t)) 1 = zhLane m 5 t :=
      (s5_zhLane_hi m7 (k := 1) (by norm_num) t).symm.trans
        (s5_gs_zh hfA (by norm_num) ht)
    have e3 := s5_pass3m_rows (m6 := m7) (fun sl hsl a ha t ht => by
        have := hlanes sl (by omega) (by interval_cases sl <;> decide) a
        rw [if_pos hsl] at this
        exact this ((GroupP.aI_aSeed hcd32 _ _).trans ha) t ht) hrows ht
    rw [hacc t ht, e3, e1, e2]
  · -- the tr slot
    refine ⟨s5X s.executionEnv.calldata 5 10 5, s5X_sized _ 5 10 5,
      s5_KS4_frame hks7 hf8 (by s5_frame_tac), ?_⟩
    unfold s5X; rfl
  · have hR := (((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
      gP).trans hc8).trans gE
    exact hR.mono (by rw [← s5_g12_cost]; omega)

end MlDsaOpt87.Proofs
