import MlDsaOpt87.Main.S5.Round
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# Mixed group 11 of ML-DSA-87 (`3963 … 4430`, WP S5)

Slots 0–2 squeeze `A[4][4]`, `A[5][4]`, `A[6][4]`; slot 3 (kept from the
previous group) absorbs blocks 5–9 of the padded public key. Then `gfix 7`
and `pass3m` (rows 4–6 of column 4 into `ACC + 0x2000`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs.Infra

/-- Group 11's cost: glue and its calls. -/
theorem s5_g11_cost :
    406 + Gas.ginit + 5 * (Gas.trabs 5 + Gas.kf4 + Gas.blk) + Gas.gfix 3 + Gas.pass3m = Gas.pG11 := by
  unfold Gas.pG11; ring

theorem s5_seg_g11 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvT s.executionEnv.calldata m 4) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 5 ∧
      Reach (callState s 3963 [flag b] m)
        (callState s 4430 [flag (b && okCol s.executionEnv.calldata 1 4 3)] m') Gas.pG11 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 2592 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S, -, hksS, hS3⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := s5_ginit_keep hs hcd hI.rho hksS (col := 4) (j0 := 5)
    (l4 := 0x0777770000074200000700) (pc0 := 3963) (ret := 4023) (c0 := 33) (by norm_num) (by decide +kernel) hS3 b
    (by opt87_reach [1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m1)
    (pc0 := 4023) (r0 := 4072) (r1 := 4080) (r2 := 4094) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 5) (off := 680) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296])
    (fun _ => by opt87_reach [1297, 1298, 1299, 1300])
    (fun _ => by opt87_reach [1301, 1302, 1303, 1304, 1305, 1306] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (s5X_sized _ 4 5 0) hks1 (S5Blocks.zero _ _)
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 4 5 b k)) (fun k _ => rfl)
  have hks2 : KS4 m2 (s5X s.executionEnv.calldata 4 5 1) :=
    s5_KS4_congr hks2' fun k hk => s5_permute_Y _ 4 5 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m2)
    (pc0 := 4094) (r0 := 4143) (r1 := 4151) (r2 := 4165) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 6) (off := 816) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315])
    (fun _ => by opt87_reach [1316, 1317, 1318, 1319])
    (fun _ => by opt87_reach [1320, 1321, 1322, 1323, 1324, 1325] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (s5X_sized _ 4 5 1) hks2 hB2
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 4 5 b k)) (fun k _ => rfl)
  have hks3 : KS4 m3 (s5X s.executionEnv.calldata 4 5 2) :=
    s5_KS4_congr hks3' fun k hk => s5_permute_Y _ 4 5 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m3)
    (pc0 := 4165) (r0 := 4214) (r1 := 4222) (r2 := 4236) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 7) (off := 952) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334])
    (fun _ => by opt87_reach [1335, 1336, 1337, 1338])
    (fun _ => by opt87_reach [1339, 1340, 1341, 1342, 1343, 1344] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (s5X_sized _ 4 5 2) hks3 hB3
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 4 5 b k)) (fun k _ => rfl)
  have hks4 : KS4 m4 (s5X s.executionEnv.calldata 4 5 3) :=
    s5_KS4_congr hks4' fun k hk => s5_permute_Y _ 4 5 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m4)
    (pc0 := 4236) (r0 := 4285) (r1 := 4293) (r2 := 4307) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 8) (off := 1088) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353])
    (fun _ => by opt87_reach [1354, 1355, 1356, 1357])
    (fun _ => by opt87_reach [1358, 1359, 1360, 1361, 1362, 1363] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (s5X_sized _ 4 5 3) hks4 hB4
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 4 5 b k)) (fun k _ => rfl)
  have hks5 : KS4 m5 (s5X s.executionEnv.calldata 4 5 4) :=
    s5_KS4_congr hks5' fun k hk => s5_permute_Y _ 4 5 3 hk
  -- squeeze 4
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m5)
    (pc0 := 4307) (r0 := 4356) (r1 := 4364) (r2 := 4378) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 9) (off := 1224) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372])
    (fun _ => by opt87_reach [1373, 1374, 1375, 1376])
    (fun _ => by opt87_reach [1377, 1378, 1379, 1380, 1381, 1382] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (s5X_sized _ 4 5 4) hks5 hB5
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 4 5 b k)) (fun k _ => rfl)
  have hks6 : KS4 m6 (s5X s.executionEnv.calldata 4 5 5) :=
    s5_KS4_congr hks6' fun k hk => s5_permute_Y _ 4 5 4 hk
  -- gfix 7
  have hfS := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfS (lo := HAVE6) (hi := HAVE6 + 32) (by s5_frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 4378 [flag b] m6) (callState s 12615 [wd 7, wd 4388, flag b] m6) 18 := by
    opt87_reach [1383, 1384, 1385, 1386, 1387]
  obtain ⟨m7, hlanes, hks7, -, hf7, hc7⟩ := gfix_call hs (ret := 4388) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 7) (by norm_num) 3 (by decide) (s5X s.executionEnv.calldata 4 5 5) (s5X_sized _ 4 5 5) hks6
    (fun k => if k < 3 then seedState 168 (aSeed s.executionEnv.calldata (4 + k) 4) else Fips202.emptyState)
    h66
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      simp only [if_pos hsl3]
      refine hB6.pending hsl (fun b' hb' => ?_) h66 ?_
      · show Keccak.permute (s5Y _ 4 5 b' sl) = _
        rw [s5_permute_Y _ 4 5 b' hsl]; unfold s5X; rw [if_pos hsl3]
      · unfold s5X; rw [if_pos hsl3])
  rw [s5_gfix7_flag hcd32] at hc7
  -- pass3m (rows 4..6 of column 4)
  have gP : Reach (callState s 4388 [flag (okCol s.executionEnv.calldata 1 4 3), flag b] m7)
      (callState s 12229 [wd (2 ^ 192 - 1), wd (64 * 0), wd ZH2, wd (ACC + 0x2000), wd 4429,
        flag (b && okCol s.executionEnv.calldata 1 4 3)] m7) 29 := by
    opt87_reach [1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396] with [flag, ite01_land, ZH2, ACC]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3m_call hs (ret := 4429)
    (tail := [flag (b && okCol s.executionEnv.calldata 1 4 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    (k := 0) (by norm_num) (lm := 2 ^ 192 - 1) (by norm_num) (zh := ZH2) (acc := ACC + 0x2000)
    (by unfold ZH2 ACC; norm_num) (by omega) (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 4429 [flag (b && okCol s.executionEnv.calldata 1 4 3)] m8)
      (callState s 4430 [flag (b && okCol s.executionEnv.calldata 1 4 3)] m8) 1 := by
    opt87_reach [1397]
  -- frames
  have hfA : FrameExcept m m7 GroupP.gsFrame :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans (FrameExcept.trans hf1 hfS) hf7) (by s5_sub)
  have hfG : FrameExcept m m8 (groupFrame 1) :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans hfA hf8) (by s5_sub)
  have hfW := s5_frame_widen hfG
  refine ⟨m8, ⟨⟨s5_invE_frame hI.toInvE hfW, s5_acc0_frame hI.acc0 hfW, ?_⟩, ?_⟩, ?_⟩
  · -- rows 4..6 gain column 4
    refine s5_accMid_step (by norm_num) (by norm_num) hI.acc1
      (fun k hk t ht => (hI.zhat k hk t ht).1) (s5_zh_frame hfW) fun hrows t ht => ?_
    have e1 := s5_gs_acc1 hfA ht
    have e2 : lane (word m7 (ZH2 + 32 * t)) 0 = zhLane m 4 t :=
      (s5_zhLane_hi m7 (k := 0) (by norm_num) t).symm.trans
        (s5_gs_zh hfA (by norm_num) ht)
    have e3 := s5_pass3m_rows (m6 := m7) (fun sl hsl a ha t ht => by
        have := hlanes sl (by omega) (by interval_cases sl <;> decide) a
        rw [if_pos hsl] at this
        exact this ((GroupP.aI_aSeed hcd32 _ _).trans ha) t ht) hrows ht
    rw [hacc t ht, e3, e1, e2]
  · -- the tr slot
    refine ⟨s5X s.executionEnv.calldata 4 5 5, s5X_sized _ 4 5 5,
      s5_KS4_frame hks7 hf8 (by s5_frame_tac), ?_⟩
    unfold s5X; rfl
  · have hR := (((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
      gP).trans hc8).trans gE
    exact hR.mono (by rw [← s5_g11_cost]; omega)

end MlDsaOpt87.Proofs
