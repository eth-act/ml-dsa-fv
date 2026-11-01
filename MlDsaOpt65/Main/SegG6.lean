import MlDsaOpt65.Main.S4.Round
import MlDsaOpt65.Fn.Pass3x
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # Segment `4033 … 4468`: mixed ExpandA group 6 (instances 3–5 with the `tr` rider). -/

namespace MlDsaOpt65.Proofs

namespace S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

set_option maxHeartbeats 1000000 in
theorem seg_g6_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 2 ∧
      Reach (callState s 4033 [flag b] m)
        (callState s 4468 [flag (b && (okI s.executionEnv.calldata 3 && okI s.executionEnv.calldata 4 &&
          okI s.executionEnv.calldata 5))] m') Gas.pG6 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdP : CTOFF ≤ s.executionEnv.calldata.size := by unfold HDR CTOFF at *; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S0, -, hks0, h30⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcd hI.rho (S := S0)
    (keep := 0x8888888888888888888888888888888888888888888888888888888888888888) (kmask := 8)
    (j0 := 5) (i0 := 3) keep8
    (fun x hx => by rw [keep8]; exact ks4_and_keep hks0 8 hx)
    (fun k hk => by interval_cases k <;> decide) (fun _ => h30) (fun h => absurd h (by decide))
    (by norm_num)
    (pc0 := 4033) (r := 4094) (c0 := 34) (l4 := 0x0777770000070500000061) (b := b)
    (by decide +kernel)
    (by opt65_reach [1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := rc4_frame hI.rc4 hf1 (by s4_frame)
  -- squeezes 0 … 4 (blocks 5 … 9 of the padded public key into slot 3)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcdP (fb := flag b) (m := m1)
    (pc0 := 4094) (r0 := 4143) (r1 := 4151) (r2 := 4165) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 5) (off := 680) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385])
    (fun _ => by opt65_reach [1386, 1387, 1388, 1389])
    (fun _ => by opt65_reach [1390, 1391, 1392, 1393, 1394, 1395] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (XT_sized _ (Itr_sized _ 3) 5 0) hks1 (Blocks.zero _ _)
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 1) :=
    ks4_congr hks2' fun k hk => permute_YT _ _ 5 0 hk
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdP (fb := flag b) (m := m2)
    (pc0 := 4165) (r0 := 4214) (r1 := 4222) (r2 := 4236) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 6) (off := 816) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404])
    (fun _ => by opt65_reach [1405, 1406, 1407, 1408])
    (fun _ => by opt65_reach [1409, 1410, 1411, 1412, 1413, 1414] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (XT_sized _ (Itr_sized _ 3) 5 1) hks2 hB2
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 2) :=
    ks4_congr hks3' fun k hk => permute_YT _ _ 5 1 hk
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdP (fb := flag b) (m := m3)
    (pc0 := 4236) (r0 := 4285) (r1 := 4293) (r2 := 4307) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 7) (off := 952) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423])
    (fun _ => by opt65_reach [1424, 1425, 1426, 1427])
    (fun _ => by opt65_reach [1428, 1429, 1430, 1431, 1432, 1433] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (XT_sized _ (Itr_sized _ 3) 5 2) hks3 hB3
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 3) :=
    ks4_congr hks4' fun k hk => permute_YT _ _ 5 2 hk
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcdP (fb := flag b) (m := m4)
    (pc0 := 4307) (r0 := 4356) (r1 := 4364) (r2 := 4378) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 8) (off := 1088) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442])
    (fun _ => by opt65_reach [1443, 1444, 1445, 1446])
    (fun _ => by opt65_reach [1447, 1448, 1449, 1450, 1451, 1452] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (XT_sized _ (Itr_sized _ 3) 5 3) hks4 hB4
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 4) :=
    ks4_congr hks5' fun k hk => permute_YT _ _ 5 3 hk
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := absorb_round hs hcdP (fb := flag b) (m := m5)
    (pc0 := 4378) (r0 := 4427) (r1 := 4435) (r2 := 4449) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 9) (off := 1224) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461])
    (fun _ => by opt65_reach [1462, 1463, 1464, 1465])
    (fun _ => by opt65_reach [1466, 1467, 1468, 1469, 1470, 1471] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (XT_sized _ (Itr_sized _ 3) 5 4) hks5 hB5
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 3) 5 5) :=
    ks4_congr hks6' fun k hk => permute_YT _ _ 5 4 hk
  -- gfix 7
  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4)
    hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  obtain ⟨m7, hl7, hks7, hf7, hR7⟩ := gfix_trio hs hcd32 (i0 := 3) (j0 := 5) (fb := flag b)
    (pc := 4449) (r := 4459) (c := 18) (by opt65_reach [1472, 1473, 1474, 1475, 1476])
    (by simp only [isValidJumpDest_lit]) (by norm_num) hrc6 hks6 hB6 h66
  -- AND, pass3x6 (instances 3–5 into ACC + 0x2000)
  have gP : Reach (callState s 4459 [flag (okI s.executionEnv.calldata 3 &&
        okI s.executionEnv.calldata (3 + 1) && okI s.executionEnv.calldata (3 + 2)), flag b] m7)
      (callState s 11390 [wd 4468, flag (b && (okI s.executionEnv.calldata 3 &&
        okI s.executionEnv.calldata 4 && okI s.executionEnv.calldata 5))] m7) 18 := by
    opt65_reach [1477, 1478, 1479, 1480, 1481] with [flag, ite01_land]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3x6_call hs (ret := 4468)
    (tail := [flag (b && (okI s.executionEnv.calldata 3 && okI s.executionEnv.calldata 4 &&
      okI s.executionEnv.calldata 5))])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
  -- frames
  have hf7' : FrameExcept m m7 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800)] :=
    (FrameExcept.trans (FrameExcept.trans hf1 hfB) hf7).mono (by decide)
  have hfA : FrameExcept m m8 (gbase ++ []) :=
    (FrameExcept.trans hf7' hf8).mono (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m8 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  have hwA : ∀ t, t < 256 → word m7 (ACC + 0x2000 + 32 * t) = word m (ACC + 0x2000 + 32 * t) :=
    fun t ht => word_frame hf7' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000) (by s4_frame)
      (Nat.le_add_right _ _) (by omega)
  have hwZ : ∀ t, t < 256 → word m7 (ZH + 32 * t) = word m (ZH + 32 * t) :=
    fun t ht => word_frame hf7' (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 0x4000) (by s4_frame) (by omega) (by omega)
  -- ACC + 0x2000
  have hacc1 : AccInst1 m8 s.executionEnv.calldata 6 :=
    accInst1_step (n := 3) (n' := 6) (by norm_num) (by norm_num) hI.acc1 hI.zhat hzh
      (D0 := fun t => ((aD s.executionEnv.calldata 4 2)[t]!).toNat * zhLane m 2 t)
      (D1 := fun t => ((aD s.executionEnv.calldata 5 1)[t]!).toNat * zhLane m 1 t +
        ((aD s.executionEnv.calldata 5 2)[t]!).toNat * zhLane m 2 t)
      (fun _ t _ => ⟨by simp only [Nat.reduceAdd, Nat.reduceDiv, accSum_succ, accSum, Nat.add_assoc, Nat.zero_add], by simp only [Nat.reduceAdd, Nat.reduceDiv, accSum_succ, accSum, Nat.add_assoc, Nat.zero_add]⟩)
      (fun hok t ht => by
        have hok' := fun i (hi : i < 6) => okIUpTo_get hok i hi
        have l0 := hl7 0 (by norm_num) (hok' 3 (by norm_num)) t ht
        have l1 := hl7 1 (by norm_num) (hok' 4 (by norm_num)) t ht
        have l2 := hl7 2 (by norm_num) (hok' 5 (by norm_num)) t ht
        simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv] at l0 l1 l2
        rw [hacc t ht, p6_eq, l0, l1, l2, hwA t ht, hwZ t ht,
          ← zhLane_lo (by norm_num : 1 < 4), ← zhLane_lo (by norm_num : 2 < 4)])
  refine ⟨m8, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc0 hI.zMisc hI.zCw hI.zIdx hfA
    (by simp only [avoids_nil]) hacc1,
    trSlot_of (Itr_sized _ 3) (j0 := 5) (b := 5) (by norm_num) (ks4_frame hks7 hf8 (by s4_frame))⟩, ?_⟩
  have hR := ((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans hR7).trans gP
    |>.trans hc8
  exact hR.mono (by unfold Gas.pG6; omega)

end S4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- Group 6: `ginit [spread(M64) << 3, 7, 0, L4]` (slots 0–2: `A[5][1]`, `A[4][2]`, `A[5][2]`; slot 3
kept: the `tr` sponge), five rounds `trabs` (pk blocks 5–9) + `kf4` + `blk`, `gfix [7]`,
`AND`, `pass3x6` (`((X & L0) << 64) · ẑ_1 + ((X & (L1|L2)) >> 64) · ẑ_2`). Proof:
`S4.seg_g6_proof`. -/
theorem seg_g6 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 2 ∧
      Reach (callState s 4033 [flag b] m)
        (callState s 4468 [flag (b && (okI s.executionEnv.calldata 3 && okI s.executionEnv.calldata 4 && okI s.executionEnv.calldata 5))] m') Gas.pG6 :=
  S4.seg_g6_proof hs hcd hI b

end MlDsaOpt65.Proofs
