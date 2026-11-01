import MlDsaOpt65.Main.S4.Round
import MlDsaOpt65.Fn.Pass3x
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # Segment `3634 … 4033`: mixed ExpandA group 5 (instances 0–2 with the `tr` rider). -/

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
theorem seg_g5_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvG s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3634 [flag b] m)
        (callState s 4033 [flag (b && (okI s.executionEnv.calldata 0 && okI s.executionEnv.calldata 1 &&
          okI s.executionEnv.calldata 2))] m') Gas.pG5 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdP : CTOFF ≤ s.executionEnv.calldata.size := by unfold HDR CTOFF at *; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcd hI.rho (S := fun _ => Fips202.emptyState)
    (keep := 0) (kmask := 0) (j0 := 0) (i0 := 0)
    (il_eq_zero fun k _ => by simp).symm
    (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
    (fun k _ => by simp) (fun h => absurd h (by decide)) (fun _ => rfl) (by norm_num)
    (pc0 := 3634) (r := 3662) (c0 := 32) (l4 := 0x0777770000070200000004) (b := b)
    (by decide +kernel)
    (by opt65_reach [1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := rc4_frame hI.rc4 hf1 (by s4_frame)
  -- squeezes 0 … 4 (blocks 0 … 4 of the padded public key into slot 3)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcdP (fb := flag b) (m := m1)
    (pc0 := 3662) (r0 := 3709) (r1 := 3717) (r2 := 3731) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 0) (j := 0) (off := 0) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269])
    (fun _ => by opt65_reach [1270, 1271, 1272, 1273])
    (fun _ => by opt65_reach [1274, 1275, 1276, 1277, 1278, 1279] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (XT_sized _ (Itr_sized _ 0) 0 0) hks1 (Blocks.zero _ _)
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 1) :=
    ks4_congr hks2' fun k hk => permute_YT _ _ 0 0 hk
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdP (fb := flag b) (m := m2)
    (pc0 := 3731) (r0 := 3779) (r1 := 3787) (r2 := 3801) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 1) (off := 136) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288])
    (fun _ => by opt65_reach [1289, 1290, 1291, 1292])
    (fun _ => by opt65_reach [1293, 1294, 1295, 1296, 1297, 1298] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (XT_sized _ (Itr_sized _ 0) 0 1) hks2 hB2
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 2) :=
    ks4_congr hks3' fun k hk => permute_YT _ _ 0 1 hk
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdP (fb := flag b) (m := m3)
    (pc0 := 3801) (r0 := 3850) (r1 := 3858) (r2 := 3872) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 2) (off := 272) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307])
    (fun _ => by opt65_reach [1308, 1309, 1310, 1311])
    (fun _ => by opt65_reach [1312, 1313, 1314, 1315, 1316, 1317] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (XT_sized _ (Itr_sized _ 0) 0 2) hks3 hB3
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 3) :=
    ks4_congr hks4' fun k hk => permute_YT _ _ 0 2 hk
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcdP (fb := flag b) (m := m4)
    (pc0 := 3872) (r0 := 3921) (r1 := 3929) (r2 := 3943) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 3) (off := 408) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326])
    (fun _ => by opt65_reach [1327, 1328, 1329, 1330])
    (fun _ => by opt65_reach [1331, 1332, 1333, 1334, 1335, 1336] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (XT_sized _ (Itr_sized _ 0) 0 3) hks4 hB4
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 4) :=
    ks4_congr hks5' fun k hk => permute_YT _ _ 0 3 hk
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := absorb_round hs hcdP (fb := flag b) (m := m5)
    (pc0 := 3943) (r0 := 3992) (r1 := 4000) (r2 := 4014) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 4) (off := 544) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345])
    (fun _ => by opt65_reach [1346, 1347, 1348, 1349])
    (fun _ => by opt65_reach [1350, 1351, 1352, 1353, 1354, 1355] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (XT_sized _ (Itr_sized _ 0) 0 4) hks5 hB5
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 0) 0 5) :=
    ks4_congr hks6' fun k hk => permute_YT _ _ 0 4 hk
  -- gfix 7
  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4)
    hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  obtain ⟨m7, hl7, hks7, hf7, hR7⟩ := gfix_trio hs hcd32 (i0 := 0) (j0 := 0) (fb := flag b)
    (pc := 4014) (r := 4024) (c := 18) (by opt65_reach [1356, 1357, 1358, 1359, 1360])
    (by simp only [isValidJumpDest_lit]) (by norm_num) hrc6 hks6 hB6 h66
  -- AND, pass3x5 (instances 0–2 into ACC + 0x2000)
  have gP : Reach (callState s 4024 [flag (okI s.executionEnv.calldata 0 &&
        okI s.executionEnv.calldata (0 + 1) && okI s.executionEnv.calldata (0 + 2)), flag b] m7)
      (callState s 11268 [wd 4033, flag (b && (okI s.executionEnv.calldata 0 &&
        okI s.executionEnv.calldata 1 && okI s.executionEnv.calldata 2))] m7) 18 := by
    opt65_reach [1361, 1362, 1363, 1364, 1365] with [flag, ite01_land]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3x5_call hs (ret := 4033)
    (tail := [flag (b && (okI s.executionEnv.calldata 0 && okI s.executionEnv.calldata 1 &&
      okI s.executionEnv.calldata 2))])
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
  have hacc1 : AccInst1 m8 s.executionEnv.calldata 3 :=
    accInst1_step (n := 0) (n' := 3) (by norm_num) (by norm_num) (accInst1_zero hI.zAcc1) hI.zhat hzh
      (D0 := fun t => ((aD s.executionEnv.calldata 4 0)[t]!).toNat * zhLane m 0 t +
        ((aD s.executionEnv.calldata 4 1)[t]!).toNat * zhLane m 1 t)
      (D1 := fun t => ((aD s.executionEnv.calldata 5 0)[t]!).toNat * zhLane m 0 t)
      (fun _ t _ => ⟨by simp only [Nat.reduceAdd, Nat.reduceDiv, accSum_succ, accSum, Nat.add_assoc, Nat.zero_add], by simp only [Nat.reduceAdd, Nat.reduceDiv, accSum_succ, accSum, Nat.add_assoc, Nat.zero_add]⟩)
      (fun hok t ht => by
        have hok' := fun i (hi : i < 3) => okIUpTo_get hok i hi
        have l0 := hl7 0 (by norm_num) (hok' 0 (by norm_num)) t ht
        have l1 := hl7 1 (by norm_num) (hok' 1 (by norm_num)) t ht
        have l2 := hl7 2 (by norm_num) (hok' 2 (by norm_num)) t ht
        simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv] at l0 l1 l2
        rw [hacc t ht, p5_eq, l0, l1, l2, hwA t ht, hwZ t ht,
          ← zhLane_lo (by norm_num : 0 < 4), ← zhLane_lo (by norm_num : 1 < 4)])
  refine ⟨m8, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc hI.zMisc hI.zCw hI.zIdx hfA
    (by simp only [avoids_nil]) hacc1,
    trSlot_of (Itr_sized _ 0) (j0 := 0) (b := 5) (by norm_num) (ks4_frame hks7 hf8 (by s4_frame))⟩, ?_⟩
  have hR := ((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans hR7).trans gP
    |>.trans hc8
  exact hR.mono (by unfold Gas.pG5; omega)

end S4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- Group 5 (v3 schedule, `MlDsaOpt/65/layout.txt`): `HAVE6 := 0`; `ginit [0, 7, 0, L4]` with
`L4` the interleaved seeds of `A[4][0]`, `A[5][0]`, `A[4][1]` in slots 0–2 (slot 3: the `tr` sponge,
fresh); five rounds `trabs [136 b, 3, 5, …, KS]` (pk blocks 0–4 into slot 3) + `kf4` +
`blk [ABUF + 1792 b, FL + 224 b]`; `gfix [7]`, `AND`; `pass3x5` (instance `i` of slot `s`
into lane `i % 2` of `ACC + 0x2000`: `(X & (L0|L1)) · ẑ_0 + ((X & L2) >> 128) · ẑ_1`).
Proof: `S4.seg_g5_proof` (`Main/S4/Round.lean`: `ginit_tr`, `absorb_round`, `gfix_trio`,
`accInst1_step`). -/
theorem seg_g5 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvG s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3634 [flag b] m)
        (callState s 4033 [flag (b && (okI s.executionEnv.calldata 0 && okI s.executionEnv.calldata 1 && okI s.executionEnv.calldata 2))] m') Gas.pG5 :=
  S4.seg_g5_proof hs hcd hI b

end MlDsaOpt65.Proofs
