import MlDsaOpt65.Main.S4.Round
set_option warningAsError true
/-!
# Group 6 (`4074 … 4517`, ML-DSA-65, WP S4)

Slots 0, 1 squeeze `A[4][1]`, `A[5][1]`; slot 2 is idle (empty state); slot 3
(kept from group 5) absorbs blocks 5–9 of the padded public key. Then `gfix 3`
and `pass3 [64, ZH, ACC + 0x2000]`. `ginit_kept` (the `ginit` of groups 6 and
7, keeping slot 3) is shared with group 7.
-/

namespace MlDsaOpt65.Proofs.S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

/-- Seeds of groups 6, 7: `A[4][col]`, `A[5][col]`, an idle slot 2. -/
def Ie (cd : ByteArray) (col k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedA cd 4 col else if k = 1 then seedA cd 5 col else Fips202.emptyState

theorem Ie_sized (cd : ByteArray) (col : Nat) : ∀ k, k < 3 → (Ie cd col k).size = 25 := fun k _ => by
  unfold Ie seedA; split_ifs
  · exact seedState_size _ _
  · exact seedState_size _ _
  · exact emptyState_size

/-- `ginit` of groups 6, 7: fresh slots 0–2, slot 3 (the `tr` sponge after `j0`
blocks) kept. -/
theorem ginit_kept {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState} (hks : KS4 m S)
    {j0 : Nat} (h3 : S 3 = absorbPre 136 (padPk s.executionEnv.calldata) j0) {col : Nat} (hcol : col < 4)
    {pc0 r c0 l4 : Nat} {b : Bool}
    (hl4 : l4 = il fun k => if k < 2 then col + 256 * (4 + k) + 0x1F0000 else 0)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 11644 [wd l4, wd 0, wd 3,
        wd 0x8888888888888888888888888888888888888888888888888888888888888888, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata col) j0 0) ∧
      word m1 HAVE6 = 0 ∧ FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho h3
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  have hl4' : l4 < 2 ^ 256 := by rw [hl4]; exact il_lt _
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := r) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m0
    (keep := 0x8888888888888888888888888888888888888888888888888888888888888888) (amult := 3)
    (cmult := 0) (l4 := l4) (by norm_num) (by norm_num) (by norm_num) hl4'
  have hrho0 := Rho1At.frame hrho hf0 (by s4_frame)
  have hks0 := ks4_frame hks hf0 (by s4_frame)
  have hks1 : KS4 m1 (XT cd (Ie cd col) j0 0) :=
    ks4_ginit (kmask := 8) (L := fun k => if k < 2 then col + 256 * (4 + k) + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := S)
      (by norm_num) (by norm_num) (by decide +kernel) hl4
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x hx => ks4_and_keep hks0 8 hx)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k hk h => by
        have hk3 : k = 3 := by
          interval_cases k <;> first | rfl | exact absurd h (by decide)
        subst hk3; exact ⟨by decide, by decide, by simp⟩)
      (fun k hk h => by
        have hk3 : k = 3 := by
          interval_cases k <;> first | rfl | exact absurd h (by decide)
        subst hk3
        unfold XT
        rw [if_neg (by decide), h3, Nat.add_zero])
      (fun k hk hb' x hx => by
        have h3' : k < 3 := by
          by_contra hne
          have : k = 3 := by omega
          subst this; exact absurd hb' (by decide)
        interval_cases k
        · show _ = laneOf (seedState 168 (aSeed cd 4 col)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by omega) (by decide)
            (by decide) (by simp) hx
        · show _ = laneOf (seedState 168 (aSeed cd 5 col)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by omega) (by decide)
            (by decide) (by simp) hx
        · show _ = laneOf Fips202.emptyState x
          exact freshLane_zero (by decide) (by decide) (by simp) x)
      hg
  refine ⟨m1, hks1, by
    rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

set_option maxHeartbeats 1000000 in
theorem seg_g6_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 2 ∧
      Reach (callState s 4074 [flag b] m)
        (callState s 4517 [flag (b && okCol1 s.executionEnv.calldata 1)] m') Gas.pG6 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdP : CTOFF ≤ s.executionEnv.calldata.size := by unfold HDR CTOFF at *; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S0, -, hks0, h30⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_kept hs hcd hI.rho hks0 (j0 := 5) h30 (col := 1)
    (by norm_num) (pc0 := 4074) (r := 4134) (c0 := 33) (l4 := 0x0333330000030200000003) (b := b)
    (by decide +kernel)
    (by opt65_reach [1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := rc4_frame hI.rc4 hf1 (by s4_frame)
  -- squeezes 0 … 4 (blocks 5 … 9)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcdP (fb := flag b) (m := m1)
    (pc0 := 4134) (r0 := 4183) (r1 := 4191) (r2 := 4205) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 5) (off := 680) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402])
    (fun _ => by opt65_reach [1403, 1404, 1405, 1406])
    (fun _ => by opt65_reach [1407, 1408, 1409, 1410, 1411, 1412] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (XT_sized _ (Ie_sized _ 1) 5 0) hks1 (Blocks.zero _ _)
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 1) :=
    ks4_congr hks2' fun k hk => permute_YT _ _ 5 0 hk
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdP (fb := flag b) (m := m2)
    (pc0 := 4205) (r0 := 4254) (r1 := 4262) (r2 := 4276) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 6) (off := 816) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421])
    (fun _ => by opt65_reach [1422, 1423, 1424, 1425])
    (fun _ => by opt65_reach [1426, 1427, 1428, 1429, 1430, 1431] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (XT_sized _ (Ie_sized _ 1) 5 1) hks2 hB2
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 2) :=
    ks4_congr hks3' fun k hk => permute_YT _ _ 5 1 hk
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdP (fb := flag b) (m := m3)
    (pc0 := 4276) (r0 := 4325) (r1 := 4333) (r2 := 4347) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 7) (off := 952) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440])
    (fun _ => by opt65_reach [1441, 1442, 1443, 1444])
    (fun _ => by opt65_reach [1445, 1446, 1447, 1448, 1449, 1450] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (XT_sized _ (Ie_sized _ 1) 5 2) hks3 hB3
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 3) :=
    ks4_congr hks4' fun k hk => permute_YT _ _ 5 2 hk
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcdP (fb := flag b) (m := m4)
    (pc0 := 4347) (r0 := 4396) (r1 := 4404) (r2 := 4418) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 8) (off := 1088) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459])
    (fun _ => by opt65_reach [1460, 1461, 1462, 1463])
    (fun _ => by opt65_reach [1464, 1465, 1466, 1467, 1468, 1469] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (XT_sized _ (Ie_sized _ 1) 5 3) hks4 hB4
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 4) :=
    ks4_congr hks5' fun k hk => permute_YT _ _ 5 3 hk
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := absorb_round hs hcdP (fb := flag b) (m := m5)
    (pc0 := 4418) (r0 := 4467) (r1 := 4475) (r2 := 4489) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 9) (off := 1224) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478])
    (fun _ => by opt65_reach [1479, 1480, 1481, 1482])
    (fun _ => by opt65_reach [1483, 1484, 1485, 1486, 1487, 1488] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (XT_sized _ (Ie_sized _ 1) 5 4) hks5 hB5
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 5) :=
    ks4_congr hks6' fun k hk => permute_YT _ _ 5 4 hk
  -- gfix 3
  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4)
    hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 4489 [flag b] m6) (callState s 11314 [wd 3, wd 4499, flag b] m6) 18 := by
    opt65_reach [1489, 1490, 1491, 1492, 1493]
  obtain ⟨m7, hlanes, hks7, hkeep7, hf7, hc7⟩ := gfix_call hs (ret := 4499) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 3) (by norm_num) 2 (by decide)
    (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 1) 5 5)
    (XT_sized _ (Ie_sized _ 1) 5 5) hks6 (Ie s.executionEnv.calldata 1) h66
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      refine hB6.pending hsl (fun b' hb' => ?_) h66 ?_
      · show Keccak.permute (YT _ _ 5 b' sl) = _
        rw [permute_YT _ _ 5 b' hsl]; unfold XT; rw [if_pos hsl3]
      · unfold XT; rw [if_pos hsl3])
  rw [gfix3_flag hcd32 (I := Ie s.executionEnv.calldata 1) (col := 1) rfl rfl] at hc7
  -- pass3 (rows 4, 5 of column 1 into ACC + 0x2000)
  have gP : Reach (callState s 4499 [flag (okCol1 s.executionEnv.calldata 1), flag b] m7)
      (callState s 11032 [wd (64 * 1), wd ZH, wd (ACC + 0x2000), wd 4516,
        flag (b && okCol1 s.executionEnv.calldata 1)] m7) 27 := by
    opt65_reach [1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3_call hs (ret := 4516)
    (tail := [flag (b && okCol1 s.executionEnv.calldata 1)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    (k := 1) (zh := ZH) (acc := ACC + 0x2000) (by norm_num) (by unfold ZH ACC; norm_num) (by omega)
    (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 4516 [flag (b && okCol1 s.executionEnv.calldata 1)] m8)
      (callState s 4517 [flag (b && okCol1 s.executionEnv.calldata 1)] m8) 1 := by
    opt65_reach [1502]
  -- frames
  have hf7' : FrameExcept m m7 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800)] :=
    (FrameExcept.trans (FrameExcept.trans hf1 hfB) hf7).mono (by decide)
  have hfA : FrameExcept m m8 (gbase ++ []) :=
    (FrameExcept.trans hf7' hf8).mono (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m8 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  have hacc1 : AccCols1 m8 s.executionEnv.calldata 2 :=
    accCols1_step (n := 1) (by norm_num) hI.acc1
      (fun k hk t ht => (hI.zhat k (by omega) t ht).1) hzh
      (A := fun t => word m7 (ABUF + 32 * t))
      (gfix3_lanes hcd32 (I := Ie s.executionEnv.calldata 1) (col := 1) rfl rfl hlanes hkeep7 hB6)
      (fun t => word_lt _ _)
      (fun t ht => by
        rw [hacc t ht,
          word_frame hf7' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000)
            (by s4_frame) (Nat.le_add_right _ _) (by omega),
          word_frame hf7' (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by s4_frame)
            (by omega) (by omega)])
  refine ⟨m8, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc0 hI.zMisc hI.zCw hI.zIdx hfA
    (by simp) hacc1 (CbAt.frame hI.cb hfA (by unfold gbase; s4_frame)),
    trSlot_of (Ie_sized _ 1) (j0 := 5) (b := 5) (by norm_num) (ks4_frame hks7 hf8 (by s4_frame))⟩, ?_⟩
  have hR := ((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans
    hc7).trans gP).trans hc8 |>.trans gE
  exact hR.mono (by unfold Gas.pG6; omega)

end MlDsaOpt65.Proofs.S4
