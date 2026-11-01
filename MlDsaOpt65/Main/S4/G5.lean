import MlDsaOpt65.Main.S4.Round
set_option warningAsError true
/-!
# Group 5 (`3634 … 4074`, ML-DSA-65, WP S4)

Slots 0, 1 squeeze `A[4][0]`, `A[5][0]`; slot 2 the c̃ stream `H(c̃)` (two
blocks into `CB`); slot 3 absorbs blocks 0–4 of the padded public key (the
`tr` rider). Then `gfix 3` and `pass3 [0, ZH, ACC + 0x2000]`.
-/

namespace MlDsaOpt65.Proofs.S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

/-- Group 5's seeds: `A[4][0]`, `A[5][0]`, the c̃ seed. -/
def I5 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedA cd 4 0 else if k = 1 then seedA cd 5 0 else seedState 136 (ctOf cd)

theorem I5_sized (cd : ByteArray) : ∀ k, k < 3 → (I5 cd k).size = 25 := fun k _ => by
  unfold I5 seedA; split_ifs <;> exact seedState_size _ _

theorem g5_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 3634 [flag b] m) (callState s 3663 [flag b] m1) (33 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  have hcdZ : Z0 ≤ cd.size := by unfold HDR Z0 at *; omega
  have g0 : Reach (callState s 3634 [flag b] m)
      (callState s 11644 [wd 0x0333330000030200000000, wd 4, wd 3, wd 0, wd 3663, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 33 := by
    opt65_reach [1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 3663) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 3) (cmult := 4) (l4 := 0x0333330000030200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by s4_frame)
  have hks : KS4 m1 (XT cd (I5 cd) 0 0) :=
    ks4_ginit (kmask := 0) (L := fun k => if k < 2 then 0 + 256 * (4 + k) + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x))
      (S := XT cd (I5 cd) 0 0)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        interval_cases k
        · show _ = laneOf (seedState 168 (aSeed cd 4 0)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf (seedState 168 (aSeed cd 5 0)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf (seedState 136 (ctOf cd)) x
          exact freshLane_ctSeed hcdZ (fun _ _ => rfl) (by decide) (by decide) (by norm_num) hx
        · show _ = laneOf (absorbPre 136 (padPk cd) (0 + 0)) x
          rw [Nat.add_zero, absorbPre_zero]
          exact freshLane_zero (by decide) (by decide) (by norm_num) x)
      hg
  refine ⟨m1, hks, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

set_option maxHeartbeats 1000000 in
theorem seg_g5_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvG s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3634 [flag b] m)
        (callState s 4074 [flag (b && okCol1 s.executionEnv.calldata 0)] m') Gas.pG5 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdP : CTOFF ≤ s.executionEnv.calldata.size := by unfold HDR CTOFF at *; omega
  have hcdZ : Z0 ≤ s.executionEnv.calldata.size := by unfold HDR Z0 at *; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g5_ginit hs hcd hI.rho b
  have hrc1 := rc4_frame hI.rc4 hf1 (by s4_frame)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcdP (fb := flag b) (m := m1)
    (pc0 := 3663) (r0 := 3710) (r1 := 3718) (r2 := 3732) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 0) (j := 0) (off := 0) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269])
    (fun _ => by opt65_reach [1270, 1271, 1272, 1273])
    (fun _ => by opt65_reach [1274, 1275, 1276, 1277, 1278, 1279] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (XT_sized _ (I5_sized _) 0 0) hks1 (Blocks.zero _ _)
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 1) :=
    ks4_congr hks2' fun k hk => permute_YT _ _ 0 0 hk
  -- H(c̃) block 0 into CB
  have gC1 : Reach (callState s 3732 [flag b] m2)
      (callState s 12705 [wd 17, wd 2, wd CB, wd 3748, flag b] m2) 24 := by
    opt65_reach [1280, 1281, 1282, 1283, 1284, 1285, 1286] with [CB]
  obtain ⟨m3, hcb1, hf3, hc3⟩ := cext_call hs (ret := 3748) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2
    (dst := CB) (sh := 2) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hks3 := ks4_frame hks2 hf3 (by s4_frame)
  have hB3 := hB2.frame hf3 (by s4_frame) (by s4_frame)
  have hrc3 := rc4_frame hrc2 hf3 (by s4_frame)
  -- squeeze 1
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdP (fb := flag b) (m := m3)
    (pc0 := 3748) (r0 := 3796) (r1 := 3804) (r2 := 3818) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 1) (off := 136) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295])
    (fun _ => by opt65_reach [1296, 1297, 1298, 1299])
    (fun _ => by opt65_reach [1300, 1301, 1302, 1303, 1304, 1305] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (XT_sized _ (I5_sized _) 0 1) hks3 hB3
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 2) :=
    ks4_congr hks4' fun k hk => permute_YT _ _ 0 1 hk
  -- H(c̃) block 1 into CB + 544
  have gC2 : Reach (callState s 3818 [flag b] m4)
      (callState s 12705 [wd 17, wd 2, wd (CB + 544), wd 3834, flag b] m4) 24 := by
    opt65_reach [1306, 1307, 1308, 1309, 1310, 1311, 1312] with [CB]
  obtain ⟨m5, hcb2, hf5, hc5⟩ := cext_call hs (ret := 3834) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := CB + 544) (sh := 2) (n := 17) (by norm_num) (by norm_num) (by norm_num)
    (by unfold KS CB; norm_num) (by unfold CB TOP; norm_num)
  have hks5 := ks4_frame hks4 hf5 (by s4_frame)
  have hB5 := hB4.frame hf5 (by s4_frame) (by s4_frame)
  have hrc5 := rc4_frame hrc4 hf5 (by s4_frame)
  -- squeezes 2, 3, 4
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := absorb_round hs hcdP (fb := flag b) (m := m5)
    (pc0 := 3834) (r0 := 3883) (r1 := 3891) (r2 := 3905) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 2) (off := 272) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321])
    (fun _ => by opt65_reach [1322, 1323, 1324, 1325])
    (fun _ => by opt65_reach [1326, 1327, 1328, 1329, 1330, 1331] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (XT_sized _ (I5_sized _) 0 2) hks5 hB5
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 3) :=
    ks4_congr hks6' fun k hk => permute_YT _ _ 0 2 hk
  obtain ⟨m7, hks7', hB7, hrc7, hf7, hR7⟩ := absorb_round hs hcdP (fb := flag b) (m := m6)
    (pc0 := 3905) (r0 := 3954) (r1 := 3962) (r2 := 3976) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 3) (off := 408) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340])
    (fun _ => by opt65_reach [1341, 1342, 1343, 1344])
    (fun _ => by opt65_reach [1345, 1346, 1347, 1348, 1349, 1350] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc6 (XT_sized _ (I5_sized _) 0 3) hks6 hB6
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 b k))
    (fun k _ => rfl)
  have hks7 : KS4 m7 (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 4) :=
    ks4_congr hks7' fun k hk => permute_YT _ _ 0 3 hk
  obtain ⟨m8, hks8', hB8, hrc8, hf8, hR8⟩ := absorb_round hs hcdP (fb := flag b) (m := m7)
    (pc0 := 3976) (r0 := 4025) (r1 := 4033) (r2 := 4047) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 4) (off := 544) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359])
    (fun _ => by opt65_reach [1360, 1361, 1362, 1363])
    (fun _ => by opt65_reach [1364, 1365, 1366, 1367, 1368, 1369] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc7 (XT_sized _ (I5_sized _) 0 4) hks7 hB7
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 b k))
    (fun k _ => rfl)
  have hks8 : KS4 m8 (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 5) :=
    ks4_congr hks8' fun k hk => permute_YT _ _ 0 4 hk
  -- gfix 3
  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
    (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6) hf7) hf8
  have h68 : word m8 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 4047 [flag b] m8) (callState s 11314 [wd 3, wd 4057, flag b] m8) 18 := by
    opt65_reach [1370, 1371, 1372, 1373, 1374]
  obtain ⟨m9, hlanes, hks9, hkeep9, hf9, hc9⟩ := gfix_call hs (ret := 4057) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8 hrc8
    (amask := 3) (by norm_num) 2 (by decide) (XT s.executionEnv.calldata (I5 s.executionEnv.calldata) 0 5)
    (XT_sized _ (I5_sized _) 0 5) hks8 (I5 s.executionEnv.calldata) h68
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      refine hB8.pending hsl (fun b' hb' => ?_) h68 ?_
      · show Keccak.permute (YT _ _ 0 b' sl) = _
        rw [permute_YT _ _ 0 b' hsl]; unfold XT; rw [if_pos hsl3]
      · unfold XT; rw [if_pos hsl3])
  rw [gfix3_flag hcd32 (I := I5 s.executionEnv.calldata) (col := 0) rfl rfl] at hc9
  -- pass3 (rows 4, 5 of column 0 into ACC + 0x2000)
  have gP : Reach (callState s 4057 [flag (okCol1 s.executionEnv.calldata 0), flag b] m9)
      (callState s 11032 [wd (64 * 0), wd ZH, wd (ACC + 0x2000), wd 4073,
        flag (b && okCol1 s.executionEnv.calldata 0)] m9) 26 := by
    opt65_reach [1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m10, hacc, hf10, hc10⟩ := pass3_call hs (ret := 4073)
    (tail := [flag (b && okCol1 s.executionEnv.calldata 0)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m9
    (k := 0) (zh := ZH) (acc := ACC + 0x2000) (by norm_num) (by unfold ZH ACC; norm_num) (by omega)
    (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 4073 [flag (b && okCol1 s.executionEnv.calldata 0)] m10)
      (callState s 4074 [flag (b && okCol1 s.executionEnv.calldata 0)] m10) 1 := by
    opt65_reach [1383]
  -- frames
  have hf9' : FrameExcept m m9 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800), (CB, CB + 1088)] :=
    (FrameExcept.trans (FrameExcept.trans hf1 hfB) hf9).mono (by decide)
  have hfA : FrameExcept m m10 (gbase ++ [(CB, CB + 1088)]) :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf1 hfB) hf9) hf10).mono
      (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m10 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  -- CB survives the later calls
  have hcbw : ∀ x, x < 17 → word m10 (CB + 32 * x) = word m3 (CB + 32 * x) := fun x hx => by
    have hf : FrameExcept m3 m10 (gbase ++ [(CB + 544, CB + 1088)]) :=
      (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf4 hf5) hf6) hf7) hf8) hf9) hf10).mono
        (by unfold gbase; decide)
    exact word_frame hf (a := CB + 32 * x) (lo := CB) (hi := CB + 544) (by unfold gbase; s4_frame)
      (by omega) (by omega)
  have hcbw2 : ∀ x, x < 17 → word m10 (CB + 544 + 32 * x) = word m5 (CB + 544 + 32 * x) := fun x hx => by
    have hf : FrameExcept m5 m10 gbase :=
      (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans hf6 hf7) hf8) hf9) hf10).mono (by unfold gbase; decide)
    exact word_frame hf (a := CB + 544 + 32 * x) (lo := CB + 544) (hi := CB + 1088)
      (by unfold gbase; s4_frame) (Nat.le_add_right _ _) (by omega)
  have hcb : CbAt m10 s.executionEnv.calldata := by
    intro x hx
    by_cases h17 : x < 17
    · rw [hcbw x h17, hcb1 x h17, cext_lane hks2 (sh := 2) (x := x) (by norm_num) (by omega),
        show 8 * x = 8 * (17 * 0 + x) by omega, le64_cStream hcdZ (by norm_num) h17]
      rfl
    · have hx' : x - 17 < 17 := by omega
      rw [show CB + 32 * x = CB + 544 + 32 * (x - 17) by omega, hcbw2 _ hx', hcb2 _ hx',
        cext_lane hks4 (sh := 2) (x := x - 17) (by norm_num) (by omega),
        show 8 * x = 8 * (17 * 1 + (x - 17)) by omega, le64_cStream hcdZ (by norm_num) hx']
      rfl
  -- ACC + 0x2000
  have hacc1 : AccCols1 m10 s.executionEnv.calldata 1 :=
    accCols1_step (n := 0) (by norm_num) (accCols1_zero hI.zAcc1)
      (fun k hk t ht => (hI.zhat k (by omega) t ht).1) hzh
      (A := fun t => word m9 (ABUF + 32 * t))
      (gfix3_lanes hcd32 (I := I5 s.executionEnv.calldata) (col := 0) rfl rfl hlanes hkeep9 hB8)
      (fun t => word_lt _ _)
      (fun t ht => by
        rw [hacc t ht,
          word_frame hf9' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000)
            (by s4_frame) (Nat.le_add_right _ _) (by omega),
          word_frame hf9' (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by s4_frame)
            (by omega) (by omega)])
  refine ⟨m10, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc hI.zMisc hI.zCw hI.zIdx hfA
    (by s4_frame) hacc1 hcb,
    trSlot_of (I5_sized _) (j0 := 0) (b := 5) (by norm_num) (ks4_frame hks9 hf10 (by s4_frame))⟩, ?_⟩
  have hR := (((((((((((((hR1.trans hR2).trans gC1).trans hc3).trans hR4).trans gC2).trans hc5).trans
    hR6).trans hR7).trans hR8).trans gG).trans hc9).trans gP).trans hc10).trans gE
  exact hR.mono (by unfold Gas.pG5; omega)

end MlDsaOpt65.Proofs.S4
