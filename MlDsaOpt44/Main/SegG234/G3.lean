import MlDsaOpt44.Main.SegG234.G2
set_option warningAsError true
/-!
# Group 3 of `seg_g234` (`3898 … 4436`)

Slots 0–2 squeeze `A[0][3]`, `A[1][3]`, `A[2][3]`; slot 3 (kept from group 2)
absorbs blocks 5–9 of the padded public key, whose last permutation gives
`tr` (`cext` into `TRL`). Then `gfix 7` and `pass3m` (rows 0–2 of column 3).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- Group 3 at the start of squeeze `b`. -/
def X3 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (seedA cd k 3) else absorbPre 136 (padPk cd) (5 + b)

theorem X3_sized (cd : ByteArray) (b : Nat) : Sized4 (X3 cd b) := fun k _ => by
  unfold X3; split
  · exact permN_size (seedState_size _ _) b
  · exact absorbPre_size _ _ _

/-- After absorbing block `5 + b` into slot 3. -/
def Y3 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 3 then Fips202.xorBlock 136 (padPk cd) ((5 + b) * 136) (X3 cd b 3) else X3 cd b k

theorem Y3_sized (cd : ByteArray) (b : Nat) : Sized4 (Y3 cd b) := fun k hk => by
  unfold Y3; split
  · rw [xorBlock_size]; exact X3_sized cd b 3 (by omega)
  · exact X3_sized cd b k hk

theorem permute_Y3 (cd : ByteArray) (b : Nat) {k : Nat} (hk : k < 4) :
    Keccak.permute (Y3 cd b k) = X3 cd (b + 1) k := by
  unfold Y3 X3
  by_cases h3 : k = 3
  · subst h3; simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [show 5 + (b + 1) = (5 + b) + 1 by omega, absorbPre_succ]
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), permN_succ]

/-- Group 3's cost: glue 467 and its calls. -/
def costG3 : Nat :=
  467 + Gas.ginit + 4 * (Gas.trabs 5 + Gas.kf4 + Gas.blk) + (Gas.trabs 3 + Gas.kf4 + Gas.blk) +
    Gas.cext 8 + Gas.gfix 3 + Gas.pass3m

theorem g3_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (hks : KS4 m (X2 s.executionEnv.calldata 5)) (b : Bool) :
    ∃ m1, KS4 m1 (X3 s.executionEnv.calldata 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 3898 [flag b] m) (callState s 3959 [flag b] m1) (34 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho hks
  have g0 : Reach (callState s 3898 [flag b] m)
      (callState s 11084 [wd 0x0777770000004200000077, wd 0, wd 7,
        wd 0x8888888888888888888888888888888888888888888888888888888888888888, wd 3959, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 34 := by
    opt44_reach [1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 3959) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0x8888888888888888888888888888888888888888888888888888888888888888) (amult := 7)
    (cmult := 0) (l4 := 0x0777770000004200000077)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := hrho.frame hf0 (by avoids_tac)
  have hks0 := hks.frame hf0 (by avoids_tac)
  have hks1 : KS4 m1 (X3 cd 0) :=
    ks4_ginit (kmask := 8) (L := fun k => if k < 3 then 3 + 256 * k + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := X2 cd 5)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
      (fun x hx => (hrho0 x hx).1) (fun x hx => (hrho0 x hx).2)
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
        unfold X3 X2
        rw [if_neg (by decide), if_neg (by decide), Nat.add_zero])
      (fun k hk hb' x hx => by
        have h3 : k < 3 := by
          by_contra hne
          have : k = 3 := by omega
          subst this; exact absurd hb' (by decide)
        have e : X3 cd 0 k = seedA cd k 3 := by unfold X3; rw [if_pos h3]; rfl
        rw [e]
        exact freshLane_aSeed (by unfold HDR at hcd; omega) (fun _ _ => rfl) (by omega) (by norm_num)
          (by interval_cases k <;> decide) (by simp) (by simp [h3]) hx)
      hg
  refine ⟨m1, hks1, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- The two padding xors of the last `pk` block. -/
theorem pad_words {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 352 ^^^ 559240) % 2 ^ 256) 32) 352)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 352 ^^^ 559240) % 2 ^ 256) 32) 352) 512 ^^^
        57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3 := by
  have hm : ∀ (w c : Nat), c < 2 ^ 256 → w < 2 ^ 256 → (w ^^^ c) % 2 ^ 256 = w ^^^ c :=
    fun w c hc hw => Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw hc)
  unfold KS
  by_cases h11 : x = 11
  · subst h11
    rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)),
      hm _ _ (by norm_num) (word_lt _ _)]
    congr 1
  · by_cases h16 : x = 16
    · subst h16
      rw [word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)), hm _ _ (by norm_num) (word_lt _ _),
        word_mstore_disjoint _ _ (by omega)]
      congr 1
    · rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), if_neg h11, if_neg h16,
        Nat.xor_zero, spread_zero, Nat.zero_mul, Nat.xor_zero]

theorem seg_g3 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata)
    (hks : KS4 m (X2 s.executionEnv.calldata 5)) (b : Bool) :
    ∃ m', (∀ x, x < 8 → word m' (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x)) ∧
      RC4Table m' ∧
      (rows3 s.executionEnv.calldata 3 = true → ∀ t, t < 256 →
        word m' (ACC + 32 * t) = acc3 s.executionEnv.calldata m 3 t) ∧
      FrameExcept m m' (groupFrame ++ [(TRL, TRL + 256)]) ∧
      Reach (callState s 3898 [flag b] m)
        (callState s 4436 [flag (b && rows3 s.executionEnv.calldata 3)] m') costG3 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 1312 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g3_ginit hs hcd hrho hks b
  have hrc1 := hrc.frame hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcd' (fb := flag b) (m := m1)
    (pc0 := 3959) (r0 := 4008) (r1 := 4016) (r2 := 4030) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 5) (off := 680) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293])
    (fun _ => by opt44_reach [1294, 1295, 1296, 1297])
    (fun _ => by opt44_reach [1298, 1299, 1300, 1301, 1302, 1303] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (X3_sized _ 0) hks1 (Blocks.zero _ _) (St := fun b k => Keccak.permute (Y3 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (X3 s.executionEnv.calldata 1) :=
    hks2'.congr fun k hk => permute_Y3 _ 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcd' (fb := flag b) (m := m2)
    (pc0 := 4030) (r0 := 4079) (r1 := 4087) (r2 := 4101) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 6) (off := 816) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312])
    (fun _ => by opt44_reach [1313, 1314, 1315, 1316])
    (fun _ => by opt44_reach [1317, 1318, 1319, 1320, 1321, 1322] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X3_sized _ 1) hks2 hB2 (St := fun b k => Keccak.permute (Y3 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (X3 s.executionEnv.calldata 2) :=
    hks3'.congr fun k hk => permute_Y3 _ 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcd' (fb := flag b) (m := m3)
    (pc0 := 4101) (r0 := 4150) (r1 := 4158) (r2 := 4172) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 7) (off := 952) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331])
    (fun _ => by opt44_reach [1332, 1333, 1334, 1335])
    (fun _ => by opt44_reach [1336, 1337, 1338, 1339, 1340, 1341] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (X3_sized _ 2) hks3 hB3 (St := fun b k => Keccak.permute (Y3 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (X3 s.executionEnv.calldata 3) :=
    hks4'.congr fun k hk => permute_Y3 _ 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcd' (fb := flag b) (m := m4)
    (pc0 := 4172) (r0 := 4221) (r1 := 4229) (r2 := 4243) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 8) (off := 1088) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350])
    (fun _ => by opt44_reach [1351, 1352, 1353, 1354])
    (fun _ => by opt44_reach [1355, 1356, 1357, 1358, 1359, 1360] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (X3_sized _ 3) hks4 hB4 (St := fun b k => Keccak.permute (Y3 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (X3 s.executionEnv.calldata 4) :=
    hks5'.congr fun k hk => permute_Y3 _ 3 hk
  -- squeeze 4: the last block, padding, kf4, blk 4
  have g50 : Reach (callState s 4243 [flag b] m5) (callState s 11497
      [wd 0, wd 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000, wd 3, wd 3, wd 1224, wd 4292, flag b] m5) 29 := by
    opt44_reach [1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369]
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := 4292) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
    (off := 1224) (sh := 3) (n4 := 3) (lm := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000) (kp := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s 4292 [flag b] mt) (callState s 21570 [wd 4355, flag b]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512))
      51 := by
    opt44_reach [1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385] with [KS]
  have hwp := fun x (hx : x < 25) => pad_words (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 559240) % 2 ^ 256) 32) 352) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(352, 352 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp : KS4 Mp (Y3 s.executionEnv.calldata 4) :=
    ks4_trabs_last hcd' (X3_sized _ 4) hks5 fun x hx => by rw [hwp x hx, trabs_norm hwt x hx]
  have hB5 := (hB5.frame hft (by frame_tac) (by frame_tac)).frame hfp (by frame_tac) (by frame_tac)
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs (fb := flag b) (stk := [wd 4355, flag b])
    (m := Mp) (pc0 := 21570) (r1 := 4355) (r2 := 4369) (c1 := 0) (c2 := 21) (b := 4) (by norm_num)
    (Reach.refl _) (fun _ => by opt44_reach [1386, 1387, 1388, 1389, 1390, 1391] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    ((hrc5.frame hft (by frame_tac)).frame hfp (by frame_tac)) (Y3_sized _ 4) hksp hB5 (fun k _ => rfl)
  have hks6 : KS4 m6 (X3 s.executionEnv.calldata 5) := hks6'.congr fun k hk => permute_Y3 _ 4 hk
  -- tr into TRL
  have gC : Reach (callState s 4369 [flag b] m6) (callState s 12118 [wd 8, wd 3, wd TRL, wd 4384, flag b] m6)
      24 := by
    opt44_reach [1392, 1393, 1394, 1395, 1396, 1397, 1398] with [TRL]
  obtain ⟨m7, htrl, hf7, hc7⟩ := cext_call hs (ret := 4384) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := TRL) (sh := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have hks7 := hks6.frame hf7 (by avoids_tac)
  have hB7 := hB6.frame hf7 (by frame_tac) (by frame_tac)
  -- gfix 7
  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hft) hfp) hf6) hf7
  have h67 : word m7 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 4384 [flag b] m7) (callState s 10754 [wd 7, wd 4394, flag b] m7) 18 := by
    opt44_reach [1399, 1400, 1401, 1402, 1403]
  obtain ⟨m8, hlanes, hks8, hf8, hc8⟩ := gfix_call hs (ret := 4394) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    ((hrc6.frame hf7 (by avoids_tac)))
    (amask := 7) (by norm_num) 3 (by decide) (X3 s.executionEnv.calldata 5) (X3_sized _ 5) hks7
    (fun k => if k < 3 then seedA s.executionEnv.calldata k 3 else Fips202.emptyState) h67
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      simp only [if_pos hsl3]
      refine hB7.pending hsl (fun b' hb' => ?_) h67 ?_
      · show Keccak.permute (Y3 _ b' sl) = _
        rw [permute_Y3 _ b' hsl]; unfold X3; rw [if_pos hsl3]
      · unfold X3; rw [if_pos hsl3])
  rw [gfix7_flag hcd32] at hc8
  -- pass3m (rows 0..2 of column 3)
  have gP : Reach (callState s 4394 [flag (rows3 s.executionEnv.calldata 3), flag b] m8)
      (callState s 10344 [wd (2 ^ 192 - 1), wd (64 * 3), wd ZH, wd ACC, wd 4436,
        flag (b && rows3 s.executionEnv.calldata 3)] m8) 30 := by
    opt44_reach [1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m9, hacc, hf9, hc9⟩ := pass3m_call hs (ret := 4436)
    (tail := [flag (b && rows3 s.executionEnv.calldata 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
    (k := 3) (by norm_num) (lm := 2 ^ 192 - 1) (by norm_num)
  have hfA := FrameExcept.trans (FrameExcept.trans hf1 hfB) hf8
  refine ⟨m9, fun x hx => ?_, ((hrc6.frame hf7 (by avoids_tac)).frame hf8 (by avoids_tac)).frame hf9
      (by avoids_tac),
    fun hrows t ht => ?_, (FrameExcept.trans hfA hf9).mono (by unfold groupFrame; decide), ?_⟩
  · rw [word_frame hf9 (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by avoids_tac) (by omega) (by omega),
      word_frame hf8 (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by avoids_tac) (by omega) (by omega),
      htrl x hx, cext_lane hks6 (by norm_num) (by omega), le64_trOf hcd' hx]
    unfold X3; rfl
  · rw [hacc t ht, pass3m_rows (fun sl hsl a ha t ht => by
        have := hlanes sl (by omega) (by interval_cases sl <;> decide) a
        rw [if_pos hsl, aI_seedA hcd32] at this
        exact this ha t ht) hrows ht,
      word_frame hfA (a := ACC + 32 * t) (lo := ACC) (hi := ACC + 8192) (by frame_tac) (by omega) (by omega),
      word_frame hfA (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by frame_tac) (by omega) (by omega)]
    rfl
  · have hR := (((((((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans g50).trans hct).trans
      gpad).trans hR6).trans gC).trans hc7).trans gG).trans hc8).trans gP).trans hc9
    exact hR.mono (by unfold costG3; omega)

end MlDsaOpt44.Proofs
