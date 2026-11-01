import MlDsaOpt65.Main.S4.Round
import MlDsaOpt65.Fn.Pass3x
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # Segment `4468 … 4972`: mixed ExpandA group 7 (instances 6–8, the `tr` rider and `TRL`). -/

namespace MlDsaOpt65.Proofs

namespace S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

/-- The two padding xors of the last `pk` block (lanes 6 and 16). -/
theorem pad_words {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 192 ^^^ 559240) % 2 ^ 256) 32) 192)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 192 ^^^ 559240) % 2 ^ 256) 32) 192) 512 ^^^
        57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3 := by
  have hm : ∀ (w c : Nat), c < 2 ^ 256 → w < 2 ^ 256 → (w ^^^ c) % 2 ^ 256 = w ^^^ c :=
    fun w c hc hw => Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw hc)
  unfold KS
  by_cases h6 : x = 6
  · subst h6
    rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)),
      hm _ _ (by norm_num) (word_lt _ _)]
    congr 1
  · by_cases h16 : x = 16
    · subst h16
      rw [word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)), hm _ _ (by norm_num) (word_lt _ _),
        word_mstore_disjoint _ _ (by omega)]
      congr 1
    · rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), if_neg h6, if_neg h16,
        Nat.xor_zero, spread_zero, Nat.zero_mul, Nat.xor_zero]

set_option maxHeartbeats 1000000 in
theorem seg_g7_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvTr s.executionEnv.calldata m' ∧
      Reach (callState s 4468 [flag b] m)
        (callState s 4972 [flag (b && (okI s.executionEnv.calldata 6 && okI s.executionEnv.calldata 7 &&
          okI s.executionEnv.calldata 8))] m') Gas.pG7 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdP : CTOFF ≤ s.executionEnv.calldata.size := by unfold HDR CTOFF at *; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S0, -, hks0, h30⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_tr hs hcd hI.rho (S := S0)
    (keep := 0x8888888888888888888888888888888888888888888888888888888888888888) (kmask := 8)
    (j0 := 10) (i0 := 6) keep8
    (fun x hx => by rw [keep8]; exact ks4_and_keep hks0 8 hx)
    (fun k hk => by interval_cases k <;> decide) (fun _ => h30) (fun h => absurd h (by decide))
    (by norm_num)
    (pc0 := 4468) (r := 4529) (c0 := 34) (l4 := 0x0777770000070200000433) (b := b)
    (by decide +kernel)
    (by opt65_reach [1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := rc4_frame hI.rc4 hf1 (by s4_frame)
  -- squeezes 0 … 3 (blocks 10 … 13)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcdP (fb := flag b) (m := m1)
    (pc0 := 4529) (r0 := 4578) (r1 := 4586) (r2 := 4600) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 10) (off := 1360) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501])
    (fun _ => by opt65_reach [1502, 1503, 1504, 1505])
    (fun _ => by opt65_reach [1506, 1507, 1508, 1509, 1510, 1511] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (XT_sized _ (Itr_sized _ 6) 10 0) hks1 (Blocks.zero _ _)
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 1) :=
    ks4_congr hks2' fun k hk => permute_YT _ _ 10 0 hk
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdP (fb := flag b) (m := m2)
    (pc0 := 4600) (r0 := 4649) (r1 := 4657) (r2 := 4671) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 11) (off := 1496) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520])
    (fun _ => by opt65_reach [1521, 1522, 1523, 1524])
    (fun _ => by opt65_reach [1525, 1526, 1527, 1528, 1529, 1530] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (XT_sized _ (Itr_sized _ 6) 10 1) hks2 hB2
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 2) :=
    ks4_congr hks3' fun k hk => permute_YT _ _ 10 1 hk
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdP (fb := flag b) (m := m3)
    (pc0 := 4671) (r0 := 4720) (r1 := 4728) (r2 := 4742) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 12) (off := 1632) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539])
    (fun _ => by opt65_reach [1540, 1541, 1542, 1543])
    (fun _ => by opt65_reach [1544, 1545, 1546, 1547, 1548, 1549] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (XT_sized _ (Itr_sized _ 6) 10 2) hks3 hB3
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 3) :=
    ks4_congr hks4' fun k hk => permute_YT _ _ 10 2 hk
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcdP (fb := flag b) (m := m4)
    (pc0 := 4742) (r0 := 4791) (r1 := 4799) (r2 := 4813) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 13) (off := 1768) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558])
    (fun _ => by opt65_reach [1559, 1560, 1561, 1562])
    (fun _ => by opt65_reach [1563, 1564, 1565, 1566, 1567, 1568] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (XT_sized _ (Itr_sized _ 6) 10 3) hks4 hB4
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 4) :=
    ks4_congr hks5' fun k hk => permute_YT _ _ 10 3 hk
  -- squeeze 4: the last block (48 bytes), padding, kf4, blk 4
  have g50 : Reach (callState s 4813 [flag b] m5) (callState s 12455
      [wd 0, wd 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, wd 2, wd 3, wd 1904,
        wd 4862, flag b] m5) 29 := by
    opt65_reach [1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577]
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := 4862) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
    (off := 1904) (sh := 3) (n4 := 2)
    (lm := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) (kp := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s 4862 [flag b] mt) (callState s 21901 [wd 4923, flag b]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512))
      51 := by
    opt65_reach [1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592,
      1593] with [KS]
  have hwp := fun x (hx : x < 25) => pad_words (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(192, 192 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp : KS4 Mp (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 4) :=
    ks4_trabs_last hcdP (XT_sized _ (Itr_sized _ 6) 10 4) hks5 fun x hx => by
      rw [hwp x hx, trabs_norm hwt x hx]
  have hB5' := (hB5.frame hft (by s4_frame) (by s4_frame)).frame hfp (by s4_frame) (by s4_frame)
  have hrcp := rc4_frame (rc4_frame hrc5 hft (by s4_frame)) hfp (by s4_frame)
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs (fb := flag b) (stk := [wd 4923, flag b])
    (m := Mp) (pc0 := 21901) (r1 := 4923) (r2 := 4937) (c1 := 0) (c2 := 21) (b := 4) (by norm_num)
    (Reach.refl _) (fun _ => by opt65_reach [1594, 1595, 1596, 1597, 1598, 1599] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrcp (YT_sized _ (Itr_sized _ 6) 10 4) hksp hB5'
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata 6) 10 5) :=
    ks4_congr hks6' fun k hk => permute_YT _ _ 10 4 hk
  -- tr into TRL
  have gC : Reach (callState s 4937 [flag b] m6) (callState s 13076 [wd 8, wd 3, wd TRL, wd 4953, flag b] m6)
      24 := by
    opt65_reach [1600, 1601, 1602, 1603, 1604, 1605, 1606] with [TRL]
  obtain ⟨m7, htrl, hf7, hc7⟩ := cext_call hs (ret := 4953) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := TRL) (sh := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have hks7 := ks4_frame hks6 hf7 (by s4_frame)
  have hB7 := hB6.frame hf7 (by s4_frame) (by s4_frame)
  have hrc7 := rc4_frame hrc6 hf7 (by s4_frame)
  -- gfix 7
  have hfB : FrameExcept m1 m7 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (TRL, TRL + 256)] :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hft) hfp) hf6) hf7).mono (by decide)
  have h67 : word m7 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  obtain ⟨m8, hl8, hks8, hf8, hR8⟩ := gfix_trio hs hcd32 (i0 := 6) (j0 := 10) (fb := flag b)
    (pc := 4953) (r := 4963) (c := 18) (by opt65_reach [1607, 1608, 1609, 1610, 1611])
    (by simp only [isValidJumpDest_lit]) (by norm_num) hrc7 hks7 hB7 h67
  -- AND, pass3x7 (instances 6–8 into ACC + 0x2000)
  have gP : Reach (callState s 4963 [flag (okI s.executionEnv.calldata 6 &&
        okI s.executionEnv.calldata (6 + 1) && okI s.executionEnv.calldata (6 + 2)), flag b] m8)
      (callState s 11510 [wd 4972, flag (b && (okI s.executionEnv.calldata 6 &&
        okI s.executionEnv.calldata 7 && okI s.executionEnv.calldata 8))] m8) 18 := by
    opt65_reach [1612, 1613, 1614, 1615, 1616] with [flag, ite01_land]
  obtain ⟨m9, hacc, hf9, hc9⟩ := pass3x7_call hs (ret := 4972)
    (tail := [flag (b && (okI s.executionEnv.calldata 6 && okI s.executionEnv.calldata 7 &&
      okI s.executionEnv.calldata 8))])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
  -- frames
  have hf8' : FrameExcept m m8 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800), (TRL, TRL + 256)] :=
    (FrameExcept.trans (FrameExcept.trans hf1 hfB) hf8).mono (by decide)
  have hfA : FrameExcept m m9 (gbase ++ [(TRL, TRL + 256)]) :=
    (FrameExcept.trans hf8' hf9).mono (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m9 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  have hwA : ∀ t, t < 256 → word m8 (ACC + 0x2000 + 32 * t) = word m (ACC + 0x2000 + 32 * t) :=
    fun t ht => word_frame hf8' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000) (by s4_frame)
      (Nat.le_add_right _ _) (by omega)
  have hwZ : ∀ t, t < 256 → word m8 (ZH + 32 * t) = word m (ZH + 32 * t) :=
    fun t ht => word_frame hf8' (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 0x4000) (by s4_frame) (by omega) (by omega)
  have hwZ2 : ∀ t, t < 256 → word m8 (ZH + 0x2000 + 32 * t) = word m (ZH + 0x2000 + 32 * t) :=
    fun t ht => word_frame hf8' (a := ZH + 0x2000 + 32 * t) (lo := ZH) (hi := ZH + 0x4000) (by s4_frame) (by omega) (by omega)
  -- ACC + 0x2000
  have hacc1 : AccInst1 m9 s.executionEnv.calldata 9 :=
    accInst1_step (n := 6) (n' := 9) (by norm_num) (by norm_num) hI.acc1 hI.zhat hzh
      (D0 := fun t => ((aD s.executionEnv.calldata 4 3)[t]!).toNat * zhLane m 3 t +
        ((aD s.executionEnv.calldata 4 4)[t]!).toNat * zhLane m 4 t)
      (D1 := fun t => ((aD s.executionEnv.calldata 5 3)[t]!).toNat * zhLane m 3 t)
      (fun _ t _ => ⟨by simp only [Nat.reduceAdd, Nat.reduceDiv, accSum_succ, accSum, Nat.add_assoc, Nat.zero_add], by simp only [Nat.reduceAdd, Nat.reduceDiv, accSum_succ, accSum, Nat.add_assoc, Nat.zero_add]⟩)
      (fun hok t ht => by
        have hok' := fun i (hi : i < 9) => okIUpTo_get hok i hi
        have l0 := hl8 0 (by norm_num) (hok' 6 (by norm_num)) t ht
        have l1 := hl8 1 (by norm_num) (hok' 7 (by norm_num)) t ht
        have l2 := hl8 2 (by norm_num) (hok' 8 (by norm_num)) t ht
        simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv] at l0 l1 l2
        rw [hacc t ht, p5_eq, l0, l1, l2, hwA t ht, hwZ t ht, hwZ2 t ht,
          ← zhLane_lo (by norm_num : 3 < 4), ← zhLane_four])
  have htrl9 : TrlAt m9 s.executionEnv.calldata := by
    intro x hx
    have hf : FrameExcept m7 m9 [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800),
        (ACC + 0x2000, ACC + 0x4000)] := FrameExcept.trans hf8 hf9
    rw [word_frame hf (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by s4_frame) (by omega) (by omega),
      htrl x hx, cext_lane hks6 (by norm_num) (by omega), le64_trOf hcdP hx]
    rfl
  refine ⟨m9, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc0 hI.zMisc hI.zCw hI.zIdx hfA
    (by s4_frame) hacc1, htrl9⟩, ?_⟩
  have hR := (((((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans g50).trans hct).trans
    gpad).trans hR6).trans gC).trans hc7).trans hR8).trans gP |>.trans hc9
  exact hR.mono (by unfold Gas.pG7; omega)

end S4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- Group 7: `ginit [spread(M64) << 3, 7, 0, L4]` (slots 0–2: `A[4][3]`, `A[5][3]`, `A[4][4]`), five
rounds `trabs` (pk blocks 10–14, the last one `trabs [1904, 3, 2, …]` plus the padding
XORs) + `kf4` + `blk`, `cext [TRL, 3, 8]` (`tr`), `gfix [7]`, `AND`, `pass3x7`
(`(X & (L0|L1)) · ẑ_3 + ((X & L2) >> 128) · ẑ_4`). Proof: `S4.seg_g7_proof`. -/
theorem seg_g7 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvTr s.executionEnv.calldata m' ∧
      Reach (callState s 4468 [flag b] m)
        (callState s 4972 [flag (b && (okI s.executionEnv.calldata 6 && okI s.executionEnv.calldata 7 && okI s.executionEnv.calldata 8))] m') Gas.pG7 :=
  S4.seg_g7_proof hs hcd hI b

end MlDsaOpt65.Proofs
