import MlDsaOpt65.Main.S4.G6
set_option warningAsError true
/-!
# Group 7 (`4517 … 5029`, ML-DSA-65, WP S4)

Slots 0, 1 squeeze `A[4][2]`, `A[5][2]`; slot 3 (kept from group 6) absorbs
blocks 10–14 of the padded public key (the last one by `trabs 2` and the two
padding xors), whose last permutation gives `tr` (`cext` into `TRL`). Then
`gfix 3` and `pass3 [128, ZH, ACC + 0x2000]`.
-/

namespace MlDsaOpt65.Proofs.S4

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
      Reach (callState s 4517 [flag b] m)
        (callState s 5029 [flag (b && okCol1 s.executionEnv.calldata 2)] m') Gas.pG7 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdP : CTOFF ≤ s.executionEnv.calldata.size := by unfold HDR CTOFF at *; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S0, -, hks0, h30⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := ginit_kept hs hcd hI.rho hks0 (j0 := 10) h30 (col := 2)
    (by norm_num) (pc0 := 4517) (r := 4577) (c0 := 33) (l4 := 0x0333330000030200000030) (b := b)
    (by decide +kernel)
    (by opt65_reach [1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := rc4_frame hI.rc4 hf1 (by s4_frame)
  -- squeezes 0 … 3 (blocks 10 … 13)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcdP (fb := flag b) (m := m1)
    (pc0 := 4577) (r0 := 4626) (r1 := 4634) (r2 := 4648) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 10) (off := 1360) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521])
    (fun _ => by opt65_reach [1522, 1523, 1524, 1525])
    (fun _ => by opt65_reach [1526, 1527, 1528, 1529, 1530, 1531] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (XT_sized _ (Ie_sized _ 2) 10 0) hks1 (Blocks.zero _ _)
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 1) :=
    ks4_congr hks2' fun k hk => permute_YT _ _ 10 0 hk
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdP (fb := flag b) (m := m2)
    (pc0 := 4648) (r0 := 4697) (r1 := 4705) (r2 := 4719) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 11) (off := 1496) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540])
    (fun _ => by opt65_reach [1541, 1542, 1543, 1544])
    (fun _ => by opt65_reach [1545, 1546, 1547, 1548, 1549, 1550] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (XT_sized _ (Ie_sized _ 2) 10 1) hks2 hB2
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 2) :=
    ks4_congr hks3' fun k hk => permute_YT _ _ 10 1 hk
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdP (fb := flag b) (m := m3)
    (pc0 := 4719) (r0 := 4768) (r1 := 4776) (r2 := 4790) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 12) (off := 1632) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559])
    (fun _ => by opt65_reach [1560, 1561, 1562, 1563])
    (fun _ => by opt65_reach [1564, 1565, 1566, 1567, 1568, 1569] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (XT_sized _ (Ie_sized _ 2) 10 2) hks3 hB3
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 3) :=
    ks4_congr hks4' fun k hk => permute_YT _ _ 10 2 hk
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcdP (fb := flag b) (m := m4)
    (pc0 := 4790) (r0 := 4839) (r1 := 4847) (r2 := 4861) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 13) (off := 1768) (by norm_num) (by norm_num) (by norm_num)
    (by opt65_reach [1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578])
    (fun _ => by opt65_reach [1579, 1580, 1581, 1582])
    (fun _ => by opt65_reach [1583, 1584, 1585, 1586, 1587, 1588] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (XT_sized _ (Ie_sized _ 2) 10 3) hks4 hB4
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 4) :=
    ks4_congr hks5' fun k hk => permute_YT _ _ 10 3 hk
  -- squeeze 4: the last block (48 bytes), padding, kf4, blk 4
  have g50 : Reach (callState s 4861 [flag b] m5) (callState s 12084
      [wd 0, wd 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, wd 2, wd 3, wd 1904,
        wd 4910, flag b] m5) 29 := by
    opt65_reach [1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597]
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := 4910) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
    (off := 1904) (sh := 3) (n4 := 2)
    (lm := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) (kp := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s 4910 [flag b] mt) (callState s 20991 [wd 4971, flag b]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512))
      51 := by
    opt65_reach [1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612,
      1613] with [KS]
  have hwp := fun x (hx : x < 25) => pad_words (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 559240) % 2 ^ 256) 32) 192) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(192, 192 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp : KS4 Mp (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 4) :=
    ks4_trabs_last hcdP (XT_sized _ (Ie_sized _ 2) 10 4) hks5 fun x hx => by
      rw [hwp x hx, trabs_norm hwt x hx]
  have hB5' := (hB5.frame hft (by s4_frame) (by s4_frame)).frame hfp (by s4_frame) (by s4_frame)
  have hrcp := rc4_frame (rc4_frame hrc5 hft (by s4_frame)) hfp (by s4_frame)
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs (fb := flag b) (stk := [wd 4971, flag b])
    (m := Mp) (pc0 := 20991) (r1 := 4971) (r2 := 4985) (c1 := 0) (c2 := 21) (b := 4) (by norm_num)
    (Reach.refl _) (fun _ => by opt65_reach [1614, 1615, 1616, 1617, 1618, 1619] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrcp (YT_sized _ (Ie_sized _ 2) 10 4) hksp hB5'
    (St := fun b k => Keccak.permute (YT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 5) :=
    ks4_congr hks6' fun k hk => permute_YT _ _ 10 4 hk
  -- tr into TRL
  have gC : Reach (callState s 4985 [flag b] m6) (callState s 12705 [wd 8, wd 3, wd TRL, wd 5001, flag b] m6)
      24 := by
    opt65_reach [1620, 1621, 1622, 1623, 1624, 1625, 1626] with [TRL]
  obtain ⟨m7, htrl, hf7, hc7⟩ := cext_call hs (ret := 5001) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := TRL) (sh := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have hks7 := ks4_frame hks6 hf7 (by s4_frame)
  have hB7 := hB6.frame hf7 (by s4_frame) (by s4_frame)
  have hrc7 := rc4_frame hrc6 hf7 (by s4_frame)
  -- gfix 3
  have hfB : FrameExcept m1 m7 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (TRL, TRL + 256)] :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hft) hfp) hf6) hf7).mono (by decide)
  have h67 : word m7 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 5001 [flag b] m7) (callState s 11314 [wd 3, wd 5011, flag b] m7) 18 := by
    opt65_reach [1627, 1628, 1629, 1630, 1631]
  obtain ⟨m8, hlanes, hks8, hkeep8, hf8, hc8⟩ := gfix_call hs (ret := 5011) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7 hrc7
    (amask := 3) (by norm_num) 2 (by decide)
    (XT s.executionEnv.calldata (Ie s.executionEnv.calldata 2) 10 5)
    (XT_sized _ (Ie_sized _ 2) 10 5) hks7 (Ie s.executionEnv.calldata 2) h67
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      refine hB7.pending hsl (fun b' hb' => ?_) h67 ?_
      · show Keccak.permute (YT _ _ 10 b' sl) = _
        rw [permute_YT _ _ 10 b' hsl]; unfold XT; rw [if_pos hsl3]
      · unfold XT; rw [if_pos hsl3])
  rw [gfix3_flag hcd32 (I := Ie s.executionEnv.calldata 2) (col := 2) rfl rfl] at hc8
  -- pass3 (rows 4, 5 of column 2 into ACC + 0x2000)
  have gP : Reach (callState s 5011 [flag (okCol1 s.executionEnv.calldata 2), flag b] m8)
      (callState s 11032 [wd (64 * 2), wd ZH, wd (ACC + 0x2000), wd 5028,
        flag (b && okCol1 s.executionEnv.calldata 2)] m8) 27 := by
    opt65_reach [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m9, hacc, hf9, hc9⟩ := pass3_call hs (ret := 5028)
    (tail := [flag (b && okCol1 s.executionEnv.calldata 2)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
    (k := 2) (zh := ZH) (acc := ACC + 0x2000) (by norm_num) (by unfold ZH ACC; norm_num) (by omega)
    (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 5028 [flag (b && okCol1 s.executionEnv.calldata 2)] m9)
      (callState s 5029 [flag (b && okCol1 s.executionEnv.calldata 2)] m9) 1 := by
    opt65_reach [1640]
  -- frames
  have hf8' : FrameExcept m m8 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800), (TRL, TRL + 256)] :=
    (FrameExcept.trans (FrameExcept.trans hf1 hfB) hf8).mono (by decide)
  have hfA : FrameExcept m m9 (gbase ++ [(TRL, TRL + 256)]) :=
    (FrameExcept.trans hf8' hf9).mono (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m9 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  have hacc1 : AccCols1 m9 s.executionEnv.calldata 3 :=
    accCols1_step (n := 2) (by norm_num) hI.acc1
      (fun k hk t ht => (hI.zhat k (by omega) t ht).1) hzh
      (A := fun t => word m8 (ABUF + 32 * t))
      (gfix3_lanes hcd32 (I := Ie s.executionEnv.calldata 2) (col := 2) rfl rfl hlanes hkeep8 hB7)
      (fun t => word_lt _ _)
      (fun t ht => by
        rw [hacc t ht,
          word_frame hf8' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000)
            (by s4_frame) (Nat.le_add_right _ _) (by omega),
          word_frame hf8' (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by s4_frame)
            (by omega) (by omega)])
  have htrl9 : TrlAt m9 s.executionEnv.calldata := by
    intro x hx
    have hf : FrameExcept m7 m9 [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800),
        (ACC + 0x2000, ACC + 0x2000 + 8192)] := FrameExcept.trans hf8 hf9
    rw [word_frame hf (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by s4_frame) (by omega) (by omega),
      htrl x hx, cext_lane hks6 (by norm_num) (by omega), le64_trOf hcdP hx]
    rfl
  refine ⟨m9, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc0 hI.zMisc hI.zCw hI.zIdx hfA
    (by s4_frame) hacc1 (CbAt.frame hI.cb hfA (by unfold gbase; s4_frame)), htrl9⟩, ?_⟩
  have hR := (((((((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans g50).trans hct).trans
    gpad).trans hR6).trans gC).trans hc7).trans gG).trans hc8).trans gP).trans hc9 |>.trans gE
  exact hR.mono (by unfold Gas.pG7; omega)

end MlDsaOpt65.Proofs.S4
