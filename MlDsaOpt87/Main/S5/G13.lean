import MlDsaOpt87.Main.S5.Round
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# Mixed group 13 of ML-DSA-87 (`4898 … 5435`, WP S5)

Slots 0–2 squeeze `A[4][6]`, `A[5][6]`, `A[6][6]`; slot 3 (kept from the
previous group) absorbs blocks 15–19 of the padded public key (the last one with the
padding), and `cext` puts `tr` into `TRL`. Then `gfix 7`
and `pass3m` (rows 4–6 of column 6 into `ACC + 0x2000`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs.Infra

/-- Group 13's cost: glue and its calls. -/
theorem s5_g13_cost :
    467 + Gas.ginit + 4 * (Gas.trabs 5 + Gas.kf4 + Gas.blk) + (Gas.trabs 1 + Gas.kf4 + Gas.blk) +
      Gas.cext 8 + Gas.gfix 3 + Gas.pass3m = Gas.pG13 := by
  unfold Gas.pG13; ring

theorem s5_seg_g13 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvT s.executionEnv.calldata m 6) (b : Bool) :
    ∃ m', InvTr s.executionEnv.calldata m' ∧
      Reach (callState s 4898 [flag b] m)
        (callState s 5435 [flag (b && okCol s.executionEnv.calldata 1 6 3)] m') Gas.pG13 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 2592 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨S, -, hksS, hS3⟩ := hI.tr
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := s5_ginit_keep hs hcd hI.rho hksS (col := 6) (j0 := 15)
    (l4 := 0x0777770000074200000770) (pc0 := 4898) (ret := 4958) (c0 := 33) (by norm_num) (by decide +kernel) hS3 b
    (by opt87_reach [1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527] with [HAVE6])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m1)
    (pc0 := 4958) (r0 := 5007) (r1 := 5015) (r2 := 5029) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 0) (j := 15) (off := 2040) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536])
    (fun _ => by opt87_reach [1537, 1538, 1539, 1540])
    (fun _ => by opt87_reach [1541, 1542, 1543, 1544, 1545, 1546] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (s5X_sized _ 6 15 0) hks1 (S5Blocks.zero _ _)
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 6 15 b k)) (fun k _ => rfl)
  have hks2 : KS4 m2 (s5X s.executionEnv.calldata 6 15 1) :=
    s5_KS4_congr hks2' fun k hk => s5_permute_Y _ 6 15 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m2)
    (pc0 := 5029) (r0 := 5078) (r1 := 5086) (r2 := 5100) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 16) (off := 2176) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555])
    (fun _ => by opt87_reach [1556, 1557, 1558, 1559])
    (fun _ => by opt87_reach [1560, 1561, 1562, 1563, 1564, 1565] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (s5X_sized _ 6 15 1) hks2 hB2
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 6 15 b k)) (fun k _ => rfl)
  have hks3 : KS4 m3 (s5X s.executionEnv.calldata 6 15 2) :=
    s5_KS4_congr hks3' fun k hk => s5_permute_Y _ 6 15 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m3)
    (pc0 := 5100) (r0 := 5149) (r1 := 5157) (r2 := 5171) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 17) (off := 2312) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574])
    (fun _ => by opt87_reach [1575, 1576, 1577, 1578])
    (fun _ => by opt87_reach [1579, 1580, 1581, 1582, 1583, 1584] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (s5X_sized _ 6 15 2) hks3 hB3
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 6 15 b k)) (fun k _ => rfl)
  have hks4 : KS4 m4 (s5X s.executionEnv.calldata 6 15 3) :=
    s5_KS4_congr hks4' fun k hk => s5_permute_Y _ 6 15 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m4)
    (pc0 := 5171) (r0 := 5220) (r1 := 5228) (r2 := 5242) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 18) (off := 2448) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593])
    (fun _ => by opt87_reach [1594, 1595, 1596, 1597])
    (fun _ => by opt87_reach [1598, 1599, 1600, 1601, 1602, 1603] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (s5X_sized _ 6 15 3) hks4 hB4
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 6 15 b k)) (fun k _ => rfl)
  have hks5 : KS4 m5 (s5X s.executionEnv.calldata 6 15 4) :=
    s5_KS4_congr hks5' fun k hk => s5_permute_Y _ 6 15 3 hk
  -- squeeze 4: the last block 19, padding, kf4, blk 4
  have g50 : Reach (callState s 5242 [flag b] m5) (callState s 13300
      [wd 0, wd 0xffffffffffffffff000000000000000000000000000000000000000000000000, wd 1, wd 3, wd 2584,
        wd 5291, flag b] m5) 29 := by
    opt87_reach [1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612]
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := 5291) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
    (off := 2584) (sh := 3) (n4 := 1) (lm := 0xffffffffffffffff000000000000000000000000000000000000000000000000)
    (kp := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s 5291 [flag b] mt) (callState s 22461 [wd 5352, flag b]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 32 ^^^ 559240) % 2 ^ 256) 32) 32)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 32 ^^^ 559240) % 2 ^ 256) 32) 32) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512))
      51 := by
    opt87_reach [1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628] with [KS]
  have hwp := fun x (hx : x < 25) => s5_pad_words (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 32 ^^^ 559240) % 2 ^ 256) 32) 32)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 32 ^^^ 559240) % 2 ^ 256) 32) 32) 512 ^^^
          57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(32, 32 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp : KS4 Mp (s5Y s.executionEnv.calldata 6 15 4) :=
    s5_KS4_congr (s5_ks4_trabs_last hcd' (s5X_sized _ 6 15 4) hks5 fun x hx => by
      rw [hwp x hx, s5_trabs_norm hwt x hx]) fun k _ => rfl
  have hB5' := (hB5.frame hft (by s5_frame_tac) (by s5_frame_tac)).frame hfp (by s5_frame_tac)
    (by s5_frame_tac)
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := s5_kb_round hs (fb := flag b) (stk := [wd 5352, flag b])
    (m := Mp) (pc0 := 22461) (r1 := 5352) (r2 := 5366) (c1 := 0) (c2 := 21) (b := 4) (by norm_num)
    (Reach.refl _) (fun _ => by opt87_reach [1629, 1630, 1631, 1632, 1633, 1634] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame (RC4Table.frame hrc5 hft (by s5_frame_tac)) hfp (by s5_frame_tac))
    (s5Y_sized _ 6 15 4) hksp hB5'
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 6 15 b k)) (fun k _ => rfl)
  have hks6c : KS4 m6 (s5X s.executionEnv.calldata 6 15 5) :=
    s5_KS4_congr hks6' fun k hk => s5_permute_Y _ 6 15 4 hk
  -- tr into TRL
  have gC : Reach (callState s 5366 [flag b] m6)
      (callState s 13921 [wd 8, wd 3, wd TRL, wd 5382, flag b] m6) 24 := by
    opt87_reach [1635, 1636, 1637, 1638, 1639, 1640, 1641] with [TRL]
  obtain ⟨m6c, htrl, hf6c, hc6c⟩ := cext_call hs (ret := 5382) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := TRL) (sh := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have hks6 := s5_KS4_frame hks6c hf6c (by s5_frame_tac)
  have hB6c := hB6.frame hf6c (by s5_frame_tac) (by s5_frame_tac)
  have hrc6c := RC4Table.frame hrc6 hf6c (by s5_frame_tac)
  -- gfix 7
  have hfS := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
    (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hft) hfp) hf6) hf6c
  have h66 : word m6c HAVE6 = 0 := by
    rw [word_frame hfS (lo := HAVE6) (hi := HAVE6 + 32) (by s5_frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 5382 [flag b] m6c) (callState s 12615 [wd 7, wd 5392, flag b] m6c) 18 := by
    opt87_reach [1642, 1643, 1644, 1645, 1646]
  obtain ⟨m7, hlanes, hks7, -, hf7, hc7⟩ := gfix_call hs (ret := 5392) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6c hrc6c
    (amask := 7) (by norm_num) 3 (by decide) (s5X s.executionEnv.calldata 6 15 5) (s5X_sized _ 6 15 5) hks6
    (fun k => if k < 3 then seedState 168 (aSeed s.executionEnv.calldata (4 + k) 6) else Fips202.emptyState)
    h66
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      simp only [if_pos hsl3]
      refine hB6c.pending hsl (fun b' hb' => ?_) h66 ?_
      · show Keccak.permute (s5Y _ 6 15 b' sl) = _
        rw [s5_permute_Y _ 6 15 b' hsl]; unfold s5X; rw [if_pos hsl3]
      · unfold s5X; rw [if_pos hsl3])
  rw [s5_gfix7_flag hcd32] at hc7
  -- pass3m (rows 4..6 of column 6)
  have gP : Reach (callState s 5392 [flag (okCol s.executionEnv.calldata 1 6 3), flag b] m7)
      (callState s 12229 [wd (2 ^ 192 - 1), wd (64 * 2), wd ZH2, wd (ACC + 0x2000), wd 5434,
        flag (b && okCol s.executionEnv.calldata 1 6 3)] m7) 30 := by
    opt87_reach [1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655] with [flag, ite01_land, ZH2, ACC]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3m_call hs (ret := 5434)
    (tail := [flag (b && okCol s.executionEnv.calldata 1 6 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    (k := 2) (by norm_num) (lm := 2 ^ 192 - 1) (by norm_num) (zh := ZH2) (acc := ACC + 0x2000)
    (by unfold ZH2 ACC; norm_num) (by omega) (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 5434 [flag (b && okCol s.executionEnv.calldata 1 6 3)] m8)
      (callState s 5435 [flag (b && okCol s.executionEnv.calldata 1 6 3)] m8) 1 := by
    opt87_reach [1656]
  -- frames
  have hfA : FrameExcept m m7 (GroupP.gsFrame ++ [(TRL, TRL + 256)]) :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans (FrameExcept.trans hf1 hfS) hf7) (by s5_sub)
  have hfW : FrameExcept m m8 s5Frame :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans hfA hf8) (by s5_sub)
  refine ⟨m8, ⟨⟨s5_invE_frame hI.toInvE hfW, s5_acc0_frame hI.acc0 hfW, ?_⟩, ?_⟩, ?_⟩
  · -- rows 4..6 gain column 6
    refine s5_accMid_step (by norm_num) (by norm_num) hI.acc1
      (fun k hk t ht => (hI.zhat k hk t ht).1) (s5_zh_frame hfW) fun hrows t ht => ?_
    have e1 := s5_gst_acc1 hfA ht
    have e2 : lane (word m7 (ZH2 + 32 * t)) 2 = zhLane m 6 t :=
      (s5_zhLane_hi m7 (k := 2) (by norm_num) t).symm.trans
        (s5_gst_zh hfA (by norm_num) ht)
    have e3 := s5_pass3m_rows (m6 := m7) (fun sl hsl a ha t ht => by
        have := hlanes sl (by omega) (by interval_cases sl <;> decide) a
        rw [if_pos hsl] at this
        exact this ((GroupP.aI_aSeed hcd32 _ _).trans ha) t ht) hrows ht
    rw [hacc t ht, e3, e1, e2]
  · -- tr in TRL
    intro x hx
    have hfT := FrameExcept.trans hf7 hf8
    rw [word_frame hfT (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by s5_frame_tac) (by omega)
        (by omega), htrl x (by omega), cext_lane hks6c (by norm_num) (by omega), s5_le64_trOf hcd' hx]
    rfl
  · have hR := ((((((((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans g50).trans hct).trans
      gpad).trans hR6).trans gC).trans hc6c).trans gG).trans hc7).trans gP).trans hc8).trans gE
    exact hR.mono (by rw [← s5_g13_cost]; omega)

end MlDsaOpt87.Proofs
