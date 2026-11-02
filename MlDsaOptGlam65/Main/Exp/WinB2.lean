import MlDsaOptGlam65.Main.Exp.WinB1
import MlDsaOpt65.Main.Exp.G8Mu
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The window, calls 40, 41 (`4601 … 4870`)

`pk`'s last block (`trabs` with two groups and the two padding xors) into slot 2;
call 40 (`blk` of block 3); `cext` of `tr` to `TRL` (slot 2) and of c̃'s stream
block 0 to `CB` (slot 3); `ginit` clears slot 2; `mub0` absorbs μ's block 0 into
it (two return paths, rejoining at the `kf4` call); call 41 (`blkh` of block 4);
`cext` of c̃'s block 1 to `CB + 544` and of μ (one-block messages) to `MU`.
-/

namespace MlDsaOptGlam65.Proofs.Exp

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding Rho1At ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

theorem I5_sized (cd : ByteArray) : Sized4 (I5 cd) := fun k hk => by
  unfold I5
  by_cases h2 : k < 2
  · rw [if_pos h2]; exact W_sized _ _ k hk
  · rw [if_neg h2]; split
    · exact T_size _ _
    · exact seedState_size _ _

theorem W_c40 (cd : ByteArray) {k : Nat} (_hk : k < 4) :
    W cd 5 k = Keccak.permute (upd (I5 cd) 2
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (14 * 136) (I5 cd 2)) k) := by
  unfold upd
  by_cases h2 : k = 2
  · subst h2; rw [if_pos rfl, show I5 cd 2 = T cd 14 from by unfold I5; simp, T_succ]
    unfold W; simp
  · rw [if_neg h2]
    unfold I5 W sC
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 3) with rfl | rfl | rfl <;> simp [permN_succ, permN]

/-- μ's slot after `mub0`. -/
def muT0 (cd : ByteArray) : Fips202.SpongeState := Fips202.xorBlock 136 (padMu cd) 0 Fips202.emptyState

/-- Call 41's slots. -/
def I6 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := if k = 2 then muT0 cd else W cd 5 k

theorem I6_sized (cd : ByteArray) : Sized4 (I6 cd) := fun k hk => by
  unfold I6; split
  · unfold muT0; rw [xorBlock_size, emptyState_size]
  · exact W_sized _ _ k hk

theorem W_c41 (cd : ByteArray) {k : Nat} (_hk : k < 4) : W cd 6 k = Keccak.permute (I6 cd k) := by
  unfold I6
  by_cases h2 : k = 2
  · subst h2; simp only [if_true]; unfold W muT0
    simp only [show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide, if_false, if_true,
      show ¬ (6 : Nat) < 5 by decide, show ¬ (6 : Nat) = 5 by decide]
    rw [absorbPre_succ, Nat.zero_mul]; rfl
  · rw [if_neg h2]
    unfold W
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 3) with rfl | rfl | rfl <;> simp [permN_succ]

theorem muMsg_size' (cd : ByteArray) (hcd : HDR ≤ cd.size) :
    (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size = 66 + mlenOf cd :=
  MlDsaOpt65.Proofs.Exp.muMsg_size cd hcd

/-- `mub0`'s bytes are block 0 of `padMu`. -/
theorem le64_mu0Bytes' (cd : ByteArray) (hcd : HDR ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (mu0Bytes (trOf cd) cd) (8 * x) = le64 (padMu cd) (8 * x) := by
  unfold mu0Bytes
  split
  · rfl
  · rename_i h
    unfold padMu muIn
    rw [le64_pad_full _ (by rw [muMsg_size' cd hcd]; unfold mlenOf at *; omega)]

/-- One-block messages: μ is read off the absorbed state. -/
theorem le64_muOf_one (cd : ByteArray) (hcd : HDR ≤ cd.size) (hm : mlenOf cd ≤ 69) {x : Nat} (hx : x < 8) :
    laneOf (absorbPre 136 (padMu cd) 1) x = le64 (muOf cd) (8 * x) := by
  rw [S6Mu.le64_muOf_absorb cd hx, show S6Mu.muPad cd = padMu cd from rfl,
    absorb_eq 136 (padMu cd) 1 (by norm_num) (by
      unfold padMu; rw [pad_size 136 _ (by norm_num), muMsg_size' cd hcd]; unfold mlenOf at *; omega)]


theorem keepB : (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb : Nat) =
    il fun k => if (11 : Nat).testBit k then M64 else 0 := by decide +kernel

/-- `4601 … 4870` (the short-μ path of `mub0`'s two returns, 3 gas more). -/
def cB2 : Nat := 29 + Gas.trabs 2 + 51 + (0 + Gas.kf4 + 21 + Gas.blk) + (24 + Gas.cext 8) + (24 + Gas.cext 17) +
  24 + Gas.ginit + 21 + Gas.mub0 + (18 + Gas.kf4 + 21 + Gas.blkh) + (24 + Gas.cext 17) + (24 + Gas.cext 8)

set_option maxHeartbeats 2000000 in
theorem win_B2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (hKX : KXH m s.executionEnv.calldata 3)
    (hks : KS4 m (I5 s.executionEnv.calldata)) (b : Bool) :
    ∃ m', KS4 m' (W s.executionEnv.calldata 6) ∧
      (∀ sl, sl < 2 → SlotHead m' sl (IKX s.executionEnv.calldata sl)) ∧
      CbAt m' s.executionEnv.calldata ∧ MuAt m' s.executionEnv.calldata ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (TRL, TRL + 256),
        (CB, CB + 1088), (MU, MU + 256)] ∧
      ∃ c, c ≤ cB2 ∧ Reach (callState s 4601 [flag b] m) (callState s 4870 [flag b] m') c := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  have hcdC : CTOFF ≤ s.executionEnv.calldata.size := by unfold CTOFF; omega
  have hcdZ : Z0 ≤ s.executionEnv.calldata.size := by unfold Z0; omega
  have htl : [flag b].length ≤ 8 := by simp
  -- pk's last block into slot 2
  have g1 : Reach (callState s 4601 [flag b] m) (callState s 18543
      [wd 0, wd 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, wd 2, wd 2, wd 1904,
        wd 4650, flag b] m) 29 := by
    glam65_rreach [1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600]
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := 4650) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (off := 1904) (sh := 2) (n4 := 2) (lm := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)
    (kp := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s 4650 [flag b] mt) (callState s 41842 [wd 4711, flag b]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 279620) % 2 ^ 256) 32) 192)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 279620) % 2 ^ 256) 32) 192) 512 ^^^
          28948022309329048855892746252171976963317496166410141009864396001978282409984) % 2 ^ 256) 32) 512))
      51 := by
    glam65_rreach [1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615,
      1616] with [KS]
  have hwp := fun x (hx : x < 25) => pad_words2 (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 279620) % 2 ^ 256) 32) 192)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 192 ^^^ 279620) % 2 ^ 256) 32) 192) 512 ^^^
          28948022309329048855892746252171976963317496166410141009864396001978282409984) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(192, 192 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp := ks4_trabs_last2 hcdC (I5_sized _) hks fun x hx => by
    rw [hwp x hx, trabs_norm hwt x hx]
  -- call 40
  obtain ⟨m3, hks3', hA3, hF3, -, hf3, hR3⟩ := kbf_round hs htl (stk := [wd 4711, flag b]) (m := Mp)
    (pc0 := 41842) (r1 := 4711) (r2 := 4725) (c1 := 0) (c2 := 21) (b := 3) (by norm_num) bufOK_abuf
    (Reach.refl _)
    (fun _ => by glam65_rreach [1617, 1618, 1619, 1620, 1621, 1622] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    trivial (upd_sized (I5_sized _) (by rw [xorBlock_size]; exact I5_sized _ 2 (by norm_num))) hksp
  have h40 : ∀ k, k < 4 → Keccak.permute (upd (I5 s.executionEnv.calldata) 2
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (14 * 136)
        (I5 s.executionEnv.calldata 2)) k) = W s.executionEnv.calldata 5 k := fun k hk => (W_c40 _ hk).symm
  have hks3 : KS4 m3 (W s.executionEnv.calldata 5) := KS4.congr hks3' h40
  have hA3' : ∀ i, i < 56 → word m3 (ABUF + 1792 * 3 + 32 * i) =
      pack4 fun k => cand (W s.executionEnv.calldata 5 k) i := fun i hi => by
    rw [hA3 i hi]; exact pack4_congr fun k hk => by rw [h40 k hk]
  have hF3' : ∀ g, g < 7 → word m3 (FL + 224 * 3 + 32 * g) = flagWord (W s.executionEnv.calldata 5) g :=
    fun g hg => by rw [hF3 g hg]; exact flagWord_congr h40 g
  -- tr to TRL
  have g4 : Reach (callState s 4725 [flag b] m3)
      (callState s 18992 [wd 8, wd 2, wd TRL, wd 4741, flag b] m3) 24 := by
    glam65_rreach [1623, 1624, 1625, 1626, 1627, 1628, 1629] with [TRL]
  obtain ⟨m4, htrl, hf4, hc4⟩ := cext_call hs (ret := 4741) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := TRL) (sh := 2) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have htrl' : ∀ x, x < 8 → word m4 (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x) :=
    fun x hx => by
      rw [htrl x hx, cext_lane hks3 (by norm_num) (by omega), S4.le64_trOf hcdC hx]
      unfold W T; simp
  -- c̃'s block 0 to CB
  have g5 : Reach (callState s 4741 [flag b] m4)
      (callState s 18992 [wd 17, wd 3, wd CB, wd 4757, flag b] m4) 24 := by
    glam65_rreach [1630, 1631, 1632, 1633, 1634, 1635, 1636] with [CB]
  obtain ⟨m5, hcb1, hf5, hc5⟩ := cext_call hs (ret := 4757) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := CB) (sh := 3) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hks4 := KS4.frame hks3 hf4 (by w_frame)
  have hcbA : ∀ x, x < 17 → word m5 (CB + 32 * x) = le64 (cStream s.executionEnv.calldata) (8 * (17 * 0 + x)) :=
    fun x hx => by
      rw [hcb1 x hx, cext_lane hks4 (by norm_num) (by omega), S4.le64_cStream hcdZ (by norm_num) hx]
      unfold W sC; simp
  -- ginit: clear slot 2
  have hks5 := KS4.frame hks4 hf5 (by w_frame)
  have hrho5 := ((((hrho.frame hft (by w_frame)).frame hfp (by w_frame)).frame hf3 (by w_frame)).frame hf4
    (by w_frame)).frame hf5 (by w_frame)
  have g6 : Reach (callState s 4757 [flag b] m5)
      (callState s 17659 [wd 0, wd 0, wd 0,
        wd 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, wd 4801, flag b] m5) 24 := by
    glam65_rreach [1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644]
  obtain ⟨m6, hks6, hf6, hR6⟩ := wginit hs hrho5 (S := W s.executionEnv.calldata 5)
    (I := fun k => if k = 2 then Fips202.emptyState else W s.executionEnv.calldata 5 k)
    (kmask := 11) (amult := 0) (cmult := 0) (l4 := 0) (L := fun _ => 0)
    (by norm_num) (by norm_num) keepB
    (fun x hx => by rw [hks5 x hx, keepB, and_keep (fun k _ => cpl_lt (laneOf_lt _ _))])
    (by decide +kernel) (fun k _ => by norm_num)
    (fun k hk hb => ⟨Nat.zero_testBit k, Nat.zero_testBit k, rfl⟩)
    (fun k hk hb => by
      have : k ≠ 2 := by rintro rfl; exact absurd hb (by decide)
      simp [this])
    (fun k hk hb x hx => by
      obtain rfl : k = 2 := by interval_cases k <;> first | rfl | exact absurd hb (by decide)
      simp only [if_true]
      exact S4.freshLane_zero (Nat.zero_testBit _) (Nat.zero_testBit _) rfl x)
    g6 (by simp only [isValidJumpDest_lit]) (by norm_num)
  -- mub0: μ's block 0 into slot 2
  have g7 : Reach (callState s 4801 [flag b] m6)
      (callState s 19481 [wd 2, wd 4814, wd 4816, flag b] m6) 21 := by
    glam65_rreach [1645, 1646, 1647, 1648, 1649, 1650]
  obtain ⟨m7, hpost7, hf7, hc7⟩ := mub0_call hs (rl := 4816) (rs := 4814) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num))
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (sh := 2) (by norm_num) hcd
  have htrl6 : ∀ x, x < 8 → word m6 (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x) :=
    fun x hx => by
      rw [word_frame (hf5.trans hf6) (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by w_frame)
        (by omega) (by omega)]
      exact htrl' x hx
  have hw7 := hpost7 (trOf s.executionEnv.calldata) (S4.trOf_size _) htrl6
  have hks7 : KS4 m7 (I6 s.executionEnv.calldata) := by
    have h := ks4_xor_slot (sh := 2) (by norm_num) hks6
      (fun x => if x < 17 then le64 (mu0Bytes (trOf s.executionEnv.calldata) s.executionEnv.calldata) (8 * x)
        else 0)
      (fun x _ => by split; exact le64_lt _ _; norm_num)
      (fun x hx => by
        rw [hw7 x hx]
        split
        · rfl
        · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
      (muT0 s.executionEnv.calldata) (fun x _ => by
        unfold muT0
        rw [laneOf_xorBlock _ _ emptyState_size (by norm_num)]
        simp only [if_true]
        by_cases h : x < 17
        · rw [if_pos (by norm_num; omega), if_pos h, le64_mu0Bytes' _ hcd h, Nat.zero_add]
        · rw [if_neg (by norm_num; omega), if_neg h, Nat.xor_zero])
    exact KS4.congr h fun k _ => by unfold I6; by_cases h2 : k = 2 <;> simp [h2]
  have hR7 : ∃ c, c ≤ 18 ∧ Reach (callState s 4801 [flag b] m6) (callState s 41842 [wd 4824, flag b] m7)
      (21 + Gas.mub0 + c) := by
    by_cases hm : mlenOf s.executionEnv.calldata ≤ 69
    · rw [if_pos hm] at hc7
      have g8 : Reach (callState s 4814 [wd 4816, flag b] m7) (callState s 41842 [wd 4824, flag b] m7) 18 := by
        glam65_rreach [1651, 1652, 1653, 1654, 1655, 1656]
      exact ⟨18, le_rfl, (g7.trans hc7).trans g8⟩
    · rw [if_neg hm] at hc7
      have g8 : Reach (callState s 4816 [flag b] m7) (callState s 41842 [wd 4824, flag b] m7) 15 := by
        glam65_rreach [1653, 1654, 1655, 1656]
      exact ⟨15, by norm_num, (g7.trans hc7).trans g8⟩
  obtain ⟨c7, hc7le, hR7⟩ := hR7
  -- call 41
  obtain ⟨m8, hks8', hA8, hF8, -, hf8, hR8⟩ := kbhf_round hs htl (stk := [wd 4824, flag b]) (m := m7)
    (pc0 := 41842) (r1 := 4824) (r2 := 4838) (c1 := 0) (c2 := 21) bufOK_abuf (Reach.refl _)
    (fun _ => by glam65_rreach [1657, 1658, 1659, 1660, 1661, 1662] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    trivial (I6_sized _) hks7
  have h41 : ∀ k, k < 4 → Keccak.permute (I6 s.executionEnv.calldata k) = W s.executionEnv.calldata 6 k :=
    fun k hk => (W_c41 _ hk).symm
  have hks8 : KS4 m8 (W s.executionEnv.calldata 6) := KS4.congr hks8' h41
  -- c̃'s block 1 to CB + 544
  have g9 : Reach (callState s 4838 [flag b] m8)
      (callState s 18992 [wd 17, wd 3, wd (CB + 544), wd 4854, flag b] m8) 24 := by
    glam65_rreach [1663, 1664, 1665, 1666, 1667, 1668, 1669] with [CB]
  obtain ⟨m9, hcb2, hf9, hc9⟩ := cext_call hs (ret := 4854) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
    (dst := CB + 544) (sh := 3) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hcbB : ∀ x, x < 17 → word m9 (CB + 544 + 32 * x) =
      le64 (cStream s.executionEnv.calldata) (8 * (17 * 1 + x)) := fun x hx => by
    rw [hcb2 x hx, cext_lane hks8 (by norm_num) (by omega), S4.le64_cStream hcdZ (by norm_num) hx]
    unfold W sC; simp
  -- μ to MU
  have hks9 := KS4.frame hks8 hf9 (by w_frame)
  have g10 : Reach (callState s 4854 [flag b] m9)
      (callState s 18992 [wd 8, wd 2, wd MU, wd 4870, flag b] m9) 24 := by
    glam65_rreach [1670, 1671, 1672, 1673, 1674, 1675, 1676] with [MU]
  obtain ⟨m10, hmu, hf10, hc10⟩ := cext_call hs (ret := 4870) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m9
    (dst := MU) (sh := 2) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS MU; norm_num)
    (by unfold MU TOP; norm_num)
  -- KX's heads
  have hf3e := (((((hf4.trans hf5).trans hf6).trans hf7).trans hf8).trans hf9).trans hf10
  have hf8e := (hf9.trans hf10)
  have hKX10 := (((hKX.frame hft (by w_frame) (by w_frame)).frame hfp (by w_frame) (by w_frame)).frame
    hf3 (by w_frame) (by w_frame))
  have hsh : ∀ sl, sl < 2 → SlotHead m10 sl (IKX s.executionEnv.calldata sl) := by
    intro sl hsl
    refine ⟨fun t ht => ?_, fun g hg => ?_⟩
    · unfold candI
      rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega]
      by_cases h3 : t / 56 < 3
      · rw [wfr hf3e (ABUF + 1792 * (t / 56) + 32 * (t % 56)) (by w_frame)]
        exact hKX10.1 _ h3 _ (Nat.mod_lt _ (by norm_num)) sl hsl
      · by_cases h4 : t / 56 = 3
        · rw [h4, wfr hf3e (ABUF + 1792 * 3 + 32 * (t % 56)) (by w_frame), hA3' _ (Nat.mod_lt _ (by norm_num)),
            Fix.lane_pack4_cand _ _ (by omega), (W_KX _ hsl).2.2 (by omega) (by omega)]
        · obtain h4' : t / 56 = 4 := by omega
          rw [h4', wfr hf8e (ABUF + 1792 * 4 + 32 * (t % 56)) (by w_frame), hA8 _ (by omega),
            Fix.lane_pack4_cand _ _ (by omega), h41 sl (by omega), (W_KX _ hsl).2.2 (by omega) (by omega)]
    · rw [show FL + 32 * g = FL + 224 * (g / 7) + 32 * (g % 7) by omega]
      have e : ((List.range 8).any fun i => decide (Fips204.q ≤ candI (IKX s.executionEnv.calldata sl)
          (8 * g + i))) = ((List.range 8).any fun i => decide (Fips204.q ≤
            cand (permN (g / 7 + 1) (IKX s.executionEnv.calldata sl)) (8 * (g % 7) + i))) := by
        apply Fix.any_range_congr; intro i hi; unfold candI
        rw [show (8 * g + i) / 56 = g / 7 by omega, show (8 * g + i) % 56 = 8 * (g % 7) + i by omega]
      rw [e]
      show _ = flagOf _ _
      by_cases h3 : g / 7 < 3
      · rw [wfr hf3e (FL + 224 * (g / 7) + 32 * (g % 7)) (by w_frame)]
        exact hKX10.2 _ h3 _ (Nat.mod_lt _ (by norm_num)) sl hsl
      · by_cases h4 : g / 7 = 3
        · rw [h4, wfr hf3e (FL + 224 * 3 + 32 * (g % 7)) (by w_frame), hF3' _ (Nat.mod_lt _ (by norm_num)),
            flagBit_flagWord _ _ (by omega), (W_KX _ hsl).2.2 (by omega) (by omega)]
        · obtain h4' : g / 7 = 4 := by omega
          rw [h4', wfr hf8e (FL + 224 * 4 + 32 * (g % 7)) (by w_frame), hF8 _ (by omega),
            flagBit_flagWord _ _ (by omega), h41 sl (by omega), (W_KX _ hsl).2.2 (by omega) (by omega)]
  refine ⟨m10, KS4.frame hks9 hf10 (by w_frame), hsh, fun x hx => ?_, fun hm x hx => ?_,
    (((hft.trans hfp).trans hf3).trans hf3e).mono (by decide), ?_⟩
  · by_cases h17 : x < 17
    · rw [wfr ((((hf6.trans hf7).trans hf8).trans hf9).trans hf10) (CB + 32 * x) (by w_frame), hcbA x h17]
      congr 2; omega
    · rw [show CB + 32 * x = CB + 544 + 32 * (x - 17) by omega, wfr hf10 (CB + 544 + 32 * (x - 17)) (by w_frame),
        hcbB _ (by omega)]
      congr 2; omega
  · rw [hmu x hx, cext_lane hks9 (by norm_num) (by omega)]
    unfold W; simp only [show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide, if_true, if_false,
      show ¬ (6 : Nat) < 5 by decide, show ¬ (6 : Nat) = 5 by decide]
    exact le64_muOf_one _ hcd hm hx
  · refine ⟨_, ?_, (((((((((((((g1.trans hct).trans gpad).trans hR3).trans g4).trans hc4).trans g5).trans
      hc5).trans hR6).trans hR7).trans hR8).trans g9).trans hc9).trans g10).trans hc10⟩
    unfold cB2
    generalize Gas.trabs 2 = a1; generalize Gas.kf4 = a2; generalize Gas.blk = a3; generalize Gas.cext 8 = a4
    generalize Gas.cext 17 = a5; generalize Gas.ginit = a6; generalize Gas.mub0 = a7; generalize Gas.blkh = a8
    omega

end MlDsaOptGlam65.Proofs.Exp
