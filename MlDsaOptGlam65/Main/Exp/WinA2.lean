import MlDsaOptGlam65.Main.Exp.WinA1
import MlDsaOptGlam65.Main.Exp.Acc
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # The window, calls 37–39, `gfix 12` and `pass3f7` (`3992 … 4400`): see `WinA.lean` -/

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

/-- After the second `kmove` and `ginit`: `tr` (blocks 0 … 11, permuted) in slot 0, `A54` in slot 1. -/
def I2 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then W cd 1 1 else if k = 1 then sA cd 5 4 else W cd 1 k

theorem I2_sized (cd : ByteArray) : Sized4 (I2 cd) := fun k hk => by
  unfold I2
  by_cases h0 : k = 0
  · rw [if_pos h0]; exact W_sized _ _ 1 (by omega)
  · rw [if_neg h0]; by_cases h1 : k = 1
    · rw [if_pos h1]; exact sA_size _ _ _
    · rw [if_neg h1]; exact W_sized _ _ k hk

theorem W_c37 (cd : ByteArray) {k : Nat} (_hk : k < 4) :
    W cd 2 k = Keccak.permute (upd (I2 cd) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (12 * 136) (I2 cd 0)) k) := by
  unfold upd
  by_cases h0 : k = 0
  · subst h0; rw [if_pos rfl, show I2 cd 0 = T cd 12 from by unfold I2 W; simp, T_succ]
    unfold W; simp
  · rw [if_neg h0]
    unfold I2 W
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;> simp [permN_succ, permN]

theorem W_c38 (cd : ByteArray) {k : Nat} (_hk : k < 4) :
    W cd 3 k = Keccak.permute (upd (W cd 2) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (13 * 136) (W cd 2 0)) k) := by
  unfold upd
  by_cases h0 : k = 0
  · subst h0; rw [if_pos rfl, show W cd 2 0 = T cd 13 from by unfold W; simp, T_succ]
    unfold W; simp
  · rw [if_neg h0]
    unfold W
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;> simp [permN_succ]

/-- After the third `kmove`: `A44` (×2) back in slot 0. -/
def I3 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := if k = 0 then W cd 1 0 else W cd 3 k

theorem I3_sized (cd : ByteArray) : Sized4 (I3 cd) := fun k hk => by
  unfold I3; split
  · exact W_sized _ _ 0 (by omega)
  · exact W_sized _ _ k hk

theorem W_c39 (cd : ByteArray) {k : Nat} (_hk : k < 4) : W cd 4 k = Keccak.permute (I3 cd k) := by
  unfold I3 W
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp [permN_succ]

theorem W_P (cd : ByteArray) {b sl : Nat} (hb : b < 5) (hsl : sl = 2 ∨ sl = 3) :
    W cd b sl = permN (b + 1) (IP cd sl) := by
  unfold W IP
  rcases hsl with rfl | rfl <;> simp [hb]

theorem keepE : (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : Nat) =
    il fun k => if (14 : Nat).testBit k then M64 else 0 := by decide +kernel

theorem ks4_il {m : ByteArray} {S : Nat → Fips202.SpongeState} {base : Nat} (h : St4At m base S) {x : Nat}
    (hx : x < 25) : word m (base + 32 * x) = il fun k => cpl x (laneOf (S k) x) := h x hx

/-- The second half of calls 35–41's first part (`3992 … 4400`). -/
def cW2 : Nat := 27 + Gas.kmove + 26 + Gas.ginit + (28 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) +
  (28 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) + 9 + 78 + 27 + Gas.kmove + (15 + Gas.kf4 + 21 + Gas.blk) +
  26 + Gas.gfix 2 + 18 + Gas.pass3f7



/-- `3992 … 4275`: `kmove`, `ginit` (`A54`), calls 37, 38, the image `IMGB`. -/
def cW2a : Nat := 27 + Gas.kmove + 26 + Gas.ginit + (28 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) +
  (28 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) + 9 + 78

set_option maxHeartbeats 1000000 in
theorem win_2a {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (hrc : RC4Table m)
    (hks : KS4 m (W s.executionEnv.calldata 1))
    (hB : HBlocks m ABUF FL (W s.executionEnv.calldata) 2) (b : Bool) :
    ∃ m', KS4 m' (W s.executionEnv.calldata 3) ∧ St4At m' 0x14d20 (W s.executionEnv.calldata 3) ∧
      HBlocks m' ABUF FL (W s.executionEnv.calldata) 4 ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (0x14d20, 0x14d20 + 800)] ∧
      Reach (callState s 3992 [flag b] m) (callState s 4275 [flag b] m') cW2a := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hcdC : CTOFF ≤ s.executionEnv.calldata.size := by unfold CTOFF; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  have htl : [flag b].length ≤ 8 := by simp
  -- kmove: tr (slot 1) to slot 0
  have g1 : Reach (callState s 3992 [flag b] m)
      (callState s 18099 [wd 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,
        wd 0x1111111111111111111111111111111111111111111111111111111111111111,
        wd 1, wd 0, wd 0, wd 4069, flag b] m) 27 := by
    glam65_rreach [1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464]
  obtain ⟨m1, hw1, hf1, hc1⟩ := kmove_call hs (ret := 4069) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (src := 0) (sl := 0) (sr := 1) (msk := 0x1111111111111111111111111111111111111111111111111111111111111111)
    (keep := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee) (Or.inl rfl)
    (by unfold TOP; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho1 := hrho.frame hf1 (by w_frame)
  -- ginit: A54 in slot 1
  have g2 : Reach (callState s 4069 [flag b] m1)
      (callState s 17659 [wd 0x0222220000020200000200, wd 0, wd 2,
        wd 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, wd 4125, flag b] m1) 26 := by
    glam65_rreach [1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472]
  obtain ⟨m2, hks2, hf2, hR2⟩ := wginit hs hrho1
    (S := fun k => if k = 0 then W s.executionEnv.calldata 1 1 else W s.executionEnv.calldata 1 k)
    (I := I2 s.executionEnv.calldata) (kmask := 13) (amult := 2) (cmult := 0) (l4 := 0x0222220000020200000200)
    (L := fun k => if k = 1 then 4 + 256 * 5 + 0x1F0000 else 0)
    (by norm_num) (by norm_num) keepD
    (fun x hx => by
      have h1 := hw1 x hx
      have h0 := hks x hx
      simp only [KS, Nat.zero_add] at h1 h0 ⊢
      rw [h1, h0, kmove_10 _ (fun k _ => cpl_lt (laneOf_lt _ _)), keepD,
        and_keep (fun k _ => by split <;> exact cpl_lt (laneOf_lt _ _))]
      apply il_congr; intro k hk
      by_cases h0 : k = 0
      · subst h0; simp
      · simp [h0])
    (by decide +kernel) (fun k _ => by split_ifs <;> omega)
    (fun k hk hb => by
      have : k ≠ 1 := by rintro rfl; exact absurd hb (by decide)
      exact ⟨by interval_cases k <;> first | exact absurd rfl this | decide, Nat.zero_testBit k,
        by simp [this]⟩)
    (fun k hk hb => by
      unfold I2
      have : k ≠ 1 := by rintro rfl; exact absurd hb (by decide)
      by_cases h0 : k = 0
      · simp [h0]
      · simp [h0, this])
    (fun k hk hb x hx => by
      obtain rfl : k = 1 := by interval_cases k <;> first | rfl | exact absurd hb (by decide)
      show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 5 4)) x
      exact S4.freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
        (by decide) (by simp) hx)
    g2 (by simp only [isValidJumpDest_lit]) (by norm_num)
  have hrc2 := RC4Table.frame (RC4Table.frame hrc hf1 (by w_frame)) hf2 (by w_frame)
  -- call 37: tr block 12 into slot 0
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcdC htl (m := m2)
    (pc0 := 4125) (r0 := 4173) (r1 := 4181) (r2 := 4195) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 2) (j := 12) (off := 1632) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam65_rreach [1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481])
    (fun _ => by glam65_rreach [1482, 1483, 1484, 1485])
    (fun _ => by glam65_rreach [1486, 1487, 1488, 1489, 1490, 1491] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (I2_sized _) hks2 ((hB.frame hf1 (by w_frame) (by w_frame)).frame hf2 (by w_frame) (by w_frame))
    (St := W s.executionEnv.calldata) (fun k hk => W_c37 _ hk)
  have hks3 : KS4 m3 (W s.executionEnv.calldata 2) := KS4.congr hks3' fun k hk => (W_c37 _ hk).symm
  -- call 38: tr block 13 into slot 0
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcdC htl (m := m3)
    (pc0 := 4195) (r0 := 4243) (r1 := 4251) (r2 := 4265) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 3) (j := 13) (off := 1768) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam65_rreach [1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500])
    (fun _ => by glam65_rreach [1501, 1502, 1503, 1504])
    (fun _ => by glam65_rreach [1505, 1506, 1507, 1508, 1509, 1510] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (W_sized _ 2) hks3 hB3 (St := W s.executionEnv.calldata) (fun k hk => W_c38 _ hk)
  have hks4 : KS4 m4 (W s.executionEnv.calldata 3) := KS4.congr hks4' fun k hk => (W_c38 _ hk).symm
  -- IMGB
  have g5 : Reach (callState s 4265 [flag b] m4)
      (callState s 4274 [wd 0x14d20, wd 0, wd 800, flag b] m4) 9 := by
    glam65_rreach [1511, 1512, 1513, 1514]
  have hmc := reach_mcopy hs ⟨1515, by norm_num⟩ (pc := 4274) (d := 0x14d20) (src := 0) (n := 800)
    (rest := [flag b]) (m := m4) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by simp)
  have hfM := FrameExcept.mcopy m4 0 0x14d20 800
  refine ⟨_, KS4.frame hks4 hfM (by w_frame), fun x hx => ?_, hB4.frame hfM (by w_frame) (by w_frame),
    RC4Table.frame hrc4 hfM (by w_frame), ?_, ?_⟩
  · rw [word_mcopy _ (by omega) (by omega), show 0 + (0x14d20 + 32 * x - 0x14d20) = KS + 32 * x by
      unfold KS; omega]
    exact hks4 x hx
  · exact ((((hf1.trans hf2).trans hf3).trans hf4).trans hfM).mono (by decide)
  · have hR := ((((((g1.trans hc1).trans hR2).trans hR3).trans hR4).trans g5).trans hmc)
    refine hR.mono (le_of_eq ?_)
    unfold cW2a
    generalize Gas.ginit = a1; generalize Gas.trabs 5 = a2; generalize Gas.kmove = a3
    generalize Gas.kf4 = a4; generalize Gas.blk = a5
    omega


/-- `4275 … 4400`: `kmove` (`A44` back), call 39, `gfix 12`, `pass3f7`. -/
def cW2b : Nat := 27 + Gas.kmove + (15 + Gas.kf4 + 21 + Gas.blk) + 26 + Gas.gfix 2 + 18 + Gas.pass3f7

set_option maxHeartbeats 1000000 in
theorem win_2b {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hks : KS4 m (W s.executionEnv.calldata 3))
    (himgA : St4At m 0x14a00 (W s.executionEnv.calldata 1))
    (hB : HBlocks m ABUF FL (W s.executionEnv.calldata) 4) (b : Bool) :
    ∃ m9 m', KS4 m' (W s.executionEnv.calldata 4) ∧
      (∀ b', b' < 5 → ∀ i, i < 56 → ∀ sl, sl < 2 →
        lane (word m' (ABUF + 1792 * b' + 32 * i)) sl = cand (W s.executionEnv.calldata b' sl) i) ∧
      (∀ b', b' < 5 → ∀ g, g < 7 → word m' (FL + 224 * b' + 32 * g) = flagWord (W s.executionEnv.calldata b') g) ∧
      (∀ t, t < 256 → word m' (ACC + 32 * t) = p3f7Word m9 t) ∧
      (okA s.executionEnv.calldata = true → ∀ t, t < 256 →
        lane (word m9 (ABUF + 32 * t)) 2 = ((aD s.executionEnv.calldata 3 4)[t]!).toNat ∧
        lane (word m9 (ABUF + 32 * t)) 3 = ((aD s.executionEnv.calldata 3 3)[t]!).toNat) ∧
      FrameExcept m m9 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
        (KB, KB + 800), (BK, BK + 800)] ∧
      FrameExcept m9 m' [(ACC, ACC + 8192)] ∧
      Reach (callState s 4275 [flag b] m)
        (callState s 4400 [flag (b && okP s.executionEnv.calldata)] m') cW2b := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  have htl : [flag b].length ≤ 8 := by simp
  -- kmove: A44 from IMGA into slot 0
  have g6 : Reach (callState s 4275 [flag b] m)
      (callState s 18099 [wd 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,
        wd 0x1111111111111111111111111111111111111111111111111111111111111111,
        wd 0, wd 0, wd 0x14a00, wd 4354, flag b] m) 27 := by
    glam65_rreach [1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523]
  obtain ⟨m6, hw6, hf6, hc6⟩ := kmove_call hs (ret := 4354) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (src := 0x14a00) (sl := 0) (sr := 0) (msk := 0x1111111111111111111111111111111111111111111111111111111111111111)
    (keep := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee) (Or.inr (by unfold KS; norm_num))
    (by unfold TOP; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hks6 : KS4 m6 (I3 s.executionEnv.calldata) := fun x hx => by
    rw [hw6 x hx, ks4_il himgA hx, hks x hx, kmove_src0 _ _ (fun k _ => cpl_lt (laneOf_lt _ _))
      (fun k _ => cpl_lt (laneOf_lt _ _))]
    apply il_congr; intro k _
    unfold I3; split <;> rfl
  -- call 39 (whole block 4)
  obtain ⟨m7, hks7', hA7, hF7, hrc7, hf7, hR7⟩ := kbf_round hs htl (stk := [flag b]) (m := m6)
    (pc0 := 4354) (r1 := 4362) (r2 := 4376) (c1 := 15) (c2 := 21) (b := 4) (by norm_num) bufOK_abuf
    (by glam65_rreach [1524, 1525, 1526, 1527])
    (fun _ => by glam65_rreach [1528, 1529, 1530, 1531, 1532, 1533] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc hf6 (by w_frame)) (I3_sized _) hks6
  have hW4 : ∀ k, k < 4 → Keccak.permute (I3 s.executionEnv.calldata k) = W s.executionEnv.calldata 4 k :=
    fun k hk => (W_c39 _ hk).symm
  have hks7 : KS4 m7 (W s.executionEnv.calldata 4) := KS4.congr hks7' hW4
  have hA7' : ∀ i, i < 56 → word m7 (ABUF + 1792 * 4 + 32 * i) =
      pack4 fun k => cand (W s.executionEnv.calldata 4 k) i := fun i hi => by
    rw [hA7 i hi]; exact pack4_congr fun k hk => by rw [hW4 k hk]
  have hF7' : ∀ g, g < 7 → word m7 (FL + 224 * 4 + 32 * g) = flagWord (W s.executionEnv.calldata 4) g :=
    fun g hg => by rw [hF7 g hg]; exact flagWord_congr hW4 g
  have hB7 : HBlocks m7 ABUF FL (W s.executionEnv.calldata) 5 := fun b' hb' => by
    by_cases h4 : b' < 4
    · exact ((hB.frame hf6 (by w_frame) (by w_frame)).frame hf7 (by w_frame) (by w_frame)) b' h4
    · obtain rfl : b' = 4 := by omega
      exact ⟨fun i hi _ => hA7' i hi, fun g hg _ => hF7' g hg⟩
  -- HAVE6 := 0, gfix 12
  have g8 : Reach (callState s 4376 [flag b] m7)
      (callState s 17249 [wd 12, wd 4391, flag b]
        (MachineState.writeBytes m7 (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 26 := by
    glam65_rreach [1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541] with [HAVE6]
  generalize hm8 : MachineState.writeBytes m7 (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m8 at g8
  have hf8 : FrameExcept m7 m8 [(HAVE6, HAVE6 + 32)] := hm8 ▸ FrameExcept.mstore m7 HAVE6 0
  have h68 : word m8 HAVE6 = 0 := hm8 ▸ word_mstore m7 HAVE6 0 (by norm_num)
  have hB8 := hB7.frame hf8 (by w_frame) (by w_frame)
  have hA8 : ∀ i, i < 56 → word m8 (ABUF + 1792 * 4 + 32 * i) =
      pack4 fun k => cand (W s.executionEnv.calldata 4 k) i := fun i hi => by
    rw [word_frame hf8 (lo := ABUF) (hi := FL + 1344) (by w_frame) (by unfold ABUF; omega)
      (by unfold ABUF FL; omega)]
    exact hA7' i hi
  have hF8 : ∀ g, g < 7 → word m8 (FL + 224 * 4 + 32 * g) = flagWord (W s.executionEnv.calldata 4) g :=
    fun g hg => by
      rw [word_frame hf8 (lo := ABUF) (hi := FL + 1344) (by w_frame) (by unfold ABUF FL; omega)
        (by unfold FL; omega)]
      exact hF7' g hg
  obtain ⟨m9, hlanes9, hks9, -, hkeep9, hf9, hc9⟩ := gfix_call hs (ret := 4391) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
    (RC4Table.frame hrc7 hf8 (by w_frame)) (amask := 12) (by norm_num) 2 (by decide)
    (W s.executionEnv.calldata 4) (W_sized _ 4) (KS4.frame hks7 hf8 (by w_frame)) (IP s.executionEnv.calldata) h68
    (fun sl hsl hbit => by
      have h23 : sl = 2 ∨ sl = 3 := by
        interval_cases sl <;> first | exact absurd hbit (by decide) | simp
      exact ⟨hB8.slotHead hsl fun b' hb' => W_P _ hb' h23, W_P _ (by norm_num) h23⟩)
  rw [flag_P hcd32] at hc9
  obtain ⟨hkl, hkf⟩ := hkeep9 ⟨fun i _ h2 => hA8 i h2, fun g _ h2 => hF8 g h2⟩
  -- AND, pass3f7
  have g10 : Reach (callState s 4391 [flag (okP s.executionEnv.calldata), flag b] m9)
      (callState s 16731 [wd 4400, flag (b && okP s.executionEnv.calldata)] m9) 18 := by
    glam65_rreach [1542, 1543, 1544, 1545, 1546] with [flag, MlDsaOpt44.Proofs.ite01_land]
  obtain ⟨m10, hw10, hf10, hc10⟩ := pass3f7_call hs (ret := 4400)
    (tail := [flag (b && okP s.executionEnv.calldata)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m9
  -- the pre-`gfix` words of blocks 0 … 4
  have hpre : ∀ b', b' < 5 → ∀ i, i < 56 →
      word m8 (ABUF + 1792 * b' + 32 * i) = pack4 fun k => cand (W s.executionEnv.calldata b' k) i := by
    intro b' hb' i hi
    by_cases h4 : b' < 4
    · exact (hB8 b' (by omega)).1 i hi (by omega)
    · obtain rfl : b' = 4 := by omega
      exact hA8 i hi
  have hpreF : ∀ b', b' < 5 → ∀ g, g < 7 →
      word m8 (FL + 224 * b' + 32 * g) = flagWord (W s.executionEnv.calldata b') g := by
    intro b' hb' g hg
    by_cases h4 : b' < 4
    · exact (hB8 b' (by omega)).2 g hg (by omega)
    · obtain rfl : b' = 4 := by omega
      exact hF8 g hg
  refine ⟨m9, m10, KS4.frame hks9 hf10 (by w_frame), fun b' hb' i hi sl hsl => ?_, fun b' hb' g hg => ?_,
    hw10, fun hok t ht => ?_, ((((hf6.trans hf7).trans hf8).trans hf9).mono (by decide)), hf10, ?_⟩
  · rw [word_frame hf10 (lo := ABUF) (hi := FL + 1344) (by w_frame) (by unfold ABUF; omega)
      (by unfold ABUF FL; omega), show ABUF + 1792 * b' + 32 * i = ABUF + 32 * (56 * b' + i) by ring,
      hkl sl (by omega) (by interval_cases sl <;> decide) _ (by omega),
      show ABUF + 32 * (56 * b' + i) = ABUF + 1792 * b' + 32 * i by ring, hpre b' hb' i hi,
      Fix.lane_pack4_cand _ _ (by omega)]
  · rw [word_frame hf10 (lo := ABUF) (hi := FL + 1344) (by w_frame) (by unfold ABUF FL; omega)
      (by unfold FL; omega), show FL + 224 * b' + 32 * g = FL + 32 * (7 * b' + g) by ring,
      hkf _ (by omega), show FL + 32 * (7 * b' + g) = FL + 224 * b' + 32 * g by ring, hpreF b' hb' g hg]
  · have h34 : (aOf s.executionEnv.calldata 3 4).isSome = true := s3_okA_get hok (by norm_num) (by norm_num)
    have h33 : (aOf s.executionEnv.calldata 3 3).isSome = true := s3_okA_get hok (by norm_num) (by norm_num)
    obtain ⟨a4, ha4⟩ := Option.isSome_iff_exists.mp h34
    obtain ⟨a3, ha3⟩ := Option.isSome_iff_exists.mp h33
    refine ⟨?_, ?_⟩
    · rw [hlanes9 2 (by norm_num) (by decide) a4 (by
        rw [show IP s.executionEnv.calldata 2 = sA s.executionEnv.calldata 3 4 from by unfold IP; simp, sA,
          GroupP.aI_aSeed hcd32]
        exact ha4) t ht]
      unfold aD; rw [ha4]; rfl
    · rw [hlanes9 3 (by norm_num) (by decide) a3 (by
        rw [show IP s.executionEnv.calldata 3 = sA s.executionEnv.calldata 3 3 from by unfold IP; simp, sA,
          GroupP.aI_aSeed hcd32]
        exact ha3) t ht]
      unfold aD; rw [ha3]; rfl
  · have hR := ((((((g6.trans hc6).trans hR7).trans g8).trans hc9).trans g10).trans hc10)
    refine hR.mono (le_of_eq ?_)
    unfold cW2b
    generalize Gas.kmove = a3; generalize Gas.kf4 = a4; generalize Gas.blk = a5
    generalize Gas.gfix 2 = a6; generalize Gas.pass3f7 = a7
    omega


/-- Calls 35–39, `gfix 12`, `pass3f7` (`3739 … 4400`). -/
theorem win_A {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : WinIn s.executionEnv.calldata m) (b : Bool) :
    ∃ m', WinMid s.executionEnv.calldata m' ∧
      Reach (callState s 3739 [flag b] m) (callState s 4400 [flag (b && okP s.executionEnv.calldata)] m')
        (cW1 + cW2a + cW2b) := by
  obtain ⟨m1, hks1, himgA, hB1, hf1, hR1⟩ := win_1 hs hcd hI b
  have hg1 := hI.toG5In.frame hf1 (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
    (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
  obtain ⟨m2, hks2, himgB, hB2, hrc2, hf2, hR2⟩ := win_2a hs hcd hg1.rho hg1.rc4 hks1 hB1 b
  obtain ⟨m9, m3, hks3, hl3, hfl3, hacc, hP, hf39, hf93, hR3⟩ := win_2b hs hcd hrc2 hks2
    (himgA.frame hf2 (by w_frame)) hB2 b
  have hg2 := hg1.frame hf2 (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
    (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
  have hg9 := hg2.frame hf39 (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
    (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
  have hfA := (hf1.trans hf2).trans hf39
  refine ⟨m3, ⟨hg9.frame hf93 (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
    (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame), hks3, hl3, hfl3,
    (himgB.frame hf39 (by w_frame)).frame hf93 (by w_frame),
    ⟨m9, hacc, hg9.zhat, hg9.c0, hg9.c1, hg9.c2, hI.c3.frame hfA (by w_frame),
      hI.c4.frame hfA (by w_frame), hP⟩⟩, (hR1.trans hR2).trans hR3⟩

end MlDsaOptGlam65.Proofs.Exp
