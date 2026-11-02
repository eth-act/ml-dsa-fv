import MlDsaOpt44.Main.Win.States
set_option warningAsError true
/-!
# Window part B: `4149 … 4422`

`ginit` (row 3 of columns 3, 2 into slots 2, 3; tr and `A[0][3]` kept), call
18 (tr block 8), call 19 (tr's last block with its padding), `cext` of tr's
eight lanes into `TRL`, the image `SAVE1`.
-/

namespace MlDsaOpt44.Proofs.Ex

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

theorem spread_xor_shift (a b sh : Nat) (hsh : sh < 4) :
    spread a * 2 ^ sh ^^^ spread b * 2 ^ sh = spread (a ^^^ b) * 2 ^ sh := by
  rw [spread_mul_two_pow _ hsh, spread_mul_two_pow _ hsh, spread_mul_two_pow _ hsh, il_xor]
  exact il_congr fun k _ => by split <;> simp

/-- The last block of the padded public key (`trabs` with three groups, then
the two padding xors), absorbed into slot `sh`. -/
theorem ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : 1312 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S) {sh : Nat} (hsh : sh < 4)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 3 then
        trLane cd 1224 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 3 x
        else 0) * 2 ^ sh ^^^ spread ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ sh) :
    KS4 m' (upd S sh (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (9 * 136) (S sh))) := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  refine ks4_xor_slot hsh hks (fun x => (if x < 4 * 3 then
        trLane cd 1224 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 3 x
        else 0) ^^^ ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact trLane_lt' _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, spread_xor_shift _ _ _ hsh]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS sh hsh) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 9 * 136 + 8 * x = 1224 + 8 * x by omega,
      le64_padPk_last hcd h17]
    congr 1
    by_cases h11 : x < 11
    · rw [if_pos h11, if_pos (by omega), trLane_eq cd lm_top3, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero]
    · rw [if_neg h11]
      by_cases hx11 : x = 11
      · subst hx11; rw [trLane_eq cd lm_top3]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx11, if_neg hx16, Nat.xor_zero]
          rw [if_neg (by omega)]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

/-- The two padding xors of tr's last block (slot 0). -/
theorem pad_words0 {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 352 ^^^ 69905) % 2 ^ 256) 32) 352)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 352 ^^^ 69905) % 2 ^ 256) 32) 352) 512 ^^^
        7237005577332262213973186563042994240829374041602535252466099000494570602496) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 0 := by
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

theorem permute_upd_W2_last (cd : ByteArray) {k : Nat} (hk : k < 4) :
    Keccak.permute (upd (W2 cd 1) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (9 * 136) (W2 cd 1 0)) k) =
      W2 cd 2 k := by
  unfold upd W2
  by_cases h0 : k = 0
  · subst h0; simp only [if_true]
    rw [show 8 + 2 = (8 + 1) + 1 by omega, absorbPre_succ]; rfl
  · rw [if_neg h0, if_neg h0, if_neg h0]
    split
    · rw [← permN_succ]
    · split <;> rw [← permN_succ]

theorem winB_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrho : Rho1At m s.executionEnv.calldata) (hks : KS4 m (W1 s.executionEnv.calldata 3)) :
    ∃ m1, KS4 m1 (W2 s.executionEnv.calldata 0) ∧ FrameExcept m m1 [(KS, KS + 800)] ∧
      Reach (callState s 4149 [flag w] m) (callState s 4204 [flag w] m1) (25 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho hks
  have g0 : Reach (callState s 4149 [flag w] m)
      (callState s 10911 [wd 0x0ccccc000000cc000000c4, wd 0, wd 12,
        wd 0x3333333333333333333333333333333333333333333333333333333333333333, wd 4204, flag w] m) 25 := by
    opt44_reach [1343, 1344, 1345, 1346, 1347, 1348, 1349]
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 4204) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (keep := 0x3333333333333333333333333333333333333333333333333333333333333333) (amult := 12)
    (cmult := 0) (l4 := 0x0ccccc000000cc000000c4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hkeep : (0x3333333333333333333333333333333333333333333333333333333333333333 : Nat) =
      il fun k => if (3 : Nat).testBit k then M64 else 0 := by decide +kernel
  have hks1 : KS4 m1 (W2 cd 0) :=
    ks4_ginit (kmask := 3)
      (L := fun k => if k = 2 then 3 + 256 * 3 + 0x1F0000 else if k = 3 then 2 + 256 * 3 + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := W1 cd 3)
      (by norm_num) (by norm_num) hkeep (by decide +kernel)
      (fun x hx => (hrho x hx).1) (fun x hx => (hrho x hx).2)
      (fun x hx => by rw [hkeep]; exact ks4_and_keep hks 3 hx)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> (try split) <;> omega)
      (fun k hk h => by
        have : k < 2 := by
          by_contra hne
          interval_cases k <;> first | omega | exact absurd h (by decide)
        interval_cases k <;> exact ⟨by decide, by decide, rfl⟩)
      (fun k hk h => by
        have : k < 2 := by
          by_contra hne
          interval_cases k <;> first | omega | exact absurd h (by decide)
        interval_cases k <;> (unfold W2 W1; simp))
      (fun k hk h x hx => by
        have : 2 ≤ k := by
          by_contra hne
          interval_cases k <;> exact absurd h (by decide)
        interval_cases k
        · exact freshLane_aSeed (r := 3) (col := 3) (by unfold HDR at hcd; omega) (fun _ _ => rfl)
            (by norm_num) (by norm_num) (by decide) (by decide) (by simp) hx
        · exact freshLane_aSeed (r := 3) (col := 2) (by unfold HDR at hcd; omega) (fun _ _ => rfl)
            (by norm_num) (by norm_num) (by decide) (by decide) (by simp) hx)
      hg
  exact ⟨m1, hks1, hf1, g0.trans hc1⟩

/-- Window part B. -/
theorem winB {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata)
    (hks : KS4 m (W1 s.executionEnv.calldata 3)) :
    ∃ m', KS4 m' (W2 s.executionEnv.calldata 2) ∧ HBlocks m' ABUF FL (EB s.executionEnv.calldata) 2 ∧
      (∀ x, x < 8 → word m' (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x)) ∧
      St4At m' SAVE1 (W2 s.executionEnv.calldata 2) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF, ABUF + 1792 * 2), (FL, FL + 224 * 2),
        (TRL, TRL + 256), (SAVE1, SAVE1 + 800)] ∧
      Reach (callState s 4149 [flag w] m) (callState s 4422 [flag w] m')
        (25 + Gas.ginit + (28 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) +
          (28 + Gas.trabs 3 + (51 + Gas.kf4 + 21 + Gas.blk)) + 23 + Gas.cext 8 + 9 + 78) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 1312 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have htl : [flag w].length ≤ 8 := by simp
  obtain ⟨m1, hks1, hf1, hR1⟩ := winB_ginit hs hcd hrho hks (w := w)
  have hrc1 := hrc.frame hf1 (by avoids_tac)
  -- call 18
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcd' htl (m := m1)
    (pc0 := 4204) (r0 := 4252) (r1 := 4260) (r2 := 4274) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 0) (j := 8) (off := 1088) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by opt44_reach [1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358])
    (fun _ => by opt44_reach [1359, 1360, 1361, 1362])
    (fun _ => by opt44_reach [1363, 1364, 1365, 1366, 1367, 1368] with [ABUF, FL])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (W2_sized _ 0) hks1 (HBlocks.zero _ _ _ _) (St := EB s.executionEnv.calldata)
    (fun k hk => (permute_upd_W2 _ hk).symm)
  have hks2 : KS4 m2 (W2 s.executionEnv.calldata 1) := KS4.congr hks2' fun k hk => permute_upd_W2 _ hk
  -- call 19: the last block of pk and its padding
  have g30 : Reach (callState s 4274 [flag w] m2) (callState s 11702
      [wd 0, wd 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000, wd 3, wd 0, wd 1224,
        wd 4322, flag w] m2) 28 := by
    opt44_reach [1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377]
  obtain ⟨mt, hwt, hft, hct⟩ := trabs_call hs (ret := 4322) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2
    (off := 1224) (sh := 0) (n4 := 3) (lm := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000)
    (kp := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lmL_top3 (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have gpad : Reach (callState s 4322 [flag w] mt) (callState s 22529 [wd 4385, flag w]
      (MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 69905) % 2 ^ 256) 32) 352)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 69905) % 2 ^ 256) 32) 352) 512 ^^^
          7237005577332262213973186563042994240829374041602535252466099000494570602496) % 2 ^ 256) 32) 512))
      51 := by
    opt44_reach [1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392,
      1393] with [KS]
  have hwp := fun x (hx : x < 25) => pad_words0 (m := mt) hx
  generalize hMp : MachineState.writeBytes
        (MachineState.writeBytes mt (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 69905) % 2 ^ 256) 32) 352)
        (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes mt
          (Data.Bytes.natToBytesPadded ((word mt 352 ^^^ 69905) % 2 ^ 256) 32) 352) 512 ^^^
          7237005577332262213973186563042994240829374041602535252466099000494570602496) % 2 ^ 256) 32) 512
      = Mp at gpad hwp
  have hfp : FrameExcept mt Mp [(352, 352 + 32), (512, 512 + 32)] := by
    rw [← hMp]; exact FrameExcept.trans (FrameExcept.mstore _ _ _) (FrameExcept.mstore _ _ _)
  have hksp := ks4_trabs_last hcd' (W2_sized _ 1) hks2 (sh := 0) (by norm_num)
    fun x hx => by rw [hwp x hx, trabs_norm hwt x hx]
  have hB2' := (hB2.frame hft (by avoids_tac) (by avoids_tac)).frame hfp (by avoids_tac) (by avoids_tac)
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs htl (stk := [wd 4385, flag w])
    (m := Mp) (pc0 := 22529) (r1 := 4385) (r2 := 4399) (c1 := 0) (c2 := 21) (b := 1) (by norm_num)
    bufOK_abuf (Reach.refl _) (fun _ => by opt44_reach [1394, 1395, 1396, 1397, 1398, 1399] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    ((hrc2.frame hft (by avoids_tac)).frame hfp (by avoids_tac))
    (upd_sized (W2_sized _ 1) (by rw [xorBlock_size]; exact W2_sized _ 1 0 (by norm_num))) hksp hB2'
    (St := EB s.executionEnv.calldata) (fun k hk => (permute_upd_W2_last _ hk).symm)
  have hks3 : KS4 m3 (W2 s.executionEnv.calldata 2) := KS4.congr hks3' fun k hk => permute_upd_W2_last _ hk
  -- tr into TRL
  have gC : Reach (callState s 4399 [flag w] m3) (callState s 12151 [wd 8, wd 0, wd TRL, wd 4413, flag w] m3)
      23 := by
    opt44_reach [1400, 1401, 1402, 1403, 1404, 1405, 1406] with [TRL]
  obtain ⟨m4, htrl, hf4, hc4⟩ := cext_call hs (ret := 4413) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := TRL) (sh := 0) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS TRL; norm_num)
    (by unfold TRL TOP; norm_num)
  have hks4 := KS4.frame hks3 hf4 (by avoids_tac)
  -- the image SAVE1
  have g5 : Reach (callState s 4413 [flag w] m4) (callState s 4421 [wd SAVE1, wd KS, wd 800, flag w] m4) 9 := by
    opt44_reach [1407, 1408, 1409, 1410] with [SAVE1, KS]
  have hmc := reach_mcopy hs ⟨1411, by norm_num⟩ (pc := 4421) (d := SAVE1) (src := KS) (n := 800)
    (rest := [flag w]) (m := m4)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold SAVE1; norm_num)
    (by unfold KS; norm_num) (by norm_num) (by norm_num) (by unfold SAVE1; omega) (by unfold KS; omega) (by simp)
  have hf5 := FrameExcept.mcopy m4 KS SAVE1 800
  refine ⟨_, KS4.frame hks4 hf5 (by avoids_tac),
    (HBlocks.frame hB3 hf4 (by avoids_tac) (by avoids_tac)).frame hf5 (by avoids_tac) (by avoids_tac),
    fun x hx => ?_, fun x hx => ?_, (hrc3.frame hf4 (by avoids_tac)).frame hf5 (by avoids_tac), ?_, ?_⟩
  · rw [word_frame hf5 (lo := TRL) (hi := TRL + 256) (by avoids_tac) (by omega) (by omega), htrl x (by omega),
      cext_lane hks3 (by norm_num) (by omega), le64_trOf hcd' hx]
    rfl
  · rw [word_mcopy _ (by omega) (by omega), show KS + (SAVE1 + 32 * x - SAVE1) = KS + 32 * x by omega]
    exact hks4 x hx
  · have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf1 hf2) hft) hfp) hf3) hf4) hf5
    exact hf.mono (by decide)
  · have hR := ((((((((hR1.trans hR2).trans g30).trans hct).trans gpad).trans hR3).trans gC).trans hc4).trans
      g5).trans hmc
    refine hR.mono (le_of_eq ?_)
    generalize Gas.ginit = a; generalize Gas.trabs 5 = c; generalize Gas.kf4 = d; generalize Gas.blk = e
    generalize Gas.trabs 3 = f; generalize Gas.cext 8 = g
    omega

end MlDsaOpt44.Proofs.Ex
