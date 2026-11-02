import MlDsaOpt65.Fn.Sponge.Mub0Math
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
/-!
# Lanes of μ's blocks `k ≥ 1` (`mub`, ML-DSA-65)

`P = |cd| − 0x144b = 66 + |M|` is the size of μ's input `tr ‖ 0 ‖ 0 ‖ M`.
For `K = 136 k ≤ P`, byte `K + i` (`i < 136`) of the padded input is the
calldata byte `cd[0x144b + K + i]` (zero past the end), xored with `0x1F` at
`P` and `0x80` at byte 135 of the last block (`byteAt_mubBlk`); lane `x` is
`le64 cd (0x144b + K + 8x)`, xored with `mubPad (P − K) x` and `muTop x` when
`P < K + 136` (`le64_mubBlk`). `mub_value_full` / `mub_value_last`: the state
words after `mub`'s `trabs` (and padding) path.
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- `mub`'s `trabs [0, LM, 5, sh, off]`: lanes `0 … 16` of calldata from `off`, lanes `17 … 19` zero. -/
theorem mub_trLane (cd : ByteArray) (off : Nat) {x : Nat} (h20 : x < 20) :
    trLane cd off 115792089237316195417293883273301227089434195242432897623355228563449095127040 5 x =
      if x ≤ 16 then le64 cd (off + 8 * x) else 0 := by
  have hu : x = 4 * (x / 4) + x % 4 := by omega
  rw [hu, trLane_eq _ _ _ _ _ (Nat.mod_lt _ (by omega))]
  by_cases hi : x / 4 + 1 = 5
  · rw [if_pos hi, lm_lane _ (Nat.mod_lt _ (by omega))]
    by_cases hj : x % 4 = 0
    · rw [if_pos hj, if_pos (by omega), show (192 : Nat) = 192 - 64 * 0 from rfl,
        bsw_lane _ _ (by omega)]
      congr 1; omega
    · rw [if_neg hj, if_neg (by omega)]
  · rw [if_neg hi, bsw_lane _ _ (Nat.mod_lt _ (by omega)), if_pos (by omega)]
    congr 1; omega

/-- Bytes of `pad` at and past the end of the message. -/
theorem byteAt_pad_ge (rate : Nat) (hr : 0 < rate) (msg : ByteArray) {i : Nat} (hi : msg.size ≤ i) :
    byteAt (Fips202.pad rate 0x1F msg) i =
      if i < msg.size + (rate - msg.size % rate) then
        (if i = msg.size then 31 else 0) |||
          (if i = msg.size + (rate - msg.size % rate) - 1 then 128 else 0)
      else 0 := by
  unfold Fips202.pad
  simp only
  rw [byteAt_append, if_neg (by omega)]
  have hL : 0 < rate - msg.size % rate := by have := Nat.mod_lt msg.size hr; omega
  generalize rate - msg.size % rate = L at hL ⊢
  have hsz0 : ((ByteArray.mk (Array.replicate L 0))).size = L := by
    change (Array.replicate _ (0 : UInt8)).size = _; rw [Array.size_replicate]
  have hsz1 : ((ByteArray.mk (Array.replicate L 0)).set! 0 0x1F).size = L := by
    rw [ByteArray.size_set!, hsz0]
  by_cases hin : i < msg.size + L
  · rw [if_pos hin, byteAt_set! _ _ _ _ (by rw [hsz1]; omega),
      byteAt_set! _ _ _ _ (by rw [hsz0]; omega), byteAt_replicate,
      ByteArray.getElem!_set! _ _ _ _ (by rw [hsz0]; omega)]
    have hz : ((ByteArray.mk (Array.replicate L 0))[L - 1]!) = 0 := by
      have := byteAt_replicate L (L - 1)
      rw [byteAt_eq_getElem!] at this
      exact UInt8.toNat_inj.mp this
    rw [hz]
    split_ifs <;> first | rfl | omega
  · rw [if_neg hin, byteAt_of_size_le (by rw [ByteArray.size_set!, hsz1]; omega)]

theorem muIn_size {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size) :
    (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size = cd.size - 5195 := by
  have h2 : (ByteArray.mk #[(0 : UInt8), 0]).size = 2 := rfl
  simp only [ByteArray.size_append, htr, h2, msgOf_size]; omega

/-- **Byte `K + i` of μ's padded input**, `K` a block start with `66 ≤ K ≤ P`. -/
theorem byteAt_mubBlk {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size) {K i : Nat}
    (hK : 66 ≤ K) (hK136 : K % 136 = 0) (hKP : K ≤ cd.size - 5195) (hi : i < 136) :
    byteAt (Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))) (K + i) =
      byteAt cd (5195 + K + i) ^^^ (if K + i = cd.size - 5195 then 31 else 0) ^^^
        (if cd.size - 5195 < K + 136 ∧ i = 135 then 128 else 0) := by
  have hsz := muIn_size htr hcd
  by_cases h : K + i < cd.size - 5195
  · unfold Fips202.pad
    simp only
    rw [byteAt_append, if_pos (by rw [hsz]; exact h), byteAt_mu0U htr hcd, if_neg (by omega),
      if_pos (by omega), if_neg (show ¬ K + i = cd.size - 5195 by omega),
      if_neg (show ¬ (cd.size - 5195 < K + 136 ∧ i = 135) by omega), Nat.add_assoc]
    simp
  · rw [byteAt_pad_ge 136 (by norm_num) _ (by rw [hsz]; omega), hsz,
      if_pos (show K + i < cd.size - 5195 + (136 - (cd.size - 5195) % 136) by omega),
      byteAt_of_size_le (show cd.size ≤ 5195 + K + i by omega)]
    have e2 : (K + i = cd.size - 5195 + (136 - (cd.size - 5195) % 136) - 1) = (i = 135) :=
      propext (by omega)
    have e3 : (cd.size - 5195 < K + 136 ∧ i = 135) = (i = 135) := propext (by omega)
    simp only [e2, e3]
    split_ifs <;> rfl

/-- The padding lane of the last block: `0x1F` at byte `r` (`r < 136`). -/
def mubPad (r x : Nat) : Nat := if x = r / 8 then 31 * 2 ^ (8 * (r % 8)) else 0

theorem testBit_mubPad (r x : Nat) {j : Nat} (hj : j < 64) :
    (mubPad r x).testBit j = (if 8 * x + j / 8 = r then 31 else 0).testBit (j % 8) := by
  unfold mubPad
  rw [testBit_ite, testBit_ite, Nat.mul_comm 31, Nat.testBit_two_pow_mul]
  by_cases hx : x = r / 8
  · by_cases hq : j / 8 = r % 8
    · have e1 : 8 * x + j / 8 = r := by omega
      have e2 : 8 * (r % 8) ≤ j := by omega
      have e3 : j - 8 * (r % 8) = j % 8 := by omega
      subst hx
      simp [e1, e2, e3]
    · have e1 : ¬ (8 * x + j / 8 = r) := by omega
      rw [decide_eq_false e1, Bool.false_and]
      by_cases hle : 8 * (r % 8) ≤ j
      · have h5 : (31 : Nat).testBit (j - 8 * (r % 8)) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show (31 : Nat) < 2 ^ 5 by norm_num)
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h5]
      · simp [hle]
  · have e1 : ¬ (8 * x + j / 8 = r) := by omega
    simp [hx, e1]

theorem mub_pad_lt (r : Nat) : 31 * 2 ^ (8 * (r % 8)) < 2 ^ 64 := by
  have h : r % 8 < 8 := Nat.mod_lt _ (by omega)
  generalize r % 8 = q at h
  interval_cases q <;> norm_num

theorem mubPad_lt (r x : Nat) : mubPad r x < 2 ^ 64 := by
  unfold mubPad; split
  · exact mub_pad_lt r
  · norm_num

theorem mub_pad_eq (r : Nat) : 31 * 2 ^ ((7 &&& r) * 8) = 31 * 2 ^ (8 * (r % 8)) := by
  rw [Nat.and_comm, show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mul_comm _ 8]

/-- **Lane `x` of block `K` of μ's padded input.** -/
theorem le64_mubBlk {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size) {K x : Nat}
    (hK : 66 ≤ K) (hK136 : K % 136 = 0) (hKP : K ≤ cd.size - 5195) (hx : x < 17) :
    le64 (Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))) (K + 8 * x) =
      le64 cd (5195 + K + 8 * x) ^^^
        (if cd.size - 5195 < K + 136 then mubPad (cd.size - 5195 - K) x ^^^ muTop x else 0) := by
  have hlt : (if cd.size - 5195 < K + 136 then mubPad (cd.size - 5195 - K) x ^^^ muTop x else 0) <
      2 ^ 64 := by
    split
    · exact Nat.xor_lt_two_pow (mubPad_lt _ _) (muTop_lt x)
    · norm_num
  apply eq_of_testBit_lt (n := 64) (le64_lt64 _ _) (Nat.xor_lt_two_pow (le64_lt64 _ _) hlt)
  intro j hj
  rw [testBit_le64, decide_eq_true hj, Bool.true_and, Nat.add_assoc,
    byteAt_mubBlk htr hcd hK hK136 hKP (by omega), Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_xor, testBit_le64, decide_eq_true hj, Bool.true_and,
    show 5195 + K + (8 * x + j / 8) = 5195 + K + 8 * x + j / 8 by omega]
  by_cases hc : cd.size - 5195 < K + 136
  · rw [if_pos hc, Nat.testBit_xor, testBit_mubPad _ _ hj, testBit_muTop _ hj]
    have e1 : (K + (8 * x + j / 8) = cd.size - 5195) = (8 * x + j / 8 = cd.size - 5195 - K) :=
      propext (by omega)
    have e2 : (cd.size - 5195 < K + 136 ∧ 8 * x + j / 8 = 135) = (x = 16 ∧ j / 8 = 7) :=
      propext (by omega)
    simp only [e1, e2, Bool.xor_assoc]
  · rw [if_neg hc, if_neg (show ¬ (K + (8 * x + j / 8) = cd.size - 5195) by omega),
      if_neg (show ¬ (cd.size - 5195 < K + 136 ∧ 8 * x + j / 8 = 135) by omega)]
    simp

set_option maxHeartbeats 1000000 in
/-- The state words after `mub`'s path through `trabs` without padding (`K + 136 ≤ P`). -/
theorem mub_value_full {m m9 tr cd : ByteArray} {sh K : Nat}
    (htr : tr.size = 64) (hcd : 5261 ≤ cd.size)
    (hK : 66 ≤ K) (hK136 : K % 136 = 0) (hKP : K + 136 ≤ cd.size - 5195)
    (h9 : ∀ x, x < 25 → word m9 (32 * x) = if x < 20 then
        word m (32 * x) ^^^ spread (trLane cd (5195 + K)
          115792089237316195417293883273301227089434195242432897623355228563449095127040 5 x) * 2 ^ sh
        else word m (32 * x))
    {x : Nat} (hx : x < 25) :
    word m9 (32 * x) = if x < 17 then
        word m (32 * x) ^^^ spread (le64 (Fips202.pad 136 0x1F
          (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))) (K + 8 * x)) * 2 ^ sh
      else word m (32 * x) := by
  have hS0 : spread 0 * 2 ^ sh = 0 := by rw [spread_zero', Nat.zero_mul]
  rw [h9 x hx]
  by_cases hx17 : x < 17
  · rw [if_pos (by omega), if_pos hx17, mub_trLane _ _ (by omega), if_pos (by omega),
      le64_mubBlk htr hcd hK hK136 (by omega) hx17, if_neg (by omega), Nat.xor_zero]
  · rw [if_neg hx17]
    by_cases h20 : x < 20
    · rw [if_pos h20, mub_trLane _ _ h20, if_neg (by omega), hS0, Nat.xor_zero]
    · rw [if_neg h20]

set_option maxHeartbeats 1000000 in
/-- The state words after `mub`'s path through `trabs` and the padding of the last block. -/
theorem mub_value_last {m m9 m10 m11 tr cd : ByteArray} {sh K : Nat} (hsh : sh < 4)
    (htr : tr.size = 64) (hcd : 5261 ≤ cd.size)
    (hK : 66 ≤ K) (hK136 : K % 136 = 0) (hKP : K ≤ cd.size - 5195) (hPK : cd.size - 5195 < K + 136)
    (h9 : ∀ x, x < 25 → word m9 (32 * x) = if x < 20 then
        word m (32 * x) ^^^ spread (trLane cd (5195 + K)
          115792089237316195417293883273301227089434195242432897623355228563449095127040 5 x) * 2 ^ sh
        else word m (32 * x))
    (h10 : m10 = MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded
      ((sprNet (31 * 2 ^ ((7 &&& cd.size - 5195 - K) * 8)) * 2 ^ sh ^^^
          word m9 (0 + (cd.size - 5195 - K) / 8 * 32)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936) 32)
      (0 + (cd.size - 5195 - K) / 8 * 32))
    (h11 : m11 = MachineState.writeBytes m10 (Data.Bytes.natToBytesPadded
      ((word m10 512 ^^^
          7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)
    {x : Nat} (hx : x < 25) :
    word m11 (32 * x) = if x < 17 then
        word m (32 * x) ^^^ spread (le64 (Fips202.pad 136 0x1F
          (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))) (K + 8 * x)) * 2 ^ sh
      else word m (32 * x) := by
  generalize hr : cd.size - 5195 - K = r at h10
  have hr16 : r / 8 ≤ 16 := by omega
  have hPAD : sprNet (31 * 2 ^ ((7 &&& r) * 8)) = spread (31 * 2 ^ (8 * (r % 8))) := by
    rw [mub_pad_eq, sprNet_eq (mub_pad_lt _)]
  have hTOP : (7237005577332262213973186563042994240829374041602535252466099000494570602496 : Nat) =
      spread (2 ^ 63) := spread_top.symm
  have hw10 : ∀ y, word m10 (32 * y) = if y = r / 8 then
      (spread (31 * 2 ^ (8 * (r % 8))) * 2 ^ sh ^^^ word m9 (32 * (r / 8))) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      else word m9 (32 * y) := by
    intro y
    rw [h10, word_wb32 _ (by omega) (by omega) (modL_lt _), hPAD,
      show 0 + r / 8 * 32 = 32 * (r / 8) by ring]
    by_cases hy : y = r / 8
    · rw [if_pos (by omega), if_pos hy]
    · rw [if_neg (by omega), if_neg hy]
  have hw11 : word m11 (32 * x) = if x = 16 then
      (word m10 (32 * 16) ^^^ spread (2 ^ 63) * 2 ^ sh) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      else word m10 (32 * x) := by
    rw [h11, word_wb32 _ (by omega) (by norm_num) (modL_lt _), hTOP]
    by_cases hy : x = 16
    · rw [if_pos (by omega), if_pos hy]
    · rw [if_neg (by omega), if_neg hy]
  have hS0 : spread 0 * 2 ^ sh = 0 := by rw [spread_zero', Nat.zero_mul]
  have h9' : ∀ y, y ≤ 16 → word m9 (32 * y) =
      word m (32 * y) ^^^ spread (le64 cd (5195 + K + 8 * y)) * 2 ^ sh := by
    intro y hy
    rw [h9 y (by omega), if_pos (by omega), mub_trLane _ _ (by omega), if_pos hy]
  rw [hw11]
  by_cases hx17 : x < 17
  · rw [if_pos hx17, le64_mubBlk htr hcd hK hK136 hKP hx17, if_pos hPK, hr, S_xor, S_xor, mubPad,
      muTop]
    by_cases h16 : x = 16
    · subst h16
      simp only [eq_self_iff_true, ↓reduceIte]
      rw [hw10 16]
      by_cases hP : 16 = r / 8
      · rw [if_pos hP, if_pos hP, ← hP, h9' 16 (le_refl _)]
        mu_fin'
      · rw [if_neg hP, if_neg hP, h9' 16 (le_refl _)]
        mu_fin'
    · rw [if_neg h16, if_neg h16, hw10 x]
      by_cases hP : x = r / 8
      · rw [if_pos hP, if_pos hP, ← hP, h9' x (by omega)]
        mu_fin'
      · rw [if_neg hP, if_neg hP, h9' x (by omega)]
        mu_fin'
  · rw [if_neg hx17, if_neg (show ¬ x = 16 by omega), hw10, if_neg (show ¬ x = r / 8 by omega),
      h9 x hx]
    by_cases h20 : x < 20
    · rw [if_pos h20, mub_trLane _ _ h20, if_neg (by omega), hS0, Nat.xor_zero]
    · rw [if_neg h20]

end MlDsaOpt65.Proofs.WP4
