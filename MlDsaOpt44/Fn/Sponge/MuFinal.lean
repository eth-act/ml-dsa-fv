import MlDsaOpt44.Fn.Sponge.MuVal
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
/-!
# The state words after `mu0`'s absorbing path

`mu0_value`: from the memory facts of the eight `TRL` lanes, the `trabs`
call and the three final stores, every state word is the old word xored with
the spread lane of μ's padded block (`le64_muBlock`).
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

theorem xor_modL' (a b : Nat) :
    (a ^^^ b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 ^^^
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.xor_mod_two_pow (n := 256)

theorem xor_left_comm'' (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem word_wb32 (M : ByteArray) {a b v : Nat} (ha : a % 32 = 0) (hb : b % 32 = 0)
    (hv : v < 2 ^ 256) :
    word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) b) a =
      if a = b then v else word M a := by
  split
  · subst_vars; exact word_mstore M _ v hv
  · exact word_mstore_disjoint M v (by omega)

theorem spread_sh_mod {sh : Nat} (hsh : sh < 4) (v : Nat) :
    spread v * 2 ^ sh %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      spread v * 2 ^ sh := Nat.mod_eq_of_lt (spread_sh_lt hsh)

theorem modL_lt (v : Nat) :
    v % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < 2 ^ 256 :=
  Nat.mod_lt _ (by norm_num)

theorem S_xor (a b sh : Nat) : spread (a ^^^ b) * 2 ^ sh = spread a * 2 ^ sh ^^^ spread b * 2 ^ sh := by
  rw [spread_xor, mul_two_pow_xor]

set_option hygiene false in
/-- Close a case of `mu0_value`: drop zero lanes and `mod 2^256`, normalise the xors. -/
macro "mu_fin'" : tactic => `(tactic| (
  simp only [hS0, Nat.xor_zero, Nat.zero_xor, xor_modL', word_mod, spread_sh_mod hsh, Nat.mod_mod]
  try simp only [Nat.xor_assoc, Nat.xor_comm, xor_left_comm'']))

set_option maxHeartbeats 1000000 in
/-- The state words after the absorbing path of `mu0`. -/
theorem mu0_value {m m8 m9 m10 m11a m11 tr cd : ByteArray} {sh : Nat} (hsh : sh < 4)
    (htr : tr.size = 64) (hcd : 3732 ≤ cd.size) (hml : cd.size - 3732 ≤ 69)
    (hTRL : ∀ x, x < 8 → word m (64768 + 32 * x) = le64 tr (8 * x))
    (h8 : ∀ x, word m8 (32 * x) = if x < 8 then
        (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
        else word m (32 * x))
    (h9 : ∀ x, x < 25 → word m9 (32 * x) = if 8 ≤ x ∧ x < 20 then
        word m8 (32 * x) ^^^ spread (trLane cd 3730
          115792089237316195417293883273301227089434195242432897623355228563449095127040 3 (x - 8)) *
            2 ^ sh
        else word m8 (32 * x))
    (h10 : m10 = MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded
      ((word m9 256 ^^^ sprNet (65280 &&& word cd 3730 /
        6901746346790563787434755862277025452451108972170386555162524223799296 |||
      word cd 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) *
        2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)
    (h11a : m11a = MachineState.writeBytes m10 (Data.Bytes.natToBytesPadded
      ((sprNet (31 * 2 ^ ((7 &&& (66 + (cd.size - 3732))) * 8)) * 2 ^ sh ^^^ word m10 (0 + (66 + (cd.size - 3732)) / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32)
      (0 + (66 + (cd.size - 3732)) / 8 * 32))
    (h11 : m11 = MachineState.writeBytes m11a (Data.Bytes.natToBytesPadded
      ((word m11a 512 ^^^
          7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)
    {x : Nat} (hx : x < 25) :
    word m11 (32 * x) = if x < 17 then
        word m (32 * x) ^^^ spread (le64 (muBlock tr cd) (8 * x)) * 2 ^ sh
      else word m (32 * x) := by
  have hP8 : 8 ≤ (66 + (cd.size - 3732)) / 8 := by omega
  have hP16 : (66 + (cd.size - 3732)) / 8 ≤ 16 := by omega
  have hFIX : sprNet (65280 &&& word cd 3730 /
        6901746346790563787434755862277025452451108972170386555162524223799296 |||
      word cd 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) =
      spread (byteAt cd 3730 + 256 * byteAt cd 3731) := by
    rw [mu0_fix_eq, sprNet_eq (mu0_fix_lt cd)]
  have hPAD : sprNet (31 * 2 ^ ((7 &&& (66 + (cd.size - 3732))) * 8)) = spread (31 * 2 ^ (8 * ((66 + (cd.size - 3732)) % 8))) := by
    rw [mu0_pad_eq, sprNet_eq (mu0_pad_lt _)]
  have hTOP : (7237005577332262213973186563042994240829374041602535252466099000494570602496 : Nat) =
      spread (2 ^ 63) := spread_top.symm
  have hw10 : ∀ y, word m10 (32 * y) = if y = 8 then
      (word m9 256 ^^^ spread (byteAt cd 3730 + 256 * byteAt cd 3731) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      else word m9 (32 * y) := by
    intro y; rw [h10, word_wb32 _ (by omega) (by norm_num) (modL_lt _), hFIX]
    by_cases hy : y = 8
    · rw [if_pos (by omega), if_pos hy]
    · rw [if_neg (by omega), if_neg hy]
  have hw11a : ∀ y, word m11a (32 * y) = if y = (66 + (cd.size - 3732)) / 8 then
      (spread (31 * 2 ^ (8 * ((66 + (cd.size - 3732)) % 8))) * 2 ^ sh ^^^ word m10 (32 * ((66 + (cd.size - 3732)) / 8))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      else word m10 (32 * y) := by
    intro y
    rw [h11a, word_wb32 _ (by omega) (by omega) (modL_lt _), hPAD,
      show 0 + (66 + (cd.size - 3732)) / 8 * 32 = 32 * ((66 + (cd.size - 3732)) / 8) by ring]
    by_cases hy : y = (66 + (cd.size - 3732)) / 8
    · rw [if_pos (by omega), if_pos hy]
    · rw [if_neg (by omega), if_neg hy]
  have hw11 : word m11 (32 * x) = if x = 16 then
      (word m11a (32 * 16) ^^^ spread (2 ^ 63) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      else word m11a (32 * x) := by
    rw [h11, word_wb32 _ (by omega) (by norm_num) (modL_lt _), hTOP]
    by_cases hy : x = 16
    · rw [if_pos (by omega), if_pos hy]
    · rw [if_neg (by omega), if_neg hy]
  have hS0 : spread 0 * 2 ^ sh = 0 := by rw [spread_zero', Nat.zero_mul]
  have h9' : ∀ y, 8 ≤ y → y ≤ 16 → word m9 (32 * y) = word m (32 * y) ^^^ spread (muCd cd y) * 2 ^ sh := by
    intro y h1 h2
    rw [h9 y (by omega), if_pos ⟨h1, by omega⟩, h8, if_neg (by omega), mu0_trLane cd h1 (by omega),
      if_pos h2]
  have h9_256 : word m9 256 = word m 256 ^^^ spread (muCd cd 8) * 2 ^ sh := h9' 8 (by omega) (by omega)
  rw [hw11]
  by_cases hx17 : x < 17
  · rw [if_pos hx17, le64_muBlock htr hcd hml hx17, S_xor, S_xor, S_xor, S_xor]
    by_cases hx8 : x < 8
    · rw [if_neg (show ¬ x = 16 by omega), hw11a, if_neg (show ¬ x = (66 + (cd.size - 3732)) / 8 by omega), hw10,
        if_neg (show ¬ x = 8 by omega), h9 x hx, if_neg (show ¬ (8 ≤ x ∧ x < 20) by omega), h8,
        if_pos hx8, hTRL x hx8, sprNet_eq (le64_lt' _ _),
        muTr, if_pos hx8, muCd, if_neg (show ¬ 8 ≤ x by omega), muFix, if_neg (show ¬ x = 8 by omega),
        muPad, if_neg (show ¬ x = (66 + (cd.size - 3732)) / 8 by omega), muTop, if_neg (show ¬ x = 16 by omega)]
      mu_fin'
    · rw [muTr, if_neg hx8, muFix, muPad, muTop]
      by_cases h16 : x = 16
      · subst h16
        simp only [eq_self_iff_true, Nat.reduceEqDiff, ↓reduceIte]
        rw [hw11a 16]
        by_cases hP : 16 = (66 + (cd.size - 3732)) / 8
        · rw [if_pos hP, if_pos hP, ← hP, hw10 16]
          simp only [Nat.reduceEqDiff, ↓reduceIte]
          rw [h9' 16 (by omega) (by omega)]
          mu_fin'
        · rw [if_neg hP, if_neg hP, hw10 16]
          simp only [Nat.reduceEqDiff, ↓reduceIte]
          rw [h9' 16 (by omega) (by omega)]
          mu_fin'
      · rw [if_neg h16, if_neg h16, hw11a x]
        by_cases hP : x = (66 + (cd.size - 3732)) / 8
        · rw [if_pos hP, if_pos hP, ← hP, hw10 x]
          by_cases h8' : x = 8
          · subst h8'
            simp only [eq_self_iff_true, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul]
            rw [h9_256]
            mu_fin'
          · rw [if_neg h8', if_neg h8', h9' x (by omega) (by omega)]
            mu_fin'
        · rw [if_neg hP, if_neg hP, hw10 x]
          by_cases h8' : x = 8
          · subst h8'
            simp only [eq_self_iff_true, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul]
            rw [h9_256]
            mu_fin'
          · rw [if_neg h8', if_neg h8', h9' x (by omega) (by omega)]
            mu_fin'
  · rw [if_neg hx17, if_neg (show ¬ x = 16 by omega), hw11a, if_neg (show ¬ x = (66 + (cd.size - 3732)) / 8 by omega),
      hw10, if_neg (show ¬ x = 8 by omega), h9 x hx]
    by_cases h20 : x < 20
    · rw [if_pos ⟨by omega, h20⟩, h8, if_neg (show ¬ x < 8 by omega), mu0_trLane cd (by omega) h20,
        if_neg (show ¬ x ≤ 16 by omega), hS0, Nat.xor_zero]
    · rw [if_neg (show ¬ (8 ≤ x ∧ x < 20) by omega), h8, if_neg (show ¬ x < 8 by omega)]

end MlDsaOpt44.Proofs.WP4
