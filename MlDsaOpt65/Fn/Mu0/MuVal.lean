import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt65.Fn.Mu0.MuMath
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/MuVal.lean` by `scripts/proofgen_port.py 65` --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195 --sub 64768=89344 --sub 64800=89376 --sub 64832=89408 --sub 64864=89440 --sub 64896=89472 --sub 64928=89504 --sub 64960=89536 --sub 64992=89568 --sub 12633=13592 --sub 12653=13613 --sub 12675=13636 --sub 12697=13659 --sub 12719=13682 --sub 12741=13705 --sub 12763=13728 --sub 12785=13751 --sub 12844=13810 --sub 12870=13836 --sub 12905=13871 --path Fn/Sponge/=Fn/Mu0/; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
/-!
# Values computed by `mu0` in terms of the lane contributions of `MuMath`
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open MlDsaOptCommon

/-- The two signature bytes `mu0` xors back out of lane 8. -/
theorem mu0_fix_eq (cd : ByteArray) :
    (65280 &&& word cd 5259 / 6901746346790563787434755862277025452451108972170386555162524223799296 |||
      word cd 5259 / 452312848583266388373324160190187140051835877600158453279131187530910662656) =
      byteAt cd 5259 + 256 * byteAt cd 5260 := by
  have ha := byteAt_lt cd 5259
  have hb := byteAt_lt cd 5260
  rw [show (6901746346790563787434755862277025452451108972170386555162524223799296 : Nat) = 2 ^ 232
    by norm_num, show (452312848583266388373324160190187140051835877600158453279131187530910662656 : Nat)
    = 2 ^ 248 by norm_num]
  have hw := word_lt cd 5259
  apply eq_of_testBit_lt (n := 16)
  · refine Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)) ?_
    have : word cd 5259 / 2 ^ 248 < 2 ^ 8 := by omega
    omega
  · omega
  · intro j hj
    rw [show byteAt cd 5259 + 256 * byteAt cd 5260 = byteAt cd 5259 + byteAt cd 5260 * 2 ^ 8 by ring,
      testBit_add_two_pow_mul (by omega)]
    interval_cases j <;>
      simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_div_two_pow, testBit_word, testBit_lit,
        Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT, decide_true,
        Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, if_true, if_false, decide_false,
        Nat.lt_irrefl, Nat.reduceLeDiff, ↓reduceIte, Nat.testBit_lt_two_pow hw]

theorem mu0_fix_lt (cd : ByteArray) : byteAt cd 5259 + 256 * byteAt cd 5260 < 2 ^ 64 := by
  have := byteAt_lt cd 5259; have := byteAt_lt cd 5260; omega

theorem mu0_pad_eq (mlen : Nat) :
    31 * 2 ^ ((7 &&& 66 + mlen) * 8) = 31 * 2 ^ (8 * ((66 + mlen) % 8)) := by
  rw [Nat.and_comm, show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mul_comm _ 8]

theorem mu0_pad_lt (mlen : Nat) : 31 * 2 ^ (8 * ((66 + mlen) % 8)) < 2 ^ 64 := by
  have h : (66 + mlen) % 8 < 8 := Nat.mod_lt _ (by omega)
  generalize (66 + mlen) % 8 = r at h
  interval_cases r <;> norm_num

theorem spread_top : spread (2 ^ 63) =
    7237005577332262213973186563042994240829374041602535252466099000494570602496 := by
  unfold spread; decide +kernel

theorem spread_zero' : spread 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [testBit_spread]; simp

theorem spread_xor (a b : Nat) : spread (a ^^^ b) = spread a ^^^ spread b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_spread, testBit_spread, testBit_spread, Nat.testBit_xor]
  cases decide (i % 4 = 0) <;> cases decide (i / 4 < 64) <;> simp

theorem mul_two_pow_xor (a b k : Nat) : (a ^^^ b) * 2 ^ k = a * 2 ^ k ^^^ b * 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mul_two_pow, Nat.testBit_xor]
  cases decide (k ≤ i) <;> simp

/-- The masked last group of `mu0`'s `trabs` keeps only its first lane. -/
theorem lm_lane (B : Nat) {j : Nat} (hj : j < 4) :
    (115792089237316195417293883273301227089434195242432897623355228563449095127040 &&& B) /
      2 ^ (192 - 64 * j) % 2 ^ 64 = if j = 0 then B / 2 ^ 192 % 2 ^ 64 else 0 := by
  have hLM : (115792089237316195417293883273301227089434195242432897623355228563449095127040 : Nat) =
      (2 ^ 64 - 1) * 2 ^ 192 := by norm_num
  apply Nat.eq_of_testBit_eq; intro b
  rw [hLM, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one]
  split
  · rename_i h; subst h
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases hb : b < 64 <;> simp [hb]
  · simp only [Nat.zero_testBit]
    by_cases hb : b < 64
    · simp [hb, show ¬ (192 ≤ b + (192 - 64 * j)) by omega]
    · simp [hb]

/-- `mu0`'s `trabs` lane `x − 8` is the calldata contribution `muCd` (`x ≤ 16`), else `0`. -/
theorem mu0_trLane (cd : ByteArray) {x : Nat} (h8 : 8 ≤ x) (h20 : x < 20) :
    trLane cd 5259 115792089237316195417293883273301227089434195242432897623355228563449095127040 3
      (x - 8) = if x ≤ 16 then muCd cd x else 0 := by
  have hu : x - 8 = 4 * ((x - 8) / 4) + (x - 8) % 4 := by omega
  rw [hu, trLane_eq _ _ _ _ _ (Nat.mod_lt _ (by omega))]
  unfold muCd
  rw [if_pos h8]
  by_cases hi : (x - 8) / 4 + 1 = 3
  · rw [if_pos hi, lm_lane _ (Nat.mod_lt _ (by omega))]
    by_cases hj : (x - 8) % 4 = 0
    · rw [if_pos hj, if_pos (by omega), show (192 : Nat) = 192 - 64 * 0 from rfl,
        bsw_lane _ _ (by omega)]
      congr 1; omega
    · rw [if_neg hj, if_neg (by omega)]
  · rw [if_neg hi, bsw_lane _ _ (Nat.mod_lt _ (by omega)), if_pos (by omega)]
    congr 1; omega

end MlDsaOpt65.Proofs.WP4
