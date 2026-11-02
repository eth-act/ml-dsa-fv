import MlDsaOpt87.Fn.Decode.Lanes
import MlDsaOpt87.Fn.Decode.Defs
import MlDsaOpt44.Fn.Decode.ZMath
import MlDsa.Bridge44
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Meaning of one `dz` gather step (ML-DSA-87, WP G2)

20-bit twin of `MlDsaOpt44/Fn/Decode/ZMath.lean`, per lane:

* `zR_gW`: the raw word of step `kk` holds `20` bits of `V_k` from bit
  `gs + 20 kk` in lane `k`;
* `zv_pack`, `zf_lane`: the stored word is `K − raw` lane-wise, and the flag word
  has no `zFlagBit j` bit iff the lane-`j` raw value is in `(β, 2γ1 − β)`;
* `le_rawZ`: the bits of the little-endian windows are the packed fields `rawZ`
  (no calldata-size hypothesis: past the end both read zero bytes).
The lane lemmas `pack4_*` are the 44 ones.
-/

namespace MlDsaOpt87.Proofs.DecodeZ

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-! ## The gathered raw words -/

theorem mb_bit (j : Nat) :
    Nat.testBit 6582011952183088782295924477334101861609978183833731334774194175 j =
      decide (j % 64 < 20 ∧ j < 256) := by
  by_cases hj : j < 256
  · have h : ∀ j, j < 256 →
        Nat.testBit 6582011952183088782295924477334101861609978183833731334774194175 j =
          decide (j % 64 < 20 ∧ j < 256) := by decide +kernel
    exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by omega) (by omega : 256 ≤ j)))]
    exact (decide_eq_false (by omega)).symm

theorem m60_bit (j : Nat) : Nat.testBit 1152921504606846975 j = decide (j < 60) := by
  rw [show (1152921504606846975 : Nat) = 2 ^ 60 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem zR_lt (x : Nat) : zR x < 2 ^ 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

/-- Raw word `kk` of a gather step. -/
theorem zR_gW (V : Nat → Nat) (gs kk : Nat) (hkk : kk ≤ 2) :
    zR (gW gs (V 0) (V 1) (V 2) (V 3) / 2 ^ (20 * kk)) =
      pack4 (fun k => V k / 2 ^ (gs + 20 * kk) % 2 ^ 20) := by
  have hl : ∀ k, k < 4 → V k / 2 ^ (gs + 20 * kk) % 2 ^ 20 < 2 ^ 64 := fun k _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  apply eq_of_testBit_lt (zR_lt _) (pack4_lt' hl)
  intro i hi
  rw [pack4_testBit hl, if_pos hi, zR, Nat.testBit_and, mb_bit, Nat.testBit_div_two_pow, gW]
  simp only [Nat.testBit_or, Nat.testBit_and, m60_bit, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow,
    show (6277101735386680763835789423207666416102355444464034512896 : Nat) = 2 ^ 192 from rfl,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 from rfl,
    show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]
  by_cases hm : i % 64 < 20
  · obtain h | h | h | h : i / 64 = 0 ∨ i / 64 = 1 ∨ i / 64 = 2 ∨ i / 64 = 3 := by omega
    all_goals
      rw [h]
      simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
        Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
      exact congrArg (Nat.testBit _) (by omega)
  · simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]

/-! ## Stored and flag words -/

theorem zv_pack {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 20) :
    zv (pack4 r) = pack4 (fun k => 8904705 - r k) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [zv, pack4]; omega

theorem and_bits_eq_zero (y : Nat) :
    y &&& (2 ^ 52 + 2 ^ 25) = 0 ↔ y.testBit 52 = false ∧ y.testBit 25 = false := by
  constructor
  · intro h
    have e52 := congrArg (Nat.testBit · 52) h
    have e25 := congrArg (Nat.testBit · 25) h
    simp only [Nat.testBit_and, Nat.zero_testBit, Nat.reducePow, Nat.reduceAdd, testBit_lit, Bool.and_true] at e52 e25
    exact ⟨e52, e25⟩
  · rintro ⟨h52, h25⟩
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hj : j = 52
    · subst hj; rw [h52, Bool.false_and]
    by_cases hj' : j = 25
    · subst hj'; rw [h25, Bool.false_and]
    have : (2 ^ 52 + 2 ^ 25 : Nat).testBit j = false := by
      rw [show (2 ^ 52 + 2 ^ 25 : Nat) = 2 ^ 52 ||| 2 ^ 25 by decide, Nat.testBit_or,
        Nat.testBit_two_pow, Nat.testBit_two_pow]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [this, Bool.and_false]

/-- One lane of the flag word. -/
theorem lane_flag {r : Nat} (hr : r < 2 ^ 20) :
    ((24649847 + (8904705 - r)) ||| (120 + r) * 4294967296) &&& (2 ^ 52 + 2 ^ 25) = 0 ↔
      120 < r ∧ r < 1048456 := by
  rw [and_bits_eq_zero, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_false_iff, Bool.or_eq_false_iff,
    Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not, Nat.reducePow]
  omega

theorem zf_pack {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 20) :
    zf (pack4 r) = pack4 (fun k => (24649847 + (8904705 - r k)) ||| (120 + r k) * 4294967296) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  have ea : 154729597380716166674783250687686220605203381641598694267257626743 + zv (pack4 r) =
      pack4 (fun k => 24649847 + (8904705 - r k)) := by simp only [zv, pack4]; omega
  have eb : (753252208246401691701128614815432585550101215516341473116280 + pack4 r) * 4294967296 =
      pack4 (fun k => (120 + r k) * 4294967296) := by simp only [pack4]; omega
  unfold zf
  rw [ea, eb, pack4_or (fun k hk => by have := h k hk; omega) (fun k hk => by have := h k hk; omega)]

-- v4: `zFlagBit_pack`, `zf_lane` (v3 flag constants) removed with the v3 `dz` proof.

theorem zf_lt {R : Nat} (hR : R ≤ 6582011952183088782295924477334101861609978183833731334774194175) :
    zf R < 2 ^ 256 := by
  unfold zf zv
  exact Nat.or_lt_two_pow (by omega) (by omega)

theorem zf_zR_lt (x : Nat) : zf (zR x) < 2 ^ 256 := zf_lt Nat.and_le_left

/-! ## Calldata fields -/

/-- A byte of an extracted range is the calldata byte (zero past either end). -/
theorem byteAt_extract' {cd : ByteArray} {a b j : Nat} (hj : j < b - a) :
    (cd.extract a b)[j]!.toNat = byteAt cd (a + j) := by
  by_cases h : a + j < cd.size
  · rw [getElem!_pos (cd.extract a b) j (by rw [ByteArray.size_extract]; omega),
      ByteArray.getElem_extract, byteAt, dif_pos h]
  · rw [getElem!_neg (cd.extract a b) j (by rw [ByteArray.size_extract]; omega), byteAt, dif_neg h]
    rfl

theorem bitsToInteger_succ (v : ByteArray) (p c : Nat) :
    Fips204.bitsToInteger v p (c + 1) = Fips204.bitsToInteger v p c + Fips204.bit v (p + c) * 2 ^ c := by
  simp [Fips204.bitsToInteger, List.range_succ, List.map_append, List.sum_append]

theorem div_mod_eq_bitsToInteger (v : ByteArray) (x s p : Nat) :
    ∀ c, (∀ t, t < c → x / 2 ^ (s + t) % 2 = Fips204.bit v (p + t)) →
      x / 2 ^ s % 2 ^ c = Fips204.bitsToInteger v p c
  | 0, _ => by simp [Fips204.bitsToInteger, Nat.mod_one]
  | c + 1, h => by
    rw [Nat.mod_pow_succ, bitsToInteger_succ,
      div_mod_eq_bitsToInteger v x s p c (fun t ht => h t (by omega)),
      Nat.div_div_eq_div_mul, ← Nat.pow_add, h c (by omega), Nat.mul_comm]

/-- The `20` bits of window `k` (of row group `G`) from bit `60 g + 20 kk` are the field
`rawZ` of polynomial `4 G + k`. -/
theorem le_rawZ (cd : ByteArray) {G u g kk k : Nat} (hg : g ≤ 3) (hkk : kk ≤ 2)
    (ht : 4 * u + 3 * g + kk < 256) :
    leNat cd (Z0 + 2560 * G + 10 * u + 640 * k) 32 / 2 ^ (60 * g + 20 * kk) % 2 ^ 20 =
      rawZ cd (4 * G + k) (4 * u + 3 * g + kk) := by
  unfold rawZ
  apply div_mod_eq_bitsToInteger
  intro j hj
  rw [testBit_eq_div_mod, leNat_bit, if_pos (by omega), Fips204.bit,
    byteAt_extract' (by omega), testBit_eq_div_mod,
    show Z0 + 2560 * G + 10 * u + 640 * k + (60 * g + 20 * kk + j) / 8 =
      Z0 + 640 * (4 * G + k) + (20 * (4 * u + 3 * g + kk) + j) / 8 by omega,
    show (60 * g + 20 * kk + j) % 8 = (20 * (4 * u + 3 * g + kk) + j) % 8 by omega]

theorem rawZ_lt (cd : ByteArray) (k t : Nat) : rawZ cd k t < 2 ^ 20 := by
  unfold rawZ; rw [MlDsa.Bridge44.bitsToInteger_eq]
  exact MlDsa44.Proofs.Decode.bitsToInteger_lt _ _ 20

end MlDsaOpt87.Proofs.DecodeZ
