import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Group
import MlDsaOpt44.Fn.Sponge
import MlDsaOpt44.Math.SpongeG234
set_option warningAsError true
/-!
# Pure lemmas of the packed window (`seg_win`)

* `kmove_*`: the three `kmove` calls of the window move interleaved slots;
* `lmerge_lanes`: `lmerge` with `ma` = lane 1 and `sl = 128`;
* `le64_mu0Bytes`: μ's block 0 as `mub0` absorbs it is the first block of `padMu`;
* `accAt_of_acc4`: `pass3f4`'s word is `Â ẑ` lane-wise.
-/

namespace MlDsaOpt44.Proofs.Ex

open EvmSemantics
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs

private theorem bit256 {c : Nat} (hc : c < 2 ^ 256) (p : Nat → Bool)
    (h : ∀ i, i < 256 → c.testBit i = p (i % 4)) (i : Nat) :
    c.testBit i = (decide (i < 256) && p (i % 4)) := by
  by_cases hi : i < 256
  · simp [hi, h i hi]
  · have : c < 2 ^ i := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hi, Nat.testBit_lt_two_pow this]

private theorem m3_bit (i : Nat) :
    (0x3333333333333333333333333333333333333333333333333333333333333333 : Nat).testBit i =
      (decide (i < 256) && decide (i % 4 < 2)) :=
  bit256 (by norm_num) (fun k => decide (k < 2)) (by decide +kernel) i

private theorem mc_bit (i : Nat) :
    (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Nat).testBit i =
      (decide (i < 256) && decide (2 ≤ i % 4)) :=
  bit256 (by norm_num) (fun k => decide (2 ≤ k)) (by decide +kernel) i

private theorem m2_bit (i : Nat) :
    (0x2222222222222222222222222222222222222222222222222222222222222222 : Nat).testBit i =
      (decide (i < 256) && decide (i % 4 = 1)) :=
  bit256 (by norm_num) (fun k => decide (k = 1)) (by decide +kernel) i

private theorem md_bit (i : Nat) :
    (0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd : Nat).testBit i =
      (decide (i < 256) && !decide (i % 4 = 1)) :=
  bit256 (by norm_num) (fun k => !decide (k = 1)) (by decide +kernel) i

set_option linter.unusedVariables false in
/-- `kmove` with `sl = 0`, `sr = 2`, `msk` = slots 0, 1, `keep` = slots 2, 3:
slots 2, 3 of `v` move to slots 0, 1. -/
theorem kmove_down2 (v w : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) (hw : ∀ k, k < 4 → w k < 2 ^ 64) :
    (il v * 2 ^ 0 % 2 ^ 256 / 2 ^ 2 &&&
        0x3333333333333333333333333333333333333333333333333333333333333333) |||
      (il w &&& 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) =
    il fun k => if k < 2 then v (k + 2) else w k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_div_two_pow, Nat.pow_zero,
    Nat.mul_one, Nat.mod_eq_of_lt (il_lt v), m3_bit, mc_bit, testBit_il, testBit_il, testBit_il]
  by_cases hi : i < 256
  · have h4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have e2 : i % 4 < 2 → (i + 2) % 4 = i % 4 + 2 ∧ (i + 2) / 4 = i / 4 ∧ i + 2 < 256 := by omega
    rcases h4 with h | h | h | h <;> simp_all
  · simp [hi, show ¬ i + 2 < 256 by omega]

set_option linter.unusedVariables false in
/-- `kmove` with `src = KS`, `sl = 2`, `sr = 0`, `msk` = slots 2, 3, `keep` = slots 0, 1:
slots 0, 1 are copied to slots 2, 3. -/
theorem kmove_up2 (v : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) :
    (il v * 2 ^ 2 % 2 ^ 256 / 2 ^ 0 &&&
        0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) |||
      (il v &&& 0x3333333333333333333333333333333333333333333333333333333333333333) =
    il fun k => if k < 2 then v k else v (k - 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.pow_zero, Nat.div_one, Nat.testBit_mod_two_pow,
    Nat.testBit_mul_two_pow, mc_bit, m3_bit, testBit_il, testBit_il, testBit_il]
  by_cases hi : i < 256
  · have h4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have e2 : 2 ≤ i % 4 → (i - 2) % 4 = i % 4 - 2 ∧ (i - 2) / 4 = i / 4 ∧ i - 2 < 256 ∧ 2 ≤ i := by omega
    rcases h4 with h | h | h | h <;> simp_all
  · simp [hi]

set_option linter.unusedVariables false in
/-- `kmove` with `sl = sr = 0`, `msk` = slot 1, `keep` = slots 0, 2, 3: slot 1 from `v`. -/
theorem kmove_slot1 (v w : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) (hw : ∀ k, k < 4 → w k < 2 ^ 64) :
    (il v * 2 ^ 0 % 2 ^ 256 / 2 ^ 0 &&&
        0x2222222222222222222222222222222222222222222222222222222222222222) |||
      (il w &&& 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd) =
    il fun k => if k = 1 then v 1 else w k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.pow_zero, Nat.mul_one, Nat.div_one,
    Nat.mod_eq_of_lt (il_lt v), m2_bit, md_bit, testBit_il, testBit_il, testBit_il]
  by_cases hi : i < 256
  · by_cases h : i % 4 = 1 <;> simp [hi, h]
  · simp [hi]

/-- `lmerge` with `ma` = lane 1 and `sl = 128`: lane 1 from `a`, lanes 2, 3
from lanes 0, 1 of `b`. -/
theorem lmerge_lanes (a b : Nat) :
    lane (b * 2 ^ 128 % 2 ^ 256 ^^^ ((a ^^^ b * 2 ^ 128 % 2 ^ 256) &&& 0xffffffffffffffff0000000000000000)) 1 =
        lane a 1 ∧
      lane (b * 2 ^ 128 % 2 ^ 256 ^^^ ((a ^^^ b * 2 ^ 128 % 2 ^ 256) &&& 0xffffffffffffffff0000000000000000)) 2 =
        lane b 0 ∧
      lane (b * 2 ^ 128 % 2 ^ 256 ^^^ ((a ^^^ b * 2 ^ 128 % 2 ^ 256) &&& 0xffffffffffffffff0000000000000000)) 3 =
        lane b 1 := by
  have hm : (0xffffffffffffffff0000000000000000 : Nat) = (2 ^ 64 - 1) * 2 ^ 64 := by norm_num
  rw [hm]
  have key : ∀ j, (b * 2 ^ 128 % 2 ^ 256 ^^^
      ((a ^^^ b * 2 ^ 128 % 2 ^ 256) &&& (2 ^ 64 - 1) * 2 ^ 64)).testBit j =
      if 64 ≤ j ∧ j < 128 then a.testBit j else (decide (128 ≤ j ∧ j < 256) && b.testBit (j - 128)) := by
    intro j
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
      Nat.testBit_two_pow_sub_one]
    rcases (by omega : j < 64 ∨ (64 ≤ j ∧ j < 128) ∨ (128 ≤ j ∧ j < 256) ∨ 256 ≤ j) with h | h | h | h
    · simp [show ¬ 64 ≤ j by omega, show ¬ 128 ≤ j by omega]
    · simp [h, show ¬ 128 ≤ j by omega, show j - 64 < 64 by omega, show j < 256 by omega]
    · simp [h, show ¬ j < 128 by omega, show ¬ j - 64 < 64 by omega, show 64 ≤ j by omega]
    · simp [show ¬ j < 256 by omega, show ¬ j < 128 by omega, show ¬ j - 64 < 64 by omega]
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;> unfold lane <;>
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, key] <;> by_cases hj : j < 64
  · simp [hj, show 64 ≤ j + 64 * 1 by omega, show j + 64 * 1 < 128 by omega]
  · simp [hj]
  · simp [hj, show ¬ j + 64 * 2 < 128 by omega, show 128 ≤ j + 64 * 2 by omega,
      show j + 64 * 2 < 256 by omega, show j + 64 * 2 - 128 = j by omega]
  · simp [hj]
  · simp [hj, show ¬ j + 64 * 3 < 128 by omega, show 128 ≤ j + 64 * 3 by omega,
      show j + 64 * 3 < 256 by omega, show j + 64 * 3 - 128 = j + 64 by omega]
  · simp [hj]

set_option linter.unusedVariables false in
theorem flagBit_eq_lane (w s : Nat) (hs : s < 4) : flagBit w s = lane w s / 2 ^ 23 % 2 := by
  unfold flagBit lane
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 = 2 ^ 23 * 2 ^ 41 by norm_num,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 41)]

set_option linter.unusedVariables false in
/-- μ's block 0 as `mub0` absorbs it is the first block of `padMu`. -/
theorem le64_mu0Bytes {cd : ByteArray} (hcd : HDR ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (mu0Bytes (trOf cd) cd) (8 * x) = le64 (padMu cd) (8 * x) := by
  unfold mu0Bytes
  split
  · rfl
  · rename_i h
    unfold padMu
    apply le64_congr
    intro k hk
    have hs : 8 * x + k < (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size := by
      rw [ByteArray.size_append, ByteArray.size_append, trOf_size,
        show (ByteArray.mk #[(0 : UInt8), 0]).size = 2 from rfl]
      unfold msgOf mlenOf HDR at *
      simp [ByteArray.size_extract]
      omega
    rw [byteAt_pad_lt _ _ _ hs]

/-! ## `pass3f4`'s word -/

private theorem okA_get {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 4) (hs : s < 4) :
    (aOf cd r s).isSome = true := by
  unfold okA at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at this
  exact this s (List.mem_range.mpr hs)

private theorem okCol_of_okA {cd : ByteArray} (h : okA cd = true) {s : Nat} (hs : s < 4) :
    okCol cd s = true := by
  unfold okCol
  rw [List.all_eq_true]
  intro r hr
  exact okA_get h (List.mem_range.mp hr) hs

private theorem okCol3_of_okA {cd : ByteArray} (h : okA cd = true) {s : Nat} (hs : s < 4) :
    okCol3 cd s = true := by
  unfold okCol3
  rw [List.all_eq_true]
  intro r hr
  exact okA_get h (by have := List.mem_range.mp hr; omega) hs

private theorem aD_lt23 {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 4) (hs : s < 4)
    {t : Nat} (ht : t < 256) : ((aD cd r s)[t]!).toNat < 2 ^ 23 := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (okA_get h hr hs)
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  have := ((rejNTTPoly_range _ a ha).2 t ht)
  have hq : (Fips204.q : Int) < 2 ^ 23 := by norm_num [Fips204.q]
  omega

private theorem sum_range4 (f : Nat → Int) : ((List.range 4).map f).sum = f 0 + f 1 + f 2 + f 3 := by
  simp [List.range_succ]; ring

private theorem and_top {y n : Nat} (hy : y < 2 ^ 256) (hn : n ≤ 256) :
    y &&& (2 ^ 256 - 2 ^ n) = y / 2 ^ n * 2 ^ n := by
  have e : 2 ^ 256 - 2 ^ n = (2 ^ (256 - n) - 1) * 2 ^ n := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hn]
  rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h : n ≤ i
  · have e1 : i - n + n = i := by omega
    by_cases h2 : i < 256
    · simp [h, e1, show i - n < 256 - n by omega]
    · have : y < 2 ^ i := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [h, e1, Nat.testBit_lt_two_pow this]
  · simp [h]

private theorem mul_lt51 {a b : Nat} (ha : a < 2 ^ 23) (hb : b < 2 ^ 28) : a * b < 2 ^ 51 :=
  lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by norm_num)

/-- The arithmetic of `acc4Word`: no carries between lanes. -/
private theorem acc4_core {w0 w1 w2 w3 w4 z : Nat} (A : Nat → Nat → Nat)
    (hA : ∀ r s, r < 4 → s < 4 → A r s < 2 ^ 23)
    (hz : ∀ k, k < 4 → lane z k < 2 ^ 28) (hzlt : z < 2 ^ 256)
    (h0 : w0 = pack4 fun r => A r 0) (h1 : w1 = pack4 fun r => A r 1)
    (h2 : ∀ r, r < 3 → lane w2 (r + 1) = A r 2) (hw2 : w2 < 2 ^ 256)
    (h3 : lane w3 2 = A 3 3) (h3' : lane w3 3 = A 3 2) (hw3 : w3 < 2 ^ 256)
    (h4 : ∀ r, r < 3 → lane w4 (r + 1) = A r 3) (hw4 : w4 < 2 ^ 256) :
    (w0 * lane z 0 + w1 * lane z 1 + w2 / 2 ^ 64 * lane z 2 +
      ((w3 &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192)) +
      w4 / 2 ^ 64 * lane z 3) % 2 ^ 256 =
    pack4 fun r => A r 0 * lane z 0 + A r 1 * lane z 1 + A r 2 * lane z 2 + A r 3 * lane z 3 := by
  have ez : z / 2 ^ 128 = lane z 2 + 2 ^ 64 * lane z 3 := by
    unfold lane; norm_num; omega
  have e2 : w2 / 2 ^ 64 = A 0 2 + 2 ^ 64 * A 1 2 + 2 ^ 128 * A 2 2 := by
    rw [← h2 0 (by omega), ← h2 1 (by omega), ← h2 2 (by omega)]
    unfold lane; norm_num; omega
  have e4 : w4 / 2 ^ 64 = A 0 3 + 2 ^ 64 * A 1 3 + 2 ^ 128 * A 2 3 := by
    rw [← h4 0 (by omega), ← h4 1 (by omega), ← h4 2 (by omega)]
    unfold lane; norm_num; omega
  have e3 : w3 / 2 ^ 128 = A 3 3 + 2 ^ 64 * A 3 2 := by
    rw [← h3, ← h3']
    unfold lane; norm_num; omega
  have hk : (w3 &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192) =
      2 ^ 192 * (A 3 3 * lane z 3 + A 3 2 * lane z 2) := by
    rw [show M64 * 2 ^ 192 = 2 ^ 256 - 2 ^ 192 by unfold M64; norm_num, and_top hw3 (by norm_num),
      and_top (Nat.mod_lt _ (by norm_num)) (by norm_num), e3, ez]
    have ex : (A 3 3 + 2 ^ 64 * A 3 2) * 2 ^ 128 * (lane z 2 + 2 ^ 64 * lane z 3) =
        2 ^ 128 * (A 3 3 * lane z 2) + 2 ^ 192 * (A 3 3 * lane z 3 + A 3 2 * lane z 2) +
          2 ^ 256 * (A 3 2 * lane z 3) := by ring
    have b1 := mul_lt51 (hA 3 3 (by omega) (by omega)) (hz 2 (by omega))
    have b2 := mul_lt51 (hA 3 3 (by omega) (by omega)) (hz 3 (by omega))
    have b3 := mul_lt51 (hA 3 2 (by omega) (by omega)) (hz 2 (by omega))
    rw [ex]
    generalize A 3 3 * lane z 2 = p at *
    generalize A 3 3 * lane z 3 = c1 at *
    generalize A 3 2 * lane z 2 = c2 at *
    generalize A 3 2 * lane z 3 = d at *
    omega
  have hlt : (pack4 fun r => A r 0 * lane z 0 + A r 1 * lane z 1 + A r 2 * lane z 2 + A r 3 * lane z 3) <
      2 ^ 256 := pack4_lt fun r hr => by
    have := mul_lt51 (hA r 0 hr (by omega)) (hz 0 (by omega))
    have := mul_lt51 (hA r 1 hr (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA r 2 hr (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA r 3 hr (by omega)) (hz 3 (by omega))
    omega
  refine (congrArg (· % 2 ^ 256) ?_).trans (Nat.mod_eq_of_lt hlt)
  rw [hk, h0, h1, e2, e4]
  unfold pack4
  ring

/-- `pass3f4`'s words are `Â ẑ` (bounded representatives mod `q`) when `A` exists. -/
theorem accAt_of_acc4 {cd m m' : ByteArray} (hzh : ZHatAt m cd)
    (hcw : ColAt m CW cd 0) (hhp : ColAt m HP cd 1) (hsb : Col3At m SB cd 2) (hb3 : Col3At m ABUF cd 3)
    (hE : okA cd = true → ∀ t, t < 256 →
      lane (word m (SB + 8192 + 32 * t)) 2 = ((aD cd 3 3)[t]!).toNat ∧
      lane (word m (SB + 8192 + 32 * t)) 3 = ((aD cd 3 2)[t]!).toNat)
    (hacc : ∀ t, t < 256 → word m' (ACC + 32 * t) = acc4Word m t) :
    AccAt m' cd := by
  intro hok r hr t ht
  have hz : ∀ k, k < 4 → lane (word m (ZH + 32 * t)) k < 2 ^ 28 := fun k hk => (hzh k hk t ht).1
  have hA : ∀ r s, r < 4 → s < 4 → ((aD cd r s)[t]!).toNat < 2 ^ 23 := fun r s hr hs =>
    aD_lt23 hok hr hs ht
  obtain ⟨hE2, hE3⟩ := hE hok t ht
  have hw : word m' (ACC + 32 * t) = pack4 fun r =>
      ((aD cd r 0)[t]!).toNat * lane (word m (ZH + 32 * t)) 0 +
        ((aD cd r 1)[t]!).toNat * lane (word m (ZH + 32 * t)) 1 +
        ((aD cd r 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2 +
        ((aD cd r 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 := by
    rw [hacc t ht]
    exact acc4_core (fun r s => ((aD cd r s)[t]!).toNat) hA hz (word_lt _ _)
      (hcw (okCol_of_okA hok (by omega)) t ht) (hhp (okCol_of_okA hok (by omega)) t ht)
      (hsb (okCol3_of_okA hok (by omega)) t ht) (word_lt _ _) hE2 hE3 (word_lt _ _)
      (hb3 (okCol3_of_okA hok (by omega)) t ht) (word_lt _ _)
  have hle : ∀ r, r < 4 → ((aD cd r 0)[t]!).toNat * lane (word m (ZH + 32 * t)) 0 +
        ((aD cd r 1)[t]!).toNat * lane (word m (ZH + 32 * t)) 1 +
        ((aD cd r 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2 +
        ((aD cd r 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 < 2 ^ 57 := fun r hr => by
    have := mul_lt51 (hA r 0 hr (by omega)) (hz 0 (by omega))
    have := mul_lt51 (hA r 1 hr (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA r 2 hr (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA r 3 hr (by omega)) (hz 3 (by omega))
    omega
  rw [hw, lane_pack4 (fun r hr => by have := hle r hr; omega) hr]
  refine ⟨hle r hr, ?_⟩
  have hnn : ∀ s, s < 4 → (((aD cd r s)[t]!).toNat : Int) = (aD cd r s)[t]! := fun s hs => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (okA_get hok hr hs)
    have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
    rw [hD]
    exact Int.toNat_of_nonneg ((rejNTTPoly_range _ a ha).2 t ht).1
  have hm : ∀ s, s < 4 → (lane (word m (ZH + 32 * t)) s : Int) % (Fips204.q : Int) =
      (zHat cd s)[t]! % (Fips204.q : Int) := fun s hs =>
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (hzh s hs t ht).2
  have hrow : (azRow cd r)[t]! = ((List.range 4).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum %
      (Fips204.q : Int) := by
    unfold azRow; exact getElem!_map_range 256 t _ ht
  rw [hrow, sum_range4]
  push_cast
  rw [hnn 0 (by omega), hnn 1 (by omega), hnn 2 (by omega), hnn 3 (by omega)]
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  have m0 := hm 0 (by omega)
  have m1 := hm 1 (by omega)
  have m2 := hm 2 (by omega)
  have m3 := hm 3 (by omega)
  exact Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.mul_left _ m0) (Int.ModEq.mul_left _ m1))
    (Int.ModEq.mul_left _ m2)) (Int.ModEq.mul_left _ m3)

end MlDsaOpt44.Proofs.Ex
