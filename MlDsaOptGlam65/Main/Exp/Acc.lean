import MlDsaOptGlam65.Main.Exp.Bound
import MlDsaOpt65.Main.Exp.Acc  -- `s3_okA_get`, `s3_aD_lt`, `s3_aD_cast`, `MlDsaOpt44.Math`
set_option warningAsError true
/-!
# The 42-call schedule's fused passes give `Â ẑ` (`accAt_glam`, glam ML-DSA-65)

`pass3f7` (`p3f7Word`, rows `0 … 3` into `ACC`): columns 0, 1, 2 from the row-packed
side buffers `CW`, `HP`, `HP + 0x2000` (`BufCol`), rows `0 … 2` of columns 3, 4
from lanes `1 … 3` of `ACC`, `SB + 0x2000` (`Col3Hi`, shifted down one lane), and
row 3 of columns 3, 4 from the Kronecker term: lane 3 of
`(ABUF & top128) · (ẑ4 ẑ3 as lanes 1, 0)` is `A[3][4] ẑ4 + A[3][3] ẑ3`.

`pass3f8` (`p3f8Word`, rows 4, 5 into `ACC + 0x2000`): `RowBuf` holds row `r`'s
columns `3, 2, 1, 0` in lanes `0 … 3`, so lane 3 of the full product with
`ẑ0 … ẑ3` is `Σ_{s<4} A[r][s] ẑ_s`; column 4 from lanes 0, 1 of `ABUF`.

Every lane sum is `< 5 · 2^51`, so there are no carries between lanes: the stored
lanes are `accSum … 5` (`p3f7_eq`, `p3f8_eq`).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open MlDsaOptCommon
open MlDsa

namespace Exp

/-! ## Word arithmetic -/

private theorem mul_lt51 {a b : Nat} (ha : a < 2 ^ 23) (hb : b < 2 ^ 28) : a * b < 2 ^ 51 :=
  lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by norm_num)

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

private theorem m64_top : M64 * 2 ^ 192 = 2 ^ 256 - 2 ^ 192 := by unfold M64; norm_num

/-- A word is the sum of its lanes. -/
private theorem word_lanes {w : Nat} (hw : w < 2 ^ 256) :
    w = lane w 0 + 2 ^ 64 * lane w 1 + 2 ^ 128 * lane w 2 + 2 ^ 192 * lane w 3 := by
  unfold lane; norm_num; omega

/-- Lane 3 of the product of two words with small lanes: the coefficient of `2^192`
(`Σ_{i+j=3} w_i z_j`), below it at most `2^192`. -/
private theorem mul_lane3 {w z : Nat} (hw : w < 2 ^ 256) (hz : z < 2 ^ 256)
    (hwl : ∀ k, k < 4 → lane w k < 2 ^ 23) (hzl : ∀ k, k < 4 → lane z k < 2 ^ 28) :
    ∃ L, L < 2 ^ 192 ∧ w * z % 2 ^ 256 = L + 2 ^ 192 *
      (lane w 0 * lane z 3 + lane w 1 * lane z 2 + lane w 2 * lane z 1 + lane w 3 * lane z 0) := by
  have ew := word_lanes hw
  have ez := word_lanes hz
  have a0 := hwl 0 (by omega); have a1 := hwl 1 (by omega)
  have a2 := hwl 2 (by omega); have a3 := hwl 3 (by omega)
  have b0 := hzl 0 (by omega); have b1 := hzl 1 (by omega)
  have b2 := hzl 2 (by omega); have b3 := hzl 3 (by omega)
  generalize lane w 0 = x0 at *; generalize lane w 1 = x1 at *
  generalize lane w 2 = x2 at *; generalize lane w 3 = x3 at *
  generalize lane z 0 = y0 at *; generalize lane z 1 = y1 at *
  generalize lane z 2 = y2 at *; generalize lane z 3 = y3 at *
  subst ew ez
  have e : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) =
      (x0 * y0 + 2 ^ 64 * (x0 * y1 + x1 * y0) + 2 ^ 128 * (x0 * y2 + x1 * y1 + x2 * y0)) +
      2 ^ 192 * (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0) +
      2 ^ 256 * (x1 * y3 + x2 * y2 + x3 * y1 + 2 ^ 64 * (x2 * y3 + x3 * y2) + 2 ^ 128 * (x3 * y3)) := by
    ring
  rw [e]
  have p00 := mul_lt51 a0 b0; have p01 := mul_lt51 a0 b1; have p10 := mul_lt51 a1 b0
  have p02 := mul_lt51 a0 b2; have p11 := mul_lt51 a1 b1; have p20 := mul_lt51 a2 b0
  have p03 := mul_lt51 a0 b3; have p12 := mul_lt51 a1 b2; have p21 := mul_lt51 a2 b1
  have p30 := mul_lt51 a3 b0
  refine ⟨x0 * y0 + 2 ^ 64 * (x0 * y1 + x1 * y0) + 2 ^ 128 * (x0 * y2 + x1 * y1 + x2 * y0), ?_, ?_⟩
  · generalize x0 * y0 = q00 at *; generalize x0 * y1 = q01 at *; generalize x1 * y0 = q10 at *
    generalize x0 * y2 = q02 at *; generalize x1 * y1 = q11 at *; generalize x2 * y0 = q20 at *
    omega
  · generalize x1 * y3 + x2 * y2 + x3 * y1 + 2 ^ 64 * (x2 * y3 + x3 * y2) + 2 ^ 128 * (x3 * y3) = R
    generalize x0 * y0 = q00 at *; generalize x0 * y1 = q01 at *; generalize x1 * y0 = q10 at *
    generalize x0 * y2 = q02 at *; generalize x1 * y1 = q11 at *; generalize x2 * y0 = q20 at *
    generalize x0 * y3 = q03 at *; generalize x1 * y2 = q12 at *; generalize x2 * y1 = q21 at *
    generalize x3 * y0 = q30 at *
    omega

/-- The arithmetic of `p3f7Word`: no carries between lanes. -/
theorem p3f7_arith {w0 w1 w2 w3 w4 wA z0 z1 : Nat} (A : Nat → Nat → Nat)
    (hA : ∀ r s, r < 4 → s < 5 → A r s < 2 ^ 23)
    (hz : ∀ k, k < 4 → lane z0 k < 2 ^ 28) (hz4 : lane z1 0 < 2 ^ 28)
    (hz0 : z0 < 2 ^ 256)
    (h0 : w0 = pack4 fun r => A r 0) (h1 : w1 = pack4 fun r => A r 1)
    (h2 : w2 = pack4 fun r => A r 2)
    (h3 : ∀ r, r < 3 → lane w3 (r + 1) = A r 3) (hw3 : w3 < 2 ^ 256)
    (h4 : ∀ r, r < 3 → lane w4 (r + 1) = A r 4) (hw4 : w4 < 2 ^ 256)
    (hA2 : lane wA 2 = A 3 4) (hA3 : lane wA 3 = A 3 3) (hwA : wA < 2 ^ 256) :
    (w0 * lane z0 0 + w1 * lane z0 1 + w2 * lane z0 2 + w3 / 2 ^ 64 * lane z0 3 +
      w4 / 2 ^ 64 * lane z1 0 +
      ((wA &&& (2 ^ 256 - 2 ^ 128)) * (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) % 2 ^ 256 &&&
        (M64 * 2 ^ 192))) % 2 ^ 256 =
    pack4 fun r => A r 0 * lane z0 0 + A r 1 * lane z0 1 + A r 2 * lane z0 2 + A r 3 * lane z0 3 +
      A r 4 * lane z1 0 := by
  have e3 : w3 / 2 ^ 64 = A 0 3 + 2 ^ 64 * A 1 3 + 2 ^ 128 * A 2 3 := by
    rw [← h3 0 (by omega), ← h3 1 (by omega), ← h3 2 (by omega)]
    unfold lane; norm_num; omega
  have e4 : w4 / 2 ^ 64 = A 0 4 + 2 ^ 64 * A 1 4 + 2 ^ 128 * A 2 4 := by
    rw [← h4 0 (by omega), ← h4 1 (by omega), ← h4 2 (by omega)]
    unfold lane; norm_num; omega
  -- the Kronecker multiplier: `ẑ3`, `ẑ4` in lanes 0, 1
  have ey1 : z1 * 2 ^ 64 % 2 ^ 256 = 2 ^ 64 * (z1 % 2 ^ 192) := by omega
  have ey2 : z0 / 2 ^ 192 = lane z0 3 := by unfold lane; omega
  have hl3 : lane z0 3 < 2 ^ 64 := by have := hz 3 (by omega); omega
  have ey : (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) =
      lane z0 3 + 2 ^ 64 * (lane z1 0 + 2 ^ 64 * (z1 / 2 ^ 64 % 2 ^ 128)) := by
    rw [ey1, ey2, ← Nat.two_pow_add_eq_or_of_lt hl3, Nat.add_comm]
    congr 2
    unfold lane; omega
  have eA : wA &&& (2 ^ 256 - 2 ^ 128) = (A 3 4 + 2 ^ 64 * A 3 3) * 2 ^ 128 := by
    rw [and_top hwA (by norm_num), ← hA2, ← hA3]
    congr 1
    unfold lane; norm_num; omega
  have hk : (wA &&& (2 ^ 256 - 2 ^ 128)) * (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) % 2 ^ 256 &&&
      (M64 * 2 ^ 192) = 2 ^ 192 * (A 3 4 * lane z1 0 + A 3 3 * lane z0 3) := by
    rw [m64_top, and_top (Nat.mod_lt _ (by norm_num)) (by norm_num), eA, ey]
    have ex : (A 3 4 + 2 ^ 64 * A 3 3) * 2 ^ 128 *
        (lane z0 3 + 2 ^ 64 * (lane z1 0 + 2 ^ 64 * (z1 / 2 ^ 64 % 2 ^ 128))) =
        2 ^ 128 * (A 3 4 * lane z0 3) + 2 ^ 192 * (A 3 4 * lane z1 0 + A 3 3 * lane z0 3) +
          2 ^ 256 * (A 3 3 * lane z1 0 + A 3 4 * (z1 / 2 ^ 64 % 2 ^ 128) +
            2 ^ 64 * (A 3 3 * (z1 / 2 ^ 64 % 2 ^ 128))) := by ring
    have b1 := mul_lt51 (hA 3 4 (by omega) (by omega)) (hz 3 (by omega))
    have b2 := mul_lt51 (hA 3 4 (by omega) (by omega)) hz4
    have b3 := mul_lt51 (hA 3 3 (by omega) (by omega)) (hz 3 (by omega))
    rw [ex]
    generalize A 3 4 * lane z0 3 = p at *
    generalize A 3 4 * lane z1 0 = c1 at *
    generalize A 3 3 * lane z0 3 = c2 at *
    generalize A 3 3 * lane z1 0 + A 3 4 * (z1 / 2 ^ 64 % 2 ^ 128) +
      2 ^ 64 * (A 3 3 * (z1 / 2 ^ 64 % 2 ^ 128)) = d
    omega
  have hlt : (pack4 fun r => A r 0 * lane z0 0 + A r 1 * lane z0 1 + A r 2 * lane z0 2 +
      A r 3 * lane z0 3 + A r 4 * lane z1 0) < 2 ^ 256 := MlDsaOpt44.Proofs.pack4_lt fun r hr => by
    have := mul_lt51 (hA r 0 hr (by omega)) (hz 0 (by omega))
    have := mul_lt51 (hA r 1 hr (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA r 2 hr (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA r 3 hr (by omega)) (hz 3 (by omega))
    have := mul_lt51 (hA r 4 hr (by omega)) hz4
    omega
  refine (congrArg (· % 2 ^ 256) ?_).trans (Nat.mod_eq_of_lt hlt)
  rw [hk, h0, h1, h2, e3, e4]
  simp only [pack4]
  ring

/-- The arithmetic of `p3f8Word`: rows 4, 5 in lanes 0, 1. -/
theorem p3f8_arith {w4 w5 wA z0 z1 : Nat} (A : Nat → Nat → Nat)
    (hA : ∀ r s, 4 ≤ r → r < 6 → s < 5 → A r s < 2 ^ 23)
    (hz : ∀ k, k < 4 → lane z0 k < 2 ^ 28) (hz4 : lane z1 0 < 2 ^ 28) (hz0 : z0 < 2 ^ 256)
    (h4 : ∀ k, k < 4 → lane w4 k = A 4 (3 - k)) (hw4 : w4 < 2 ^ 256)
    (h5 : ∀ k, k < 4 → lane w5 k = A 5 (3 - k)) (hw5 : w5 < 2 ^ 256)
    (hA0 : lane wA 0 = A 4 4) (hA1 : lane wA 1 = A 5 4) :
    (w4 * z0 % 2 ^ 256 / 2 ^ 192 + (w5 * z0 % 2 ^ 256 &&& (M64 * 2 ^ 192)) / 2 ^ 128 +
      (wA &&& (2 ^ 128 - 1)) * lane z1 0) % 2 ^ 256 =
    (A 4 0 * lane z0 0 + A 4 1 * lane z0 1 + A 4 2 * lane z0 2 + A 4 3 * lane z0 3 +
      A 4 4 * lane z1 0) + 2 ^ 64 *
    (A 5 0 * lane z0 0 + A 5 1 * lane z0 1 + A 5 2 * lane z0 2 + A 5 3 * lane z0 3 +
      A 5 4 * lane z1 0) := by
  have hl : ∀ r, 4 ≤ r → r < 6 → ∀ w : Nat, (∀ k, k < 4 → lane w k = A r (3 - k)) →
      ∀ k, k < 4 → lane w k < 2 ^ 23 := fun r hr4 hr6 w hw k hk => by
    rw [hw k hk]; exact hA r (3 - k) hr4 hr6 (by omega)
  obtain ⟨L4, hL4, e4⟩ := mul_lane3 hw4 hz0 (hl 4 le_rfl (by omega) w4 h4) hz
  obtain ⟨L5, hL5, e5⟩ := mul_lane3 hw5 hz0 (hl 5 (by omega) (by omega) w5 h5) hz
  rw [h4 0 (by omega), h4 1 (by omega), h4 2 (by omega), h4 3 (by omega)] at e4
  rw [h5 0 (by omega), h5 1 (by omega), h5 2 (by omega), h5 3 (by omega)] at e5
  simp only [Nat.reduceSub] at e4 e5
  have c4 : A 4 3 * lane z0 3 + A 4 2 * lane z0 2 + A 4 1 * lane z0 1 + A 4 0 * lane z0 0 < 2 ^ 53 := by
    have := mul_lt51 (hA 4 3 (by omega) (by omega) (by omega)) (hz 3 (by omega))
    have := mul_lt51 (hA 4 2 (by omega) (by omega) (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA 4 1 (by omega) (by omega) (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA 4 0 (by omega) (by omega) (by omega)) (hz 0 (by omega))
    omega
  have c5 : A 5 3 * lane z0 3 + A 5 2 * lane z0 2 + A 5 1 * lane z0 1 + A 5 0 * lane z0 0 < 2 ^ 53 := by
    have := mul_lt51 (hA 5 3 (by omega) (by omega) (by omega)) (hz 3 (by omega))
    have := mul_lt51 (hA 5 2 (by omega) (by omega) (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA 5 1 (by omega) (by omega) (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA 5 0 (by omega) (by omega) (by omega)) (hz 0 (by omega))
    omega
  have d44 := mul_lt51 (hA 4 4 (by omega) (by omega) (by omega)) hz4
  have d54 := mul_lt51 (hA 5 4 (by omega) (by omega) (by omega)) hz4
  have q4 : w4 * z0 % 2 ^ 256 / 2 ^ 192 =
      A 4 3 * lane z0 3 + A 4 2 * lane z0 2 + A 4 1 * lane z0 1 + A 4 0 * lane z0 0 := by
    rw [e4]; omega
  have q5 : (w5 * z0 % 2 ^ 256 &&& (M64 * 2 ^ 192)) / 2 ^ 128 = 2 ^ 64 *
      (A 5 3 * lane z0 3 + A 5 2 * lane z0 2 + A 5 1 * lane z0 1 + A 5 0 * lane z0 0) := by
    rw [m64_top, and_top (Nat.mod_lt _ (by norm_num)) (by norm_num), e5]; omega
  have qA : wA &&& (2 ^ 128 - 1) = A 4 4 + 2 ^ 64 * A 5 4 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, ← hA0, ← hA1]; unfold lane; omega
  rw [q4, q5, qA]
  have e : A 4 3 * lane z0 3 + A 4 2 * lane z0 2 + A 4 1 * lane z0 1 + A 4 0 * lane z0 0 +
      2 ^ 64 * (A 5 3 * lane z0 3 + A 5 2 * lane z0 2 + A 5 1 * lane z0 1 + A 5 0 * lane z0 0) +
      (A 4 4 + 2 ^ 64 * A 5 4) * lane z1 0 =
      (A 4 0 * lane z0 0 + A 4 1 * lane z0 1 + A 4 2 * lane z0 2 + A 4 3 * lane z0 3 +
        A 4 4 * lane z1 0) + 2 ^ 64 *
      (A 5 0 * lane z0 0 + A 5 1 * lane z0 1 + A 5 2 * lane z0 2 + A 5 3 * lane z0 3 +
        A 5 4 * lane z1 0) := by ring
  rw [e]
  apply Nat.mod_eq_of_lt
  have := mul_lt51 (hA 4 0 (by omega) (by omega) (by omega)) (hz 0 (by omega))
  have := mul_lt51 (hA 4 1 (by omega) (by omega) (by omega)) (hz 1 (by omega))
  have := mul_lt51 (hA 4 2 (by omega) (by omega) (by omega)) (hz 2 (by omega))
  have := mul_lt51 (hA 4 3 (by omega) (by omega) (by omega)) (hz 3 (by omega))
  have := mul_lt51 (hA 5 0 (by omega) (by omega) (by omega)) (hz 0 (by omega))
  have := mul_lt51 (hA 5 1 (by omega) (by omega) (by omega)) (hz 1 (by omega))
  have := mul_lt51 (hA 5 2 (by omega) (by omega) (by omega)) (hz 2 (by omega))
  have := mul_lt51 (hA 5 3 (by omega) (by omega) (by omega)) (hz 3 (by omega))
  omega

/-! ## The stored lanes are `Â ẑ` -/

private theorem zhLane_lo (m : ByteArray) {k : Nat} (hk : k < 4) (t : Nat) :
    zhLane m k t = lane (word m (ZH + 32 * t)) k := by
  unfold zhLane zhAddr; rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.mul_zero, Nat.add_zero]

private theorem zhLane_four (m : ByteArray) (t : Nat) :
    zhLane m 4 t = lane (word m (ZH + 8192 + 32 * t)) 0 := rfl

private theorem lane_two {X Y : Nat} (hX : X < 2 ^ 64) (hY : Y < 2 ^ 64) :
    lane (X + 2 ^ 64 * Y) 0 = X ∧ lane (X + 2 ^ 64 * Y) 1 = Y ∧ lane (X + 2 ^ 64 * Y) 2 = 0 ∧
      lane (X + 2 ^ 64 * Y) 3 = 0 := by
  unfold lane; refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> omega

private theorem accSum5_lt {cd m : ByteArray} (hok : okA cd = true) (hz : ZHatAt m cd) {r t : Nat}
    (hr : r < 6) (ht : t < 256) : accSum cd m r t 5 < 2 ^ 54 := by
  have h := fun s (hs : s < 5) => mul_lt51 (s3_aD_lt (s3_okA_get hok hr hs) ht) (hz s hs t ht).1
  have := h 0 (by omega); have := h 1 (by omega); have := h 2 (by omega)
  have := h 3 (by omega); have := h 4 (by omega)
  simp only [accSum, Nat.zero_add]
  omega

private theorem sum_range5 (f : Nat → Int) :
    ((List.range 5).map f).sum = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  ring

/-- The row sum is `azRow` modulo `q`. -/
private theorem accSum5_mod {cd m : ByteArray} (hok : okA cd = true) (hz : ZHatAt m cd) {r t : Nat}
    (hr : r < 6) (ht : t < 256) :
    ((accSum cd m r t 5 : Int) - (azRow cd r)[t]!) % (Fips204.q : Int) = 0 := by
  have hnn : ∀ s, s < 5 → (((aD cd r s)[t]!).toNat : Int) = (aD cd r s)[t]! := fun s hs =>
    s3_aD_cast (s3_okA_get hok hr hs) ht
  have hm : ∀ s, s < 5 → (zhLane m s t : Int) % (Fips204.q : Int) =
      (zHat cd s)[t]! % (Fips204.q : Int) := fun s hs =>
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (hz s hs t ht).2
  have hrow : (azRow cd r)[t]! = ((List.range 5).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum %
      (Fips204.q : Int) := by
    unfold azRow; exact MlDsaOpt44.Proofs.getElem!_map_range 256 t _ ht
  rw [hrow, sum_range5]
  simp only [accSum, Nat.zero_add]
  push_cast
  rw [hnn 0 (by omega), hnn 1 (by omega), hnn 2 (by omega), hnn 3 (by omega), hnn 4 (by omega)]
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  exact Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add
    (Int.ModEq.mul_left _ (hm 0 (by omega))) (Int.ModEq.mul_left _ (hm 1 (by omega))))
    (Int.ModEq.mul_left _ (hm 2 (by omega)))) (Int.ModEq.mul_left _ (hm 3 (by omega))))
    (Int.ModEq.mul_left _ (hm 4 (by omega)))

/-- The words `pass3f7` and `pass3f8` store are `Â ẑ` (bounded representatives mod `q`)
when `A` exists. -/
theorem accAt_glam {cd m7 m8 m : ByteArray}
    (hz7 : ZHatAt m7 cd) (b0 : BufCol m7 CW cd 0) (b1 : BufCol m7 HP cd 1)
    (b2 : BufCol m7 (HP + 8192) cd 2)
    (c3 : Col3Hi m7 ACC cd 3) (c4 : Col3Hi m7 (SB + 8192) cd 4)
    (hP : okA cd = true → ∀ t, t < 256 →
      lane (word m7 (ABUF + 32 * t)) 2 = ((aD cd 3 4)[t]!).toNat ∧
      lane (word m7 (ABUF + 32 * t)) 3 = ((aD cd 3 3)[t]!).toNat)
    (hz8 : ZHatAt m8 cd) (r4 : RowBuf m8 (ACC + 8192) cd 4) (r5 : RowBuf m8 SB cd 5)
    (hKX : okA cd = true → ∀ t, t < 256 →
      lane (word m8 (ABUF + 32 * t)) 0 = ((aD cd 4 4)[t]!).toNat ∧
      lane (word m8 (ABUF + 32 * t)) 1 = ((aD cd 5 4)[t]!).toNat)
    (h7 : ∀ t, t < 256 → word m (ACC + 32 * t) = p3f7Word m7 t)
    (h8 : ∀ t, t < 256 → word m (ACC + 8192 + 32 * t) = p3f8Word m8 t) :
    AccAt m cd := by
  intro hok
  have hA : ∀ r s, r < 6 → s < 5 → (aOf cd r s).isSome = true := fun r s hr hs =>
    s3_okA_get hok hr hs
  have hlt : ∀ r s, r < 6 → s < 5 → ∀ t, t < 256 → ((aD cd r s)[t]!).toNat < 2 ^ 23 :=
    fun r s hr hs t ht => s3_aD_lt (hA r s hr hs) ht
  have oc0 : ∀ s, s < 5 → okCol0 cd s = true := fun s hs => by
    simp only [okCol0, Bool.and_eq_true]
    exact ⟨⟨⟨hA 0 s (by omega) hs, hA 1 s (by omega) hs⟩, hA 2 s (by omega) hs⟩, hA 3 s (by omega) hs⟩
  have orow : ∀ r, r < 6 → okRow cd r = true := fun r hr => by
    unfold okRow; rw [List.all_eq_true]; intro k hk
    exact hA r (3 - k) hr (by have := List.mem_range.mp hk; omega)
  have oc3 : ∀ s, s < 5 → okCol3 cd s = true := fun s hs => by
    unfold okCol3; rw [List.all_eq_true]; intro r hr
    exact hA r s (by have := List.mem_range.mp hr; omega) hs
  have hzb : ∀ {mm : ByteArray}, ZHatAt mm cd → ∀ t, t < 256 →
      (∀ k, k < 4 → lane (word mm (ZH + 32 * t)) k < 2 ^ 28) ∧
        lane (word mm (ZH + 8192 + 32 * t)) 0 < 2 ^ 28 := fun hz t ht =>
    ⟨fun k hk => by rw [← zhLane_lo _ hk]; exact (hz k (by omega) t ht).1,
      by rw [← zhLane_four]; exact (hz 4 (by omega) t ht).1⟩
  -- the stored words
  have w7 : ∀ t, t < 256 → word m (ACC + 32 * t) = pack4 fun r => accSum cd m7 r t 5 := by
    intro t ht
    obtain ⟨hz, hz4⟩ := hzb hz7 t ht
    obtain ⟨e2, e3⟩ := hP hok t ht
    rw [h7 t ht]
    refine (p3f7_arith (fun r s => ((aD cd r s)[t]!).toNat)
      (fun r s hr hs => hlt r s (by omega) hs t ht) hz hz4 (word_lt _ _)
      (b0 (oc0 0 (by omega)) t ht) (b1 (oc0 1 (by omega)) t ht) (b2 (oc0 2 (by omega)) t ht)
      (c3 (oc3 3 (by omega)) t ht) (word_lt _ _) (c4 (oc3 4 (by omega)) t ht) (word_lt _ _)
      e2 e3 (word_lt _ _)).trans ?_
    simp only [accSum, Nat.zero_add, zhLane_lo m7 (by omega : 0 < 4), zhLane_lo m7 (by omega : 1 < 4),
      zhLane_lo m7 (by omega : 2 < 4), zhLane_lo m7 (by omega : 3 < 4), zhLane_four]
  have w8 : ∀ t, t < 256 →
      word m (ACC + 8192 + 32 * t) = accSum cd m8 4 t 5 + 2 ^ 64 * accSum cd m8 5 t 5 := by
    intro t ht
    obtain ⟨hz, hz4⟩ := hzb hz8 t ht
    obtain ⟨e0, e1⟩ := hKX hok t ht
    rw [h8 t ht]
    refine (p3f8_arith (fun r s => ((aD cd r s)[t]!).toNat)
      (fun r s _ hr hs => hlt r s hr hs t ht) hz hz4 (word_lt _ _)
      (r4 (orow 4 (by omega)) t ht) (word_lt _ _) (r5 (orow 5 (by omega)) t ht) (word_lt _ _)
      e0 e1).trans ?_
    simp only [accSum, Nat.zero_add, zhLane_lo m8 (by omega : 0 < 4), zhLane_lo m8 (by omega : 1 < 4),
      zhLane_lo m8 (by omega : 2 < 4), zhLane_lo m8 (by omega : 3 < 4), zhLane_four]
  have l7 : ∀ t, t < 256 → ∀ k, k < 4 → lane (word m (ACC + 32 * t)) k = accSum cd m7 k t 5 :=
    fun t ht k hk => by
      rw [w7 t ht, MlDsaOpt44.Proofs.lane_pack4 (fun r hr => by
        have := accSum5_lt hok hz7 (r := r) (by omega) ht; omega) hk]
  have l8 : ∀ t, t < 256 → lane (word m (ACC + 8192 + 32 * t)) 0 = accSum cd m8 4 t 5 ∧
      lane (word m (ACC + 8192 + 32 * t)) 1 = accSum cd m8 5 t 5 ∧
      lane (word m (ACC + 8192 + 32 * t)) 2 = 0 ∧ lane (word m (ACC + 8192 + 32 * t)) 3 = 0 :=
    fun t ht => by
      rw [w8 t ht]
      have := accSum5_lt hok hz8 (r := 4) (by omega) ht
      have := accSum5_lt hok hz8 (r := 5) (by omega) ht
      exact lane_two (by omega) (by omega)
  refine ⟨fun g hg k hk t ht => ?_, fun r hr t ht => ?_⟩
  · interval_cases g
    · rw [show ACC + 0x2000 * 0 + 32 * t = ACC + 32 * t by omega, l7 t ht k hk]
      have := accSum5_lt hok hz7 (r := k) (by omega) ht; omega
    · rw [show ACC + 0x2000 * 1 + 32 * t = ACC + 8192 + 32 * t by omega]
      obtain ⟨e0, e1, e2, e3⟩ := l8 t ht
      have := accSum5_lt hok hz8 (r := 4) (by omega) ht
      have := accSum5_lt hok hz8 (r := 5) (by omega) ht
      interval_cases k
      · rw [e0]; omega
      · rw [e1]; omega
      · rw [e2]; norm_num
      · rw [e3]; norm_num
  · by_cases h4 : r < 4
    · rw [show accAddr r t = ACC + 32 * t by unfold accAddr; rw [Nat.div_eq_of_lt h4]; omega,
        Nat.mod_eq_of_lt h4, l7 t ht r h4]
      exact accSum5_mod hok hz7 hr ht
    · rw [show accAddr r t = ACC + 8192 + 32 * t by unfold accAddr; rw [show r / 4 = 1 by omega]]
      obtain ⟨e0, e1, -, -⟩ := l8 t ht
      rcases (by omega : r = 4 ∨ r = 5) with rfl | rfl
      · rw [show 4 % 4 = 0 from rfl, e0]; exact accSum5_mod hok hz8 hr ht
      · rw [show 5 % 4 = 1 from rfl, e1]; exact accSum5_mod hok hz8 hr ht

end Exp

end MlDsaOptGlam65.Proofs
