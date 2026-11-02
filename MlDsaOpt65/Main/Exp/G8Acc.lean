import MlDsaOpt65.Main.Exp.Bound
import MlDsaOpt65.Fn.Group
set_option warningAsError true
/-!
# `pass3f8`'s word as row group 1 of `Â ẑ` (ML-DSA-65, v4)

`p3f8Word` (`Fn/Group.lean`) adds the products of the ten row-group-1
instances (groups 5–7 in `CW`, `HP`, `HP + 0x2000`, group 8 in lane 0 of
`ABUF`) with `ẑ`, each moved to its row's lane by a mask and a 64-bit shift.
With the buffers' lanes (`MixBuf`) the word is `pack4 (accSum 4, accSum 5, 0, 0)`
(`p3f8Word_eq`), so the table after `pass3f8` is `AccCols1 … 5` (`accCols1_p3f8`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Exp

/-! ## Masks on a word's lanes -/

theorem land_window (x a n : Nat) : x &&& (2 ^ (a + n) - 2 ^ a) = 2 ^ a * (x / 2 ^ a % 2 ^ n) := by
  have e : 2 ^ (a + n) - 2 ^ a = 2 ^ a * (2 ^ n - 1) := by
    rw [Nat.pow_add, Nat.mul_sub, Nat.mul_one]
  rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : a ≤ i
  · rw [show i - a + a = i by omega]; simp [hi]; exact Bool.and_comm _ _
  · simp [show ¬ i ≥ a by omega]

theorem land_l01 (w : Nat) : w &&& (2 ^ 128 - 1) = lane w 0 + 2 ^ 64 * lane w 1 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]; unfold lane; omega

theorem land_l0 (w : Nat) : w &&& (2 ^ 64 - 1) = lane w 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]; unfold lane; omega

theorem land_l2 (w : Nat) : w &&& (2 ^ 192 - 2 ^ 128) = 2 ^ 128 * lane w 2 := by
  rw [show (192 : Nat) = 128 + 64 by rfl, land_window]; unfold lane; omega

theorem land_l12 (w : Nat) : w &&& (2 ^ 192 - 2 ^ 64) = 2 ^ 64 * lane w 1 + 2 ^ 128 * lane w 2 := by
  rw [show (192 : Nat) = 64 + 128 by rfl, land_window]; unfold lane; omega

/-! ## The word -/

theorem aD_lt {cd : ByteArray} (hok : okA cd = true) {r s : Nat} (hr : r < 6) (hs : s < 5) {t : Nat}
    (ht : t < 256) : ((aD cd r s)[t]!).toNat < 2 ^ 23 :=
  s3_aD_lt (s3_okA_get hok hr hs) ht

private theorem zl_eq' (m : ByteArray) (j t : Nat) : zl m j t = zhLane m j t := rfl

set_option maxHeartbeats 400000 in
theorem p3f8_arith {A40 A41 A42 A43 A44 A50 A51 A52 A53 A54 Z0 Z1 Z2 Z3 Z4 : Nat}
    (a40 : A40 < 2 ^ 23) (a43 : A43 < 2 ^ 23)
    (a50 : A50 < 2 ^ 23) (a51 : A51 < 2 ^ 23) 
    (a53 : A53 < 2 ^ 23) (a54 : A54 < 2 ^ 23)
    (b0 : A40 * Z0 + A41 * Z1 + A42 * Z2 + A43 * Z3 + A44 * Z4 < 2 ^ 64)
    (b1 : A50 * Z0 + A51 * Z1 + A52 * Z2 + A53 * Z3 + A54 * Z4 < 2 ^ 64) :
    ((A40 + 2 ^ 64 * A50) * 2 ^ (64 * 0) % 2 ^ 256 * Z0 + 2 ^ 128 * A41 / 2 ^ (64 * 2) * Z1 +
      A51 * 2 ^ (64 * 1) % 2 ^ 256 * Z1 + (2 ^ 64 * A42 + 2 ^ 128 * A52) / 2 ^ (64 * 1) * Z2 +
      (A43 + 2 ^ 64 * A53) * 2 ^ (64 * 0) % 2 ^ 256 * Z3 + 2 ^ 128 * A44 / 2 ^ (64 * 2) * Z4 +
      A54 * 2 ^ (64 * 1) % 2 ^ 256 * Z4) % 2 ^ 256 =
    (A40 * Z0 + A41 * Z1 + A42 * Z2 + A43 * Z3 + A44 * Z4) +
      2 ^ 64 * (A50 * Z0 + A51 * Z1 + A52 * Z2 + A53 * Z3 + A54 * Z4) := by
  have q0 : (A40 + 2 ^ 64 * A50) * 2 ^ (64 * 0) % 2 ^ 256 = A40 + 2 ^ 64 * A50 := by
    rw [show (2 : Nat) ^ (64 * 0) = 1 from rfl, Nat.mul_one]; exact Nat.mod_eq_of_lt (by omega)
  have q1 : 2 ^ 128 * A41 / 2 ^ (64 * 2) = A41 := Nat.mul_div_cancel_left _ (by norm_num)
  have q2 : A51 * 2 ^ (64 * 1) % 2 ^ 256 = 2 ^ 64 * A51 := by
    rw [show (2 : Nat) ^ (64 * 1) = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have q3 : (2 ^ 64 * A42 + 2 ^ 128 * A52) / 2 ^ (64 * 1) = A42 + 2 ^ 64 * A52 := by
    rw [show (2 : Nat) ^ (64 * 1) = 2 ^ 64 from rfl]; omega
  have q4 : (A43 + 2 ^ 64 * A53) * 2 ^ (64 * 0) % 2 ^ 256 = A43 + 2 ^ 64 * A53 := by
    rw [show (2 : Nat) ^ (64 * 0) = 1 from rfl, Nat.mul_one]; exact Nat.mod_eq_of_lt (by omega)
  have q5 : 2 ^ 128 * A44 / 2 ^ (64 * 2) = A44 := Nat.mul_div_cancel_left _ (by norm_num)
  have q6 : A54 * 2 ^ (64 * 1) % 2 ^ 256 = 2 ^ 64 * A54 := by
    rw [show (2 : Nat) ^ (64 * 1) = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  rw [q0, q1, q2, q3, q4, q5, q6]
  have e : (A40 + 2 ^ 64 * A50) * Z0 + A41 * Z1 + 2 ^ 64 * A51 * Z1 + (A42 + 2 ^ 64 * A52) * Z2 +
      (A43 + 2 ^ 64 * A53) * Z3 + A44 * Z4 + 2 ^ 64 * A54 * Z4 =
      (A40 * Z0 + A41 * Z1 + A42 * Z2 + A43 * Z3 + A44 * Z4) +
        2 ^ 64 * (A50 * Z0 + A51 * Z1 + A52 * Z2 + A53 * Z3 + A54 * Z4) := by ring
  rw [e]
  generalize A40 * Z0 + A41 * Z1 + A42 * Z2 + A43 * Z3 + A44 * Z4 = X at b0 ⊢
  generalize A50 * Z0 + A51 * Z1 + A52 * Z2 + A53 * Z3 + A54 * Z4 = Y at b1 ⊢
  exact Nat.mod_eq_of_lt (by omega)

theorem pack4_two (X Y : Nat) :
    (pack4 fun j => if j = 0 then X else if j = 1 then Y else 0) = X + 2 ^ 64 * Y := by
  unfold pack4; simp

theorem p3f8Word_eq {cd m : ByteArray} (hok : okA cd = true) (hz : ZHatAt m cd)
    (b5 : MixBuf m CW cd 0) (b6 : MixBuf m HP cd 3) (b7 : MixBuf m (HP + 8192) cd 6)
    {t : Nat} (ht : t < 256) (ha : lane (word m (ABUF + 32 * t)) 0 = ((aD cd 5 4)[t]!).toNat) :
    p3f8Word m t = pack4 fun j => if j = 0 then accSum cd m 4 t 5 else if j = 1 then accSum cd m 5 t 5
      else 0 := by
  have c0 := b5 hok t ht 0 (by norm_num); have c1 := b5 hok t ht 1 (by norm_num)
  have c2 := b5 hok t ht 2 (by norm_num)
  have h0 := b6 hok t ht 0 (by norm_num); have h1 := b6 hok t ht 1 (by norm_num)
  have h2 := b6 hok t ht 2 (by norm_num)
  have g0 := b7 hok t ht 0 (by norm_num); have g1 := b7 hok t ht 1 (by norm_num)
  have g2 := b7 hok t ht 2 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv] at c0 c1 c2 h0 h1 h2 g0 g1 g2
  have z0 := (hz 0 (by norm_num) t ht).1; have z1 := (hz 1 (by norm_num) t ht).1
  have z2 := (hz 2 (by norm_num) t ht).1; have z3 := (hz 3 (by norm_num) t ht).1
  have z4 := (hz 4 (by norm_num) t ht).1
  have lt := fun r s (hr : r < 6) (hs : s < 5) => aD_lt hok hr hs ht
  have a40 := lt 4 0 (by omega) (by omega); have a41 := lt 4 1 (by omega) (by omega)
  have a42 := lt 4 2 (by omega) (by omega); have a43 := lt 4 3 (by omega) (by omega)
  have a44 := lt 4 4 (by omega) (by omega); have a50 := lt 5 0 (by omega) (by omega)
  have a51 := lt 5 1 (by omega) (by omega); have a52 := lt 5 2 (by omega) (by omega)
  have a53 := lt 5 3 (by omega) (by omega); have a54 := lt 5 4 (by omega) (by omega)
  have L0 : accSum cd m 4 t 5 = ((aD cd 4 0)[t]!).toNat * zhLane m 0 t +
      ((aD cd 4 1)[t]!).toNat * zhLane m 1 t + ((aD cd 4 2)[t]!).toNat * zhLane m 2 t +
      ((aD cd 4 3)[t]!).toNat * zhLane m 3 t + ((aD cd 4 4)[t]!).toNat * zhLane m 4 t := by
    simp only [accSum, Nat.zero_add]
  have L1 : accSum cd m 5 t 5 = ((aD cd 5 0)[t]!).toNat * zhLane m 0 t +
      ((aD cd 5 1)[t]!).toNat * zhLane m 1 t + ((aD cd 5 2)[t]!).toNat * zhLane m 2 t +
      ((aD cd 5 3)[t]!).toNat * zhLane m 3 t + ((aD cd 5 4)[t]!).toNat * zhLane m 4 t := by
    simp only [accSum, Nat.zero_add]
  have hb : ∀ r, r < 6 → accSum cd m r t 5 < 2 ^ 64 := fun r hr => by
    have := s3_accSum_le ht (fun k hk => (hz k hk t ht).1) 5 le_rfl
      (fun s hs => s3_okA_get hok hr hs)
    omega
  have b0 := hb 4 (by omega); have b1 := hb 5 (by omega)
  rw [L0] at b0; rw [L1] at b1
  unfold p3f8Word bzl bzr
  simp only [zl_eq']
  rw [land_l01, land_l2, land_l0, land_l12, land_l01, land_l2, land_l0, c0, c1, c2, h0, h1, h2, g0, g1,
    g2, ha, p3f8_arith a40 a43 a50 a51 a53 a54 b0 b1, ← L0, ← L1]
  exact (pack4_two _ _).symm

/-- The table after `pass3f8` (word `t` is `p3f8Word m t`, `ẑ` unchanged). -/
theorem accCols1_p3f8 {cd m m' : ByteArray} (hok : okA cd = true) (hz : ZHatAt m cd)
    (b5 : MixBuf m CW cd 0) (b6 : MixBuf m HP cd 3) (b7 : MixBuf m (HP + 8192) cd 6)
    (ha : ∀ t, t < 256 → lane (word m (ABUF + 32 * t)) 0 = ((aD cd 5 4)[t]!).toNat)
    (hw : ∀ t, t < 256 → word m' (ACC + 8192 + 32 * t) = p3f8Word m t)
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : AccCols1 m' cd 5 := by
  intro _ t ht
  have hs : ∀ r, accSum cd m' r t 5 = accSum cd m r t 5 := fun r =>
    s3_accSum_congr 5 (fun k hk => hzh k hk t ht)
  have hlt : ∀ r, r < 6 → accSum cd m r t 5 < 2 ^ 64 := fun r hr => by
    have := s3_accSum_le ht (fun k hk => (hz k hk t ht).1) 5 le_rfl
      (fun s hs => s3_okA_get hok hr hs)
    omega
  have hv : ∀ j, j < 4 → (if j = 0 then accSum cd m 4 t 5 else if j = 1 then accSum cd m 5 t 5 else 0)
      < 2 ^ 64 := fun j _ => by
    split
    · exact hlt 4 (by omega)
    · split
      · exact hlt 5 (by omega)
      · norm_num
  rw [show ACC + 0x2000 + 32 * t = ACC + 8192 + 32 * t from rfl, hw t ht,
    p3f8Word_eq hok hz b5 b6 b7 ht (ha t ht)]
  refine ⟨fun j hj => ?_, fun j hj2 hj4 => ?_⟩
  · rw [MlDsaOpt44.Proofs.lane_pack4 hv (by omega), hs]
    interval_cases j <;> simp
  · rw [MlDsaOpt44.Proofs.lane_pack4 hv hj4, if_neg (by omega), if_neg (by omega)]
    exact Nat.zero_le _

end Exp

end MlDsaOpt65.Proofs
