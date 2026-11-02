import MlDsaOpt44.Math.NttV4
import MlDsaOpt65.Fn.Hint.G5Pure
/-!
# v4 NTT and UseHint arithmetic for `γ1 = 2^19`, `γ2 = (q − 1)/32` (ML-DSA-65 and -87)

The ML-DSA-44 facts (`MlDsaOpt44/Math/NttV4.lean`) with the 65/87 parameters,
as asserted by `scripts/opt_selftest.py` (`test_constants`):

* forward NTT bias interval for inputs `z + 8q` with `γ1 = 2^19`, `raw < 2^20`
  (`zLo = 2^19 + 9q − (2^20 − 1)`): `[lo6 L, hi6 L] ⊆ [U4, 2^28)`;
* UseHint with `m = 16`: `⌊y / γ2⌋ = (y · 2149582851) >> 49` for `y < 2^31 + γ2`
  (`divg2_exact6`), the rounding term folded into `SP` (`fold_mod32`), and the
  stored lane `((D' >> 1) + 16 − h + 2 (h & D')) & 15` is FIPS 204 `UseHint`
  (`uh6L_spec`, any parameter set with `γ2 = 261888`).
-/

namespace MlDsaOpt65.Proofs.NttV4

open MlDsa
open MlDsaOpt44.Proofs.NttV4 (U4)

/-! ## Forward NTT: the bias interval (`γ1 = 2^19`) -/

/-- Lane bounds after `L` forward layers: `[zLo − L U4, zHi + L U4]`. -/
def lo6 (L : Nat) : Nat := 74899466 - L * 8904705
def hi6 (L : Nat) : Nat := 75948041 + L * 8904705

theorem lo6_ge {L : Nat} (hL : L < 8) : U4 ≤ lo6 L := by unfold U4 lo6; omega
theorem lo6_succ {L : Nat} (hL : L < 8) : lo6 (L + 1) + U4 = lo6 L := by unfold U4 lo6; omega
theorem hi6_succ (L : Nat) : hi6 (L + 1) = hi6 L + U4 := by unfold U4 hi6; ring
theorem hi6_lt {L : Nat} (hL : L ≤ 8) : hi6 L < 2 ^ 28 := by unfold hi6; omega

/-! ## UseHint, `γ2 = 261888`, `m = 16` -/

/-- `⌊y / γ2⌋` by `(y · 2149582851) >> 49`, exact for `y < 2^31 + γ2`. -/
theorem divg2_exact6 {y : Nat} (hy : y < 2 ^ 31 + 261888) : 2149582851 * y / 2 ^ 49 = y / 261888 := by
  omega

/-- The stored lane of the fused UseHint (`m = 16`). -/
def uh6L (x h : Nat) : Nat :=
  ((x - x / 8380417) / 261888 / 2 + (16 - h) + 2 * (h &&& ((x - x / 8380417) / 261888))) % 16

/-- `D' ≡ D (mod 2m)` with the rounding term `γ2 − 1` in `x` (`q − 1 = 2 γ2 · 16`). -/
theorem fold_mod32 {x r : Nat} (hr : (r : Int) = ((x : Int) - 261887) % 8380417) :
    (x - x / 8380417) / 261888 % 32 = (261887 + r) / 261888 % 32 := by
  obtain ⟨k, s, hs, rfl⟩ : ∃ k s, s < 8380417 ∧ x = 8380417 * k + s :=
    ⟨x / 8380417, x % 8380417, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod x 8380417).symm⟩
  have hk : (8380417 * k + s) / 8380417 = k := by omega
  have hy : 8380417 * k + s - k = 261888 * (32 * k) + s := by omega
  rw [hk, hy, Nat.mul_add_div (by norm_num)]
  by_cases h0 : 261887 ≤ s
  · have e : 261887 + r = s := by omega
    rw [e]
    omega
  · have e : (261887 + r) / 261888 = 32 := by omega
    rw [e, Nat.div_eq_of_lt (by omega : s < 261888)]
    omega

theorem useHint_emod6 (Q : Params) (h r : Int) :
    Fips204.useHint Q h r = Fips204.useHint Q h (r % (Fips204.q : Int)) := by
  unfold Fips204.useHint Fips204.decompose
  rw [Int.emod_emod]

/-- The fused UseHint lane is FIPS 204 `UseHint(h, x − (γ2 − 1))`. -/
theorem uh6L_spec (Q : Params) (hQ : Q.gamma2 = 261888) {x h : Nat} (hh : h ≤ 1) :
    uh6L x h = (Fips204.useHint Q h ((x : Int) - 261887)).toNat := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, (r : Int) = ((x : Int) - 261887) % 8380417 :=
    ⟨(((x : Int) - 261887) % 8380417).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))⟩
  have hrq : r < 8380417 := by
    have : ((x : Int) - 261887) % 8380417 < 8380417 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  have e : Fips204.useHint Q h ((x : Int) - 261887) = Fips204.useHint Q h (r : Int) := by
    rw [useHint_emod6 Q _ ((x : Int) - 261887), hr]; rfl
  rw [e, ← MlDsaOpt65.Proofs.G5H.useHint_lane Q hQ r h hrq hh, Int.toNat_natCast,
    ← MlDsaOpt65.Proofs.G5H.lv_eq hrq hh, MlDsaOpt65.Proofs.G5H.lD_eq hrq]
  have hf := fold_mod32 hr
  unfold uh6L MlDsaOpt65.Proofs.G5H.lv
  rw [MlDsaOpt44.Proofs.UH.land_bit hh, MlDsaOpt44.Proofs.UH.land_bit hh]
  have hD : (261887 + r) / 261888 ≤ 32 := by omega
  split_ifs <;> omega

/-- `x = W + SP < 2^31` (`W < 2^30`, `SP ≤ spOff = 128 q + γ2 − 1`). -/
theorem uh6_x_lt {W s : Nat} (hW : W < 2 ^ 30) (hs : s ≤ 128 * 8380417 + 261888 - 1) :
    s + W < 2 ^ 31 := by omega

end MlDsaOpt65.Proofs.NttV4
