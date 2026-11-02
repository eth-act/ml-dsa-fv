import MlDsaOpt44.Fn.Hint.UseHint
/-!
# v4 NTT and UseHint arithmetic (`scripts/opt_selftest.py`, `test_constants`)

The numeric facts the v4 `ntt` / `intt` code relies on, which the generator's
self-test asserts by sampling or by an interval iteration:

* forward NTT with the `8q` bias (R4-3): the lanes stay in
  `[lo4 L, hi4 L] ⊆ [U4, 2^28)` through the 8 layers, so `b' = a − u` never
  borrows (`lo4_ge`, `hi4_lt`); Shoup's product `u = bζ − q ⌊bζ'/2^32⌋` is
  `≡ bζ`, non-negative and `< q + 2^19` for `b < 2^28` (`shoup_bound`);
* inverse NTT (R4-6): `C ≥ a` and the Montgomery input `< 2^64` are the v3
  bounds `Bi L ≤ 9662627968 < C` (`NttW.Bi_le`); outputs `< 2^26 + q`, so
  `W < 2^30` and UseHint's `x = W + SP < 2^31` (`uh_x_lt`);
* UseHint (R4-4, R4-6): `⌊x/q⌋` by multiply-shift (`UH.div_q`), the exact
  `⌊y/γ2⌋` for `y < 2^31 + γ2` (`divg2_exact`), `v mod 44` for `v < 2^15`
  (`mod44_exact`), and the rounding term `γ2 − 1` folded into `SP`:
  `D' = ⌊(x − ⌊x/q⌋)/γ2⌋ ≡ ⌊((x − (γ2 − 1)) mod q + γ2 − 1)/γ2⌋ (mod 2m)`
  for every `x` (`fold_mod88`), so the stored lane is FIPS 204 `UseHint`
  (`uh4L_spec`).
-/

namespace MlDsaOpt44.Proofs.NttV4

open MlDsa44
open MlDsaOpt44.Proofs

/-! ## Forward NTT: the bias interval -/

/-- Bound of one butterfly's product `u` (Montgomery `< 2^19 + q` for inputs
`< 2^28`, Shoup `< q + q/16 + 1`). -/
def U4 : Nat := 8380417 + 2 ^ 19

/-- Lane bounds after `L` forward layers: `[zLo − L U4, zHi + L U4]`. -/
def lo4 (L : Nat) : Nat := 75292682 - L * 8904705
def hi4 (L : Nat) : Nat := 75554825 + L * 8904705

theorem zLo_eq : zLo = lo4 0 := by unfold zLo lo4 Fips204.q; norm_num
theorem zHi_eq : zHi = hi4 0 := by unfold zHi hi4 Fips204.q; norm_num

theorem lo4_ge {L : Nat} (hL : L < 8) : U4 ≤ lo4 L := by unfold U4 lo4; omega
theorem lo4_succ {L : Nat} (hL : L < 8) : lo4 (L + 1) + U4 = lo4 L := by unfold U4 lo4; omega
theorem hi4_succ (L : Nat) : hi4 (L + 1) = hi4 L + U4 := by unfold U4 hi4; ring
theorem hi4_lt {L : Nat} (hL : L ≤ 8) : hi4 L < 2 ^ 28 := by unfold hi4; omega

/-- Shoup multiplication by `zt` with `zs = ⌊zt 2^32 / q⌋`: `u = zt B − q ⌊zs B / 2^32⌋`
does not borrow and is `< q + 2^19` for `B < 2^28`. -/
theorem shoup_bound {zs zt B : Nat} (h1 : zs * 8380417 ≤ zt * 2 ^ 32)
    (h2 : zt * 2 ^ 32 < zs * 8380417 + 8380417) (hB : B < 2 ^ 28) :
    8380417 * (zs * B / 2 ^ 32) ≤ zt * B ∧ zt * B < 8380417 * (zs * B / 2 ^ 32) + U4 := by
  set h := zs * B / 2 ^ 32 with hh
  have e1 : h * 2 ^ 32 ≤ zs * B := Nat.div_mul_le_self _ _
  have e2 : zs * B < (h + 1) * 2 ^ 32 := by
    rw [hh, Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add (by positivity)
  constructor
  · apply Nat.le_of_mul_le_mul_right (c := 2 ^ 32) _ (by positivity)
    calc 8380417 * h * 2 ^ 32 = 8380417 * (h * 2 ^ 32) := by ring
      _ ≤ 8380417 * (zs * B) := Nat.mul_le_mul_left _ e1
      _ = zs * 8380417 * B := by ring
      _ ≤ zt * 2 ^ 32 * B := Nat.mul_le_mul_right _ h1
      _ = zt * B * 2 ^ 32 := by ring
  · apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ 32)
    rcases Nat.eq_zero_or_pos B with hB0 | hB0
    · subst hB0; unfold U4; simp
    have e3 : zt * 2 ^ 32 * B < (zs * 8380417 + 8380417) * B := Nat.mul_lt_mul_of_pos_right h2 hB0
    have e4 : 8380417 * (zs * B) ≤ 8380417 * ((h + 1) * 2 ^ 32) := Nat.mul_le_mul_left _ e2.le
    have e5 : 8380417 * B ≤ 8380417 * 2 ^ 28 := Nat.mul_le_mul_left _ hB.le
    calc zt * B * 2 ^ 32 = zt * 2 ^ 32 * B := by ring
      _ < (zs * 8380417 + 8380417) * B := e3
      _ = 8380417 * (zs * B) + 8380417 * B := by ring
      _ ≤ 8380417 * ((h + 1) * 2 ^ 32) + 8380417 * 2 ^ 28 := Nat.add_le_add e4 e5
      _ ≤ (8380417 * h + U4) * 2 ^ 32 := by unfold U4; ring_nf; omega

/-! ## UseHint (fused into the inverse NTT's last pass) -/

/-- `⌊y / γ2⌋` by `(y · 738919105) >> 46`, exact for `y < 2^31 + γ2`. -/
theorem divg2_exact {y : Nat} (hy : y < 2 ^ 31 + 95232) : 738919105 * y / 2 ^ 46 = y / 95232 := by
  omega

/-- `v mod 44` by `v − 44 ((v · 2979) >> 17)`, exact for `v < 2^15`. -/
theorem div44_exact {v : Nat} (hv : v < 2 ^ 15) : 2979 * v / 2 ^ 17 = v / 44 := by
  have e : 2979 * v = 2 ^ 17 * (v / 44) + (4 * (v / 44) + 2979 * (v % 44)) := by omega
  have hl : 4 * (v / 44) + 2979 * (v % 44) < 2 ^ 17 := by omega
  rw [e, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hl, Nat.add_zero]

theorem mod44_exact {v : Nat} (hv : v < 2 ^ 15) : v - 44 * (2979 * v / 2 ^ 17 % 2 ^ 10) = v % 44 := by
  rw [div44_exact hv, Nat.mod_eq_of_lt (by omega : v / 44 < 2 ^ 10)]
  omega

/-- The stored lane of the fused UseHint for `x = W + SP` and hint bit `h`
(`gen_opt.py` `uh_word`): `D' = ⌊(x − ⌊x/q⌋)/γ2⌋`, `((D' >> 1) + m − h + 2 (h & D')) mod m`. -/
def uh4L (x h : Nat) : Nat :=
  ((x - x / 8380417) / 95232 / 2 + (44 - h) + 2 * (h &&& ((x - x / 8380417) / 95232))) % 44

/-- `D' ≡ D (mod 2m)`: the rounding term `γ2 − 1` is in `x`, and `y = x − ⌊x/q⌋` replaces
`x mod q` (`q − 1 = 2 γ2 m`). Holds for every `x`, also when `(x − (γ2 − 1)) mod q`
wraps. -/
theorem fold_mod88 {x r : Nat} (hr : (r : Int) = ((x : Int) - 95231) % 8380417) :
    (x - x / 8380417) / 95232 % 88 = (95231 + r) / 95232 % 88 := by
  obtain ⟨k, s, hs, rfl⟩ : ∃ k s, s < 8380417 ∧ x = 8380417 * k + s :=
    ⟨x / 8380417, x % 8380417, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod x 8380417).symm⟩
  have hk : (8380417 * k + s) / 8380417 = k := by omega
  have hy : 8380417 * k + s - k = 95232 * (88 * k) + s := by omega
  rw [hk, hy, Nat.mul_add_div (by norm_num)]
  by_cases h0 : 95231 ≤ s
  · have e : 95231 + r = s := by omega
    rw [e]
    omega
  · have e : (95231 + r) / 95232 = 88 := by omega
    rw [e, Nat.div_eq_of_lt (by omega : s < 95232)]
    omega

theorem useHint_emod' (h r : Int) : Fips204.useHint h r = Fips204.useHint h (r % (Fips204.q : Int)) := by
  unfold Fips204.useHint Fips204.decompose
  rw [Int.emod_emod]

/-- The fused UseHint lane is FIPS 204 `UseHint(h, x − (γ2 − 1))`. -/
theorem uh4L_spec {x h : Nat} (hh : h ≤ 1) :
    uh4L x h = (Fips204.useHint h ((x : Int) - 95231)).toNat := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, (r : Int) = ((x : Int) - 95231) % 8380417 :=
    ⟨(((x : Int) - 95231) % 8380417).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))⟩
  have hrq : r < 8380417 := by
    have : ((x : Int) - 95231) % 8380417 < 8380417 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  have e : Fips204.useHint h ((x : Int) - 95231) = Fips204.useHint h (r : Int) := by
    rw [useHint_emod' _ ((x : Int) - 95231), hr]; rfl
  rw [e, ← UH.useHint_lane r h hrq hh, Int.toNat_natCast, ← UH.lv_eq hrq hh, UH.lD_eq hrq]
  have hf := fold_mod88 hr
  unfold uh4L UH.lv
  rw [UH.land_bit hh, UH.land_bit hh]
  have hD : (95231 + r) / 95232 ≤ 88 := by omega
  split_ifs <;> omega

/-- UseHint's input `x = W + SP` stays below `2^31` (`W < 2^26 + q`, `SP ≤ spOff`). -/
theorem uh_x_lt {W s : Nat} (hW : W < 2 ^ 26 + 8380417) (hs : s ≤ spOff) : s + W < 2 ^ 31 := by
  unfold spOff Fips204.gamma2 Fips204.q at hs; omega

end MlDsaOpt44.Proofs.NttV4
