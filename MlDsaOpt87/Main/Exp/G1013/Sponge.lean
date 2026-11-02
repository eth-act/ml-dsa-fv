import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Fix
import MlDsaOpt87.Fn.Group.Seed
import MlDsaOpt87.Math
import MlDsaOpt44.Math.SpongeG234
import MlDsaOpt44.Math.Sponge
set_option warningAsError true
/-!
# Sponge facts for the mixed groups 10–13 of ML-DSA-87 (restored from the v3 `S5/Sponge.lean`)

* `s5_le64_padPk_*`, `s5_le64_trOf`: the 20 blocks of the padded public key and
  `tr` as lanes of the absorbed state.
* `s5_ks4_trabs_full`, `s5_ks4_trabs_last`: what `trabs` (and the padding
  xors of group 13) do to the `tr` slot.
-/

namespace MlDsaOpt87.Proofs.G1013

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs

/-! ## The padded public key (2592 bytes, 20 blocks) -/

theorem s5_pkOf_size {cd : ByteArray} (hcd : 2592 ≤ cd.size) : (pkOf cd).size = 2592 := by
  unfold pkOf CTOFF; simp [ByteArray.size_extract]; omega

theorem s5_padPk_size {cd : ByteArray} (hcd : 2592 ≤ cd.size) : (padPk cd).size = 20 * 136 := by
  unfold padPk; rw [pad_size _ _ (by norm_num), s5_pkOf_size hcd]

/-- Lanes of the 19 full blocks of the padded public key are calldata lanes. -/
theorem s5_le64_padPk_full {cd : ByteArray} (hcd : 2592 ≤ cd.size) {a : Nat} (ha : a + 8 ≤ 2592) :
    le64 (padPk cd) a = le64 cd a := by
  apply le64_congr
  intro k hk
  unfold padPk
  rw [byteAt_pad_lt _ _ _ (by rw [s5_pkOf_size hcd]; omega)]
  unfold pkOf CTOFF
  rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]

theorem s5_byteAt_padPk_last {cd : ByteArray} (hcd : 2592 ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (padPk cd) (2584 + i) =
      if i < 8 then byteAt cd (2584 + i) else if i = 8 then 31 else if i = 135 then 128 else 0 := by
  have := byteAt_pad_last 136 (pkOf cd) (by norm_num) i hi
  rw [s5_pkOf_size hcd] at this
  norm_num at this
  unfold padPk
  rw [this]
  by_cases h : i < 8
  · rw [if_pos h, if_pos h]; unfold pkOf CTOFF
    rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- The last block of the padded public key: one calldata lane, then the padding. -/
theorem s5_le64_padPk_last {cd : ByteArray} (hcd : 2592 ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (padPk cd) (2584 + 8 * x) =
      if x = 0 then le64 cd 2584 else if x = 1 then 31 else if x = 16 then 2 ^ 63 else 0 := by
  have hb := fun i (hi : i < 136) => s5_byteAt_padPk_last hcd (i := i) hi
  by_cases h0 : x = 0
  · subst h0; rw [if_pos rfl]
    apply le64_congr
    intro k hk
    rw [Nat.mul_zero, Nat.add_zero, hb _ (by omega), if_pos (by omega)]
  rw [if_neg h0, le64_eq]
  have hk : ∀ k, k < 8 → byteAt (padPk cd) (2584 + 8 * x + k) =
      if 8 * x + k < 8 then byteAt cd (2584 + (8 * x + k)) else if 8 * x + k = 8 then 31
      else if 8 * x + k = 135 then 128 else 0 := fun k hk => by
    rw [Nat.add_assoc]; exact hb _ (by omega)
  have h0' := hk 0 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at h0'
  rw [h0', hk 1 (by omega), hk 2 (by omega), hk 3 (by omega), hk 4 (by omega), hk 5 (by omega),
    hk 6 (by omega), hk 7 (by omega)]
  by_cases hx1 : x = 1
  · subst hx1; norm_num
  · by_cases hx16 : x = 16
    · subst hx16; norm_num
    · rw [if_neg hx1, if_neg hx16]
      simp only [show ¬ 8 * x < 8 by omega, show ¬ 8 * x = 8 by omega, show ¬ 8 * x = 135 by omega,
        show ¬ 8 * x + 1 < 8 by omega, show ¬ 8 * x + 1 = 8 by omega, show ¬ 8 * x + 1 = 135 by omega,
        show ¬ 8 * x + 2 < 8 by omega, show ¬ 8 * x + 2 = 8 by omega, show ¬ 8 * x + 2 = 135 by omega,
        show ¬ 8 * x + 3 < 8 by omega, show ¬ 8 * x + 3 = 8 by omega, show ¬ 8 * x + 3 = 135 by omega,
        show ¬ 8 * x + 4 < 8 by omega, show ¬ 8 * x + 4 = 8 by omega, show ¬ 8 * x + 4 = 135 by omega,
        show ¬ 8 * x + 5 < 8 by omega, show ¬ 8 * x + 5 = 8 by omega, show ¬ 8 * x + 5 = 135 by omega,
        show ¬ 8 * x + 6 < 8 by omega, show ¬ 8 * x + 6 = 8 by omega, show ¬ 8 * x + 6 = 135 by omega,
        show ¬ 8 * x + 7 < 8 by omega, show ¬ 8 * x + 7 = 8 by omega, show ¬ 8 * x + 7 = 135 by omega,
        if_false]

/-- `tr = H(pk, 64)`: lane `x` is lane `x` of the state after the 20 absorbed
blocks of the padded public key. -/
theorem s5_le64_trOf {cd : ByteArray} (hcd : 2592 ≤ cd.size) {x : Nat} (hx : x < 8) :
    le64 (trOf cd) (8 * x) = laneOf (absorbPre 136 (padPk cd) 20) x := by
  unfold trOf MlDsa.Fips204.H Fips202.shake256
  have := le64_shake256 (pkOf cd) (n := 64) (j := 0) (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this, Function.iterate_zero_apply]
  exact congrArg (fun S => laneOf S x) (absorb_eq 136 (padPk cd) 20 (by norm_num) (s5_padPk_size hcd))

/-! ## `trabs` on the `tr` slot -/

/-- `trabs`'s post with `kp = 0`, `sh = 3`, normalised. -/
theorem s5_trabs_norm {m m' : ByteArray} {cd : ByteArray} {off lm n4 : Nat}
    (hpost : ∀ x, x < 25 → word m' (KS + 32 * x) =
      if 0 ≤ KS + 32 * x ∧ KS + 32 * x < 0 + 128 * n4 then
        word m (KS + 32 * x) ^^^ spread (trLane cd off lm n4 ((KS + 32 * x - 0) / 32)) * 2 ^ 3
      else word m (KS + 32 * x)) :
    ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * n4 then trLane cd off lm n4 x else 0) * 2 ^ 3 := by
  intro x hx
  rw [hpost x hx]
  by_cases h : x < 4 * n4
  · rw [if_pos (by unfold KS; omega), if_pos h, show (KS + 32 * x - 0) / 32 = x by unfold KS; omega]
  · rw [if_neg (by unfold KS; omega), if_neg h, spread_zero, Nat.zero_mul, Nat.xor_zero]

theorem s5_trLane_lt (cd : ByteArray) (off lm n4 u : Nat) : trLane cd off lm n4 u < 2 ^ 64 := by
  unfold trLane; exact Nat.mod_lt _ (by norm_num)

/-- A full block `j < 19` of the padded public key, absorbed into slot 3. -/
theorem s5_ks4_trabs_full {m m' : ByteArray} {cd : ByteArray} (hcd : 2592 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S) {j : Nat} (hj : j < 19)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 5 then
        trLane cd (136 * j) 0xffffffffffffffff000000000000000000000000000000000000000000000000 5 x
        else 0) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then Fips202.xorBlock 136 (padPk cd) (j * 136) (S 3) else S k := by
  refine ks4_xor_slot (by norm_num) hks _ (fun x _ => by
    split
    · exact s5_trLane_lt _ _ _ _ _
    · norm_num) hw _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), if_pos (by omega), trLane_eq cd lm_top1,
      if_neg (by omega), s5_le64_padPk_full hcd (by omega), Nat.mul_comm j]
  · rw [if_neg (by norm_num; omega)]
    by_cases h20 : x < 20
    · rw [if_pos (by omega), trLane_eq cd lm_top1, if_pos (by omega), Nat.xor_zero]
    · rw [if_neg (by omega), Nat.xor_zero]

theorem s5_spread_xor_shift (a b : Nat) :
    spread a * 2 ^ 3 ^^^ spread b * 2 ^ 3 = spread (a ^^^ b) * 2 ^ 3 := by
  rw [spread_mul_two_pow _ (by norm_num), spread_mul_two_pow _ (by norm_num),
    spread_mul_two_pow _ (by norm_num), il_xor]
  exact il_congr fun k _ => by split <;> simp

/-- The last block 19 of the padded public key (`trabs` with one group, then
the two padding xors), absorbed into slot 3. -/
theorem s5_ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : 2592 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 1 then
        trLane cd 2584 0xffffffffffffffff000000000000000000000000000000000000000000000000 1 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 1 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then Fips202.xorBlock 136 (padPk cd) (19 * 136) (S 3) else S k := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 1 then
        trLane cd 2584 0xffffffffffffffff000000000000000000000000000000000000000000000000 1 x
        else 0) ^^^ ((if x = 1 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact s5_trLane_lt _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, s5_spread_xor_shift]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 19 * 136 + 8 * x = 2584 + 8 * x by omega,
      s5_le64_padPk_last hcd h17]
    congr 1
    by_cases h0 : x = 0
    · subst h0
      rw [trLane_eq cd lm_top1]
      norm_num
    · rw [if_neg h0]
      by_cases hx1 : x = 1
      · subst hx1; rw [trLane_eq cd lm_top1]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx1, if_neg hx16, Nat.xor_zero]
          split
          · rw [trLane_eq cd lm_top1, if_pos (by omega)]
          · rfl
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

end MlDsaOpt87.Proofs.G1013
