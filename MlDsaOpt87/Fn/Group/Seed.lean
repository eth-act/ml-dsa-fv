import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt44.Math.Sponge
import MlDsa.Bridge44
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Seeds of a pure ExpandA SIMD group (ML-DSA-87)

`group [amask, col, rb]` gives slot `k` the seed `ρ ‖ col ‖ gRow amask rb k`
(row `4 rb + k` for active slots, row `4 rb` for the others): `gL4` is the
lane-4 word its prologue builds, `ginit_group` the `ginit` word for
`keep = 0`, `amult = 15`, `cmult = 0`, `aI_aSeed` the sampled polynomial.
-/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- Row of slot `k` of `group [amask, col, rb]`. -/
def gRow (amask rb k : Nat) : Nat := 4 * rb + if amask.testBit k then k else 0

theorem gRow_lt {amask rb k : Nat} (hrb : rb < 2) (hk : k < 4) : gRow amask rb k < 8 := by
  unfold gRow; split <;> omega

/-- Lane-4 word built by `group`'s prologue (as the symbolic execution leaves it). -/
def gL4 (amask col rb : Nat) : Nat :=
  584115552256 * (1 &&& amask / 8) |||
    (274877906944 * (1 &&& amask / 4) |||
      (8589934592 * (1 &&& amask / 2) |||
        15 * (1289519644472666205716480 |||
          (rb * 1099511627776 ||| ((4 &&& col) * 64 ||| ((2 &&& col) * 8 ||| 1 &&& col))))))

theorem gL4_eq {amask col rb : Nat} (ha : amask < 16) (hcol : col < 8) (hrb : rb < 2) :
    gL4 amask col rb = il fun k => col + 256 * gRow amask rb k + 0x1F * 65536 := by
  interval_cases amask <;> interval_cases col <;> interval_cases rb <;> decide +kernel

theorem gL4_lt {amask col rb : Nat} (ha : amask < 16) (hcol : col < 8) (hrb : rb < 2) :
    gL4 amask col rb < 2 ^ 256 := by
  rw [gL4_eq ha hcol hrb]; exact il_lt _

/-- `ginit` of a pure ExpandA group: slot `k` is the seed of `A[L k][col]`. -/
theorem ginit_group {m cd : ByteArray}
    (hrho : ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 cd (8 * x)))
    (hcd : 32 ≤ cd.size) {col : Nat} (hcol : col < 256) {row : Nat → Nat}
    (hrow : ∀ k, k < 4 → row k < 256) {x : Nat} (hx : x < 25) :
    ginitWord m 0 15 0 (il fun k => col + 256 * row k + 0x1F * 65536) x =
      il fun k => cpl x (laneOf (seedState 168 (aSeed cd (row k) col)) x) := by
  have h15 : ∀ k, k < 4 → (15 : Nat).testBit k = true := fun k hk => by
    interval_cases k <;> decide
  have hda : (if x < 4 then word m (RHO1 + 32 * x) * 15 % 2 ^ 256 else 0) =
      il fun k => if x < 4 then le64 cd (8 * x) else 0 := by
    by_cases h4 : x < 4
    · rw [if_pos h4, hrho x h4, spread_mul _ (by norm_num), Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k hk => by rw [h15 k hk, if_pos rfl, if_pos h4]
    · rw [if_neg h4, il_eq_zero fun k _ => by rw [if_neg h4]]
  have hd1 : (if x = 4 then il (fun k => col + 256 * row k + 0x1F * 65536) else 0) =
      il fun k => if x = 4 then col + 256 * row k + 0x1F * 65536 else 0 := by
    by_cases h : x = 4
    · rw [if_pos h]; exact il_congr fun k _ => by rw [if_pos h]
    · rw [if_neg h, il_eq_zero fun k _ => by rw [if_neg h]]
  have hd3 : (if x = 20 then spread (2 ^ 63) * 15 % 2 ^ 256 else 0) =
      il fun k => if x = 20 then 2 ^ 63 else 0 := by
    by_cases h : x = 20
    · rw [if_pos h, spread_mul _ (by norm_num), Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k hk => by rw [h15 k hk, if_pos rfl, if_pos h]
    · rw [if_neg h, il_eq_zero fun k _ => by rw [if_neg h]]
  have hd4 : (if x ∈ complemented then 2 ^ 256 - 1 - 0 else 0) =
      il fun k => if x ∈ complemented then M64 else 0 := by
    by_cases h : x ∈ complemented
    · rw [if_pos h, ← il_zero, ones_sub_il (fun k _ => by norm_num)]
      exact il_congr fun k _ => by rw [if_pos h]; rfl
    · rw [if_neg h, il_eq_zero fun k _ => by rw [if_neg h]]
  unfold ginitWord
  simp only [Nat.mul_zero, Nat.zero_mod, ite_self, Nat.xor_zero, Nat.and_zero, Nat.or_zero]
  rw [hda, hd1, hd3, hd4, il_xor, il_xor, il_xor]
  apply il_congr; intro k hk
  have hr := hrow k hk
  rw [laneOf_aSeed hcd hr hcol hx]
  have hv : (if x < 4 then le64 cd (8 * x) else if x = 4 then col + 256 * row k + 0x1F0000
      else if x = 20 then 2 ^ 63 else 0) < 2 ^ 64 := by
    have := le64_lt cd (8 * x)
    split_ifs <;> omega
  rw [cpl_eq hv]
  by_cases h4 : x < 4
  · simp only [h4, if_true, show x ≠ 4 by omega, show x ≠ 20 by omega, if_false, Nat.xor_zero]
    split <;> simp
  · by_cases h5 : x = 4
    · subst h5; simp [complemented]
    · by_cases h6 : x = 20
      · subst h6; simp [complemented]
      · simp only [h4, h5, h6, if_false, Nat.zero_xor]

/-- The polynomial sampled from the seed of slot row `r`, column `col`. -/
theorem aI_aSeed {cd : ByteArray} (h32 : 32 ≤ cd.size) (r col : Nat) :
    MlDsaOpt44.Proofs.aI (seedState 168 (aSeed cd r col)) = aOf cd r col := by
  rw [aI_seedState (by rw [aSeed_size h32]; norm_num), aOf, MlDsa.Bridge44.rejNTTPoly_eq]
  rfl

end MlDsaOpt87.Proofs.GroupP
