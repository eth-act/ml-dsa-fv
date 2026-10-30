import MlDsa44.Spec.Fips204
set_option warningAsError true
/-!
# `UseHint` (Algorithms 36/40) on `[0, q)` in unsigned arithmetic

The Yul `useHint(hb, r)` computes `r0u = r mod 2γ₂`, `neg = r0u > γ₂`,
`hi = r − r0u + neg·2γ₂` (`= r − r0` with `r0 = r mod± 2γ₂`), then
`r1 = hi / 2γ₂` (or `0` with `r0pos = 0` when `hi = q − 1`), and adjusts
`r1` by `±1 mod 44` when the hint bit is set. `yulUseHint` is that result.
-/

namespace MlDsa44.Proofs.Hint

/-- The final adjustment step of the Yul `useHint` (`p` is `r0pos`). -/
def adjust (hb p r1 : Nat) : Nat :=
  if hb = 1 then (if p = 1 then (r1 + 1) % 44 else (r1 + 43) % 44) else r1

/-- The Yul `useHint(hb, r)` in `Nat` arithmetic. -/
def yulUseHint (hb r : Nat) : Nat :=
  if r - r % 190464 + (if r % 190464 > 95232 then 190464 else 0) = 8380416 then adjust hb 0 0
  else adjust hb (if ¬ r % 190464 > 95232 ∧ r % 190464 > 0 then 1 else 0)
    ((r - r % 190464 + (if r % 190464 > 95232 then 190464 else 0)) / 190464)

theorem useHint_eq (hb r : Nat) (hhb : hb ≤ 1) (hr : r < 8380417) :
    (Fips204.useHint (hb : Int) (r : Int)).toNat = yulUseHint hb r := by
  have hR : (r : Int) % ((8380417 : Nat) : Int) = r := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Fips204.useHint, Fips204.decompose, Fips204.modPm, Fips204.q, Fips204.gamma2,
    yulUseHint, adjust, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMul, hR]
  repeat' split
  all_goals (try simp only [not_true_eq_false] at *)
  all_goals omega

theorem yulUseHint_lt (hb r : Nat) (hr : r < 8380417) : yulUseHint hb r < 44 := by
  simp only [yulUseHint, adjust]
  repeat' split
  all_goals omega

end MlDsa44.Proofs.Hint
