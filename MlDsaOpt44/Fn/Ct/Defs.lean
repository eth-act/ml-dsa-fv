import MlDsaOpt44.Layout
/-! Definitions of the `c · t1` window table and sums (used by `Fn/Ct.lean`). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa44

/-- Window table entry `e < 768` of row `r`. -/
def tEntry (cd : ByteArray) (r e : Nat) : Nat :=
  if 256 ≤ e ∧ e < 512 then t1v cd r (e - 256) else 1023 - t1v cd r (e % 256)

/-- The table `tbuild` writes at `tt`. -/
def TTable (m : ByteArray) (tt : Nat) (cd : ByteArray) : Prop :=
  ∀ e, e < 768 → ∀ r, r < 4 → be16 m (tt + 6142 - 8 * e - 2 * r) = tEntry cd r e

/-- `S'_r(t)`: the window sum of row `r` at `t`. -/
def sPrime (c : Fips204.Poly) (cd : ByteArray) (r t : Nat) : Nat :=
  ((List.range 256).map fun p =>
    if c[p]! = 0 then 0 else tEntry cd r (t + 256 - p + if c[p]! = -1 then 256 else 0)).sum

/-- `n_neg(t)`: negative contributions to `(c · t1)(t)`. -/
def nNeg (c : Fips204.Poly) (t : Nat) : Nat :=
  ((List.range 256).filter fun p => (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1)).length

end MlDsaOpt44.Proofs
