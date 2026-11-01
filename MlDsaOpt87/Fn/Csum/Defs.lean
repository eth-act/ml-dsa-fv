import MlDsaOpt87.Fn.TBuild.Defs
import MlDsaOpt87.Fn.Ball.Defs
set_option warningAsError true
/-! Window sums of `c · t1` (ML-DSA-87; used by `Fn/Csum.lean`). As
`MlDsaOpt44/Fn/Ct/Defs.lean`, with the table rows read from calldata offset `off`
(`tEntry cd off`, `Fn/TBuild/Defs.lean`): `off = 32` for rows 0–3, `0x520` for rows 4–7. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa

/-- `S'_r(t)`: the window sum of table row `r` (t1 row at calldata offset `off + 320 r`) at `t`. -/
def sPrime (c : Fips204.Poly) (cd : ByteArray) (off r t : Nat) : Nat :=
  ((List.range 256).map fun p =>
    if c[p]! = 0 then 0 else tEntry cd off r (t + 256 - p + if c[p]! = -1 then 256 else 0)).sum

/-- `n_neg(t)`: negative contributions to `(c · t1)(t)`. -/
def nNeg (c : Fips204.Poly) (t : Nat) : Nat :=
  ((List.range 256).filter fun p => (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1)).length

end MlDsaOpt87.Proofs
