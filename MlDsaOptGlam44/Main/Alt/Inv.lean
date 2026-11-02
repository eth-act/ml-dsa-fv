import MlDsaOptGlam44.Main.Inv
import MlDsaOptGlam44.Main.Frame
import MlDsaOptGlam44.Fn.Alt
set_option warningAsError true
/-!
# Boundaries of the long-message schedule (`|M| ≥ 342`, `FLAG = 0`)

| boundary | pc | stack | invariant |
|---|---|---|---|
| after `pass3f4b` (= `altj`) | 5081 | `[okZ ∧ okA]` | `InvWA` |
| hints | 5183 | `[… ∧ okH]` | `InvHA` |
| μ | 6020 | `[… ∧ okH]` | `Inv6A` |

The rows `0 … 2` of columns 2 and 3 sit in lanes `0 … 2` of `SB`, `SB + 8192`
(`Col3Lo`), the Kronecker pair `(A[3][3], A[3][2])` in lanes 2, 3 of `ABUF`.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- Lanes `0 … 2` of the 256 words at `base` are rows `0 … 2` of column `col`. -/
def Col3Lo (m : ByteArray) (base : Nat) (cd : ByteArray) (col : Nat) : Prop :=
  okCol3 cd col = true → ∀ t, t < 256 → ∀ r, r < 3 →
    lane (word m (base + 32 * t)) r = ((aD cd r col)[t]!).toNat

/-- After ExpandA on the long-message schedule (`pass3f4b`, pc 5081). -/
structure InvWA (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  acc : AccAt m cd
  /-- `|M| ≤ 613`: μ in `MU` (extracted by `mub`). -/
  mu : mlenOf cd ≤ 613 → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)
  /-- `|M| ≥ 614`: μ's sponge after blocks `0 … 4` is slot 1 of `KS`. -/
  muks : 613 < mlenOf cd → ∃ S : Nat → Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 1 = absorbPre 136 (padMu cd) 5
  /-- Both blocks of the SampleInBall stream. -/
  cb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)
  zIdx : ZeroOn m IDX (IDX + 256)
  zNeg : ZeroOn m NNEG (NNEG + 64)
  flag0 : word m FLAG = 0

/-- After the side buffers are zeroed and the hints decoded (pc 5183). -/
structure InvHA (cd m : ByteArray) : Prop extends InvWA cd m where
  hp : HPAt m cd
  zCw : ZeroOn m CW (CW + 8192)

/-- After μ (pc 6020). -/
structure Inv6A (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  cb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)
  fresh : SibFresh m
  fmu : FinMu m cd
  flag0 : word m FLAG = 0

end MlDsaOptGlam44.Proofs
