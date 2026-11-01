import MlDsaOpt44.Layout
set_option warningAsError true
/-!
# Vocabulary of the ExpandA SIMD groups

`Rho1At` (what `init_rho1` leaves at `RHO1`). Light module: only
`MlDsaOpt44.Layout`, so the main-flow invariants need not wait for the group
proofs.
-/

namespace MlDsaOpt44.Proofs

open MlDsaOptCommon

/-- `RHO1[x] = spread(ρ lane x)`, `RHO1[4 + x] = spread(c̃ lane x)` (`init_rho1`). -/
def Rho1At (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 cd (8 * x)) ∧
    word m (RHO1 + 32 * (4 + x)) = spread (le64 cd (CTOFF + 8 * x))

end MlDsaOpt44.Proofs
