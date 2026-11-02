import MlDsaOptGlam87.Main.S1.Rho
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegRho.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `3122 … 3371`: `RHO1` (4 `spr` calls) -/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `3122 … 3371` (proved in `Main/S1/Rho.lean`): `init_rho1` for ML-DSA-87 (ρ lanes only, no c̃ rider):
one `CALLDATALOAD`, byte swap, four `spr` calls storing `RHO1[x]`
(`Rho1At`). Mirror `MlDsaOpt44/Main/SegRho.lean` + `Main/Rho/*`. -/
theorem seg_rho {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv3 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv4 s.executionEnv.calldata m' ∧
      Reach (callState s 2081 [flag b] m) (callState s 2330 [flag b] m') Gas.pRho := by
  exact S1.seg_rho_proof hs hcd hI b

end MlDsaOptGlam87.Proofs
