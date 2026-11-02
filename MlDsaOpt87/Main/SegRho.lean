import MlDsaOpt87.Main.S1.Rho
/-! # Segment `3122 … 3371`: `RHO1` (4 `spr` calls) -/

namespace MlDsaOpt87.Proofs

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
      Reach (callState s 3122 [flag b] m) (callState s 3371 [flag b] m') Gas.pRho := by
  exact S1.seg_rho_proof hs hcd hI b

end MlDsaOpt87.Proofs
