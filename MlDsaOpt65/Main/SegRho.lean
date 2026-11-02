import MlDsaOpt65.Main.S1.Rho
/-! # Segment `3115 … 3565`: `RHO1` (spread ρ and c̃ lanes, ten `spr` calls). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- Proved in `Main/S1/Rho.lean` (`seg_rho_proof`; four ρ lanes and six c̃
lanes, `bswap` network then `spr`, `MSTORE` to `RHO1 + 32 x`). -/
theorem seg_rho {s : State} (hs : Ctx s) {m : ByteArray}
    (hI : Inv3 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv4 s.executionEnv.calldata m' ∧
      Reach (callState s 3106 [flag b] m) (callState s 3556 [flag b] m') Gas.pRho := by
  exact S1.seg_rho_proof hs hI b

end MlDsaOpt65.Proofs
