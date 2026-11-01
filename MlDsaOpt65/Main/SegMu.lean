import MlDsaOpt65.Main.Base
/-! # Segment `5236 … 6545`: μ from the SIMD slot (`|M| ≤ 69`) or `hash_mu` (`kf1`). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/Mu/*`, `seg_mu_proof`). `|M| ≤ 69`: replicate the
eight `MU` lanes into `FIN[0, 8)`. Otherwise `hash_mu`: `KS1` of the sponge absorbing
`tr ‖ 0 ‖ 0 ‖ M` (`TRL` lanes, `absorb17` per 136-byte block of calldata from `HDR`),
`(66 + |M|)/136 + 1` loop visits, the final `kf1`, μ lanes replicated into `FIN[0, 8)`. -/
theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5236 [flag b] m) (callState s 6545 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry

end MlDsaOpt65.Proofs
