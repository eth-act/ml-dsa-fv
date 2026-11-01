import MlDsaOpt65.Main.Base
import MlDsaOpt65.Main.Mu.Proof
/-! # Segment `5236 … 6545`: μ from the SIMD slot (`|M| ≤ 69`) or `hash_mu` (`kf1`). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- `|M| ≤ 69`: replicate the eight `MU` lanes into `FIN[0, 8)`. Otherwise `hash_mu`: `KS1`
of the sponge absorbing `tr ‖ 0 ‖ 0 ‖ M` (`TRL` lanes, `absorb17` per 136-byte block of
calldata from `HDR`), `(66 + |M|)/136 + 1` loop visits, the final `kf1`, μ lanes replicated
into `FIN[0, 8)`. The proof (`Main/Mu/*`) is `MlDsaOpt44/Main/Mu/*` relocated to this artifact. -/
theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5236 [flag b] m) (callState s 6545 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) :=
  S6Mu.seg_mu_proof hs hcd hI b

end MlDsaOpt65.Proofs
