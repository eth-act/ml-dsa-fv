import MlDsaOpt87.Main.Base
import MlDsaOpt87.Main.Mu.Proof
/-! # Segment `5593 … 6591`: μ by `kf1` (`hash_mu`) -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `5593 … 6591`: `KS[x] := cpl x (rep TRL[x])` (`x < 8`), `hash_mu`:
zero lanes 8–24, absorb `0 ‖ 0 ‖ M[0, 70)` inline, loop `(66 + |M|) / 136`
times `kf1` + `absorb17`, pad, `kf1`, `FIN[x] := rep μ_x` (`FinMu`). The proof
(`Main/Mu/*`) is the long-message branch of `MlDsaOpt44/Main/Mu/*` relocated to
this artifact (ML-DSA-87 has no `|M| ≤ 69` branch). -/
theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv6 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 5593 [flag b] m) (callState s 6591 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) :=
  S6Mu.seg_mu_proof hs hcd hI b

end MlDsaOpt87.Proofs
