import MlDsaOptGlam87.Main.Base
import MlDsaOptGlam87.Main.Mu.Proof
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegMu.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `5665 … 6663`: μ by `kf1` (`hash_mu`) -/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `5665 … 6663`: `KS[x] := cpl x (rep TRL[x])` (`x < 8`), `hash_mu`:
zero lanes 8–24, absorb `0 ‖ 0 ‖ M[0, 70)` inline, loop `(66 + |M|) / 136`
times `kf1` + `absorb17`, pad, `kf1`, `FIN[x] := rep μ_x` (`FinMu`). The proof
(`Main/Mu/*`) is the long-message branch of `MlDsaOpt44/Main/Mu/*` relocated to
this artifact (ML-DSA-87 has no `|M| ≤ 69` branch). -/
theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 4624 [flag b] m) (callState s 5622 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) :=
  S6Mu.seg_mu_proof hs hcd hI b

end MlDsaOptGlam87.Proofs
