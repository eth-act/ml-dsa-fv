import MlDsaOptGlam44.Main.Fin.Proof
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegFin.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `6001 … RETURN`: the final hash, the c̃ comparison and the return. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

/-- `6001 … RETURN`: hash `FIN` with `kf1`, compare with c̃, return. The
comparison `E` is the commitment check whenever `FIN` holds a well-formed
832-byte hash input. -/
theorem seg_fin {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC1Table m) (b : Bool) :
    ∃ E : Bool, ∃ pc stk m',
      (∀ X : ByteArray, X.size = 832 → FinAt m X → E = (ctOf s.executionEnv.calldata == Fips204.H X 32)) ∧
      Reach (callState s 6084 [flag b] m)
        (finalState s pc stk m' (if (b && E) = true then 1 else 0)) Gas.pFin := by
  exact seg_fin_proof hs hcd hrc b


end MlDsaOptGlam44.Proofs
