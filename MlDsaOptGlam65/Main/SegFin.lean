import MlDsaOptGlam65.Main.S1.Fin
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/SegFin.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `6293 … RETURN`: the final hash, the c̃ comparison and the return. -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

/-- Proved in `Main/S1/{FinBlocks,Fin}.lean` (`seg_fin_proof`). Hash the 104 `FIN` lanes
(`832` bytes) with `kf1` (six absorbing loop visits and the last permutation), compare the
first 48 squeezed bytes with c̃ (two `EQ`s on 32 + 16 bytes), `mstore(0, b ∧ E)`,
`return(0, 32)`. The comparison `E` is the commitment check whenever `FIN` holds a
well-formed 832-byte hash input. -/
theorem seg_fin {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC1Table m) (b : Bool) :
    ∃ E : Bool, ∃ pc stk m',
      (∀ X : ByteArray, X.size = 832 → FinAt m X →
        E = (ctOf s.executionEnv.calldata == Fips204.H X 48)) ∧
      Reach (callState s 5964 [flag b] m)
        (finalState s pc stk m' (if (b && E) = true then 1 else 0)) Gas.pFin := by
  exact S1.seg_fin_proof hs hcd hrc b

end MlDsaOptGlam65.Proofs
