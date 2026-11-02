import MlDsaOptGlam87.Main.S1.Fin
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegFin.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `6805 … RETURN`: the final hash, the c̃ comparison and the return -/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `6805 … RETURN` (proved in `Main/S1/{FinBlocks,Fin}.lean`): zero `KS`, eight visits of the 17-lane loop over
`FIN` (136 lanes, `kf1` each), the padding block (`0x1F` in lane 0, `0x80` in
lane 16) and `kf1`, then compare the first 8 output lanes with `c̃` (two
32-byte `CALLDATALOAD`s) and `mstore(0, ok); return(0, 32)`. The comparison
`E` is the commitment check whenever `FIN` holds a 1088-byte hash input.
Mirror `MlDsaOpt44/Main/SegFin.lean` + `Main/Fin/*`. -/
theorem seg_fin {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC1Table m) (b : Bool) :
    ∃ E : Bool, ∃ pc stk m',
      (∀ X : ByteArray, X.size = 1088 → FinAt m X →
        E = (ctOf s.executionEnv.calldata == Fips204.H X 64)) ∧
      Reach (callState s 5742 [flag b] m)
        (finalState s pc stk m' (if (b && E) = true then 1 else 0)) Gas.pFin := by
  exact S1.seg_fin_proof hs hcd hrc b

end MlDsaOptGlam87.Proofs
