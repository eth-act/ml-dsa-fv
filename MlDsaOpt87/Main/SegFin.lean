import MlDsaOpt87.Main.Base
/-! # Segment `6724 … RETURN`: the final hash, the c̃ comparison and the return -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `6724 … RETURN`, open: zero `KS`, eight visits of the 17-lane loop over
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
      Reach (callState s 6724 [flag b] m)
        (finalState s pc stk m' (if (b && E) = true then 1 else 0)) Gas.pFin := by
  sorry

end MlDsaOpt87.Proofs
