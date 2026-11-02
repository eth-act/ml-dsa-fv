import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Decode
/-! # Segment `4973 … 5075`: zero the side buffers, HintBitUnpack

`CW` and `HP` served as side buffers during ExpandA: one `MSTORE` of zero at
`CW`, the zero prefix doubled by `MCOPY` up to 8 KB, then copied to `HP`;
`dhint` decodes the hints into `HP`; `AND`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_zd {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvW s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvH s.executionEnv.calldata m' ∧
      Reach (callState s 4973 [flag b] m)
        (callState s 5075 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  sorry

end MlDsaOpt44.Proofs
