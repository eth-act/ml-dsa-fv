import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Decode
/-! # Segment `5551 … 5665`: zero the side buffers, HintBitUnpack (v4, open)

`CW`, `HP`, `HP + 0x2000` served as side buffers during ExpandA: one `MSTORE`
of zero at `CW`, the zero prefix doubled by `MCOPY` up to 8 KB, copied to
`HP`, `HP + 0x2000`; `dhint`; `AND`. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

theorem seg_zd {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvW s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvH s.executionEnv.calldata m' ∧
      Reach (callState s 5551 [flag b] m)
        (callState s 5665 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  sorry

end MlDsaOpt87.Proofs
