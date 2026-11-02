import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Decode
/-! # Segment `5242 … 5356`: zero the side buffers, HintBitUnpack (v4, open)

`CW`, `HP`, `HP + 0x2000` served as side buffers during ExpandA: one `MSTORE`
of zero at `CW`, the zero prefix doubled by `MCOPY` up to 8 KB, copied to
`HP`, `HP + 0x2000`; `dhint`; `AND`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

theorem seg_zd {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvW s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvH s.executionEnv.calldata m' ∧
      Reach (callState s 5242 [flag b] m)
        (callState s 5356 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  sorry

end MlDsaOpt65.Proofs
