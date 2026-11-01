import MlDsaOpt65.Main.Base
/-! # Segment `6545 … 6555`: `sib`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegSib.lean` with the 65 `sib_call`; stream
`cStream cd` from `CB`, `cStream_size`). -/
theorem seg_sib {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv6 cd m) (b : Bool) :
    ∃ m', Inv7 cd m' ∧
      Reach (callState s 6545 [flag b] m) (callState s 6555 [flag (b && okC cd)] m') Gas.pSib := by
  sorry

end MlDsaOpt65.Proofs
