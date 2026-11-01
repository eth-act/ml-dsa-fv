import MlDsaOpt65.Main.Base
/-! # Segment `6555 … 6610`: `tbuild`, `csum` for both row groups. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegCt.lean`). `tbuild [TT, 32]`,
`csum [SP, TT]` (rows 0–3), `tbuild [TT + 0x1800, 0x520]`, `csum [SP + 0x2000, TT + 0x1800]`
(rows 4–7 of the window table; rows 4, 5 used). -/
theorem seg_ct {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv7 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv8 s.executionEnv.calldata m' ∧
      Reach (callState s 6555 [flag b] m) (callState s 6610 [flag b] m') Gas.pCt := by
  sorry

end MlDsaOpt65.Proofs
