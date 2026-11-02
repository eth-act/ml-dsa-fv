import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Group
/-! # Segment `3477 … 3875`: the mixed group

`tr`'s blocks 0 … 4 in slot 0 (`trabs` before each `kf4`), column 2 rows
0 … 2 in slots 1 … 3; `gfix` on slots 1 … 3; the candidates are copied to
`SB`. `tr`'s sponge stays in slot 0 of `KS` for the window. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG2 s.executionEnv.calldata m' ∧
      Reach (callState s 3477 [flag b] m)
        (callState s 3875 [flag (b && okCol3 s.executionEnv.calldata 2)] m') Gas.pG2 := by
  sorry

end MlDsaOpt44.Proofs
