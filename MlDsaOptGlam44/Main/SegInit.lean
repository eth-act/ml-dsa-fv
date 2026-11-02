import MlDsaOptGlam44.Main.Init.Blocks
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegInit.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `0 … 992`: size check, memory sizing, the `RC4`/`RC1` iota tables (straight line). -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

/-- `0 … 992` from the frame entry (memory empty, not yet sized). -/
theorem seg_init {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    ∃ m, Inv0 m ∧
      Reach (callState s 0 [] .empty) (callState (sized s) 15 [] m)
        (Gas.pInit + MachineState.memCost memWords) := by
  exact seg_init_proof h0 haw hcd hfit


end MlDsaOptGlam44.Proofs
