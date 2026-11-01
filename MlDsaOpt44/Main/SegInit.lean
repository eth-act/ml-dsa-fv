import MlDsaOpt44.Main.Base
/-! # Segment `0 … 992`: size check, memory sizing, the `RC4`/`RC1` iota tables (straight line). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- `0 … 992` from the frame entry (memory empty, not yet sized). -/
theorem seg_init {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m, Inv0 m ∧
      Reach (callState s 0 [] .empty) (callState (sized s) 992 [] m)
        (Gas.pInit + MachineState.memCost memWords) := by
  sorry


end MlDsaOpt44.Proofs
