import MlDsaOpt65.Main.Base
/-! # Segment `0 … 992`: size check, memory sizing, the `RC4`/`RC1` iota tables (straight line). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/Init/*`, `seg_init_proof`). `0 … 992` from the
frame entry (memory empty, not yet sized): `PUSH2 5261; CALLDATASIZE; LT; PUSH2 short; JUMPI`
falls through, `MSTORE` at `0x16200` sizes memory to `memWords`, the 24 `RC4` and 24 `RC1`
words are stored; everything else in `[MISC, TOP)` stays zero. -/
theorem seg_init {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    ∃ m, Inv0 m ∧
      Reach (callState s 0 [] .empty) (callState (sized s) 992 [] m)
        (Gas.pInit + MachineState.memCost memWords) := by
  sorry

end MlDsaOpt65.Proofs
