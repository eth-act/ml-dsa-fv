import MlDsa65.Spec
import MlDsa.Spec.InterfaceAmsterdam
set_option warningAsError true
/-!
# ML-DSA-65 verifier on Amsterdam (Glamsterdam): the statement an auditor must accept

The statements of `MlDsa65/Spec.lean` with the frame on the `Amsterdam` fork
instead of `Osaka` (`MlDsa.Interface.Amsterdam`), for bytecode that uses EIP-8024
(`DUPN`, `SWAPN`, `EXCHANGE`) and EIP-7954's code size (`MlDsaOpt/65/glam/`).
The parameter set, `accepts`, `spec` and the deployment address are `MlDsa65`'s.
-/

namespace MlDsa65.Amsterdam

open EvmSemantics
open MlDsa

/-- `MlDsa65.initialState` on the `Amsterdam` fork. -/
abbrev initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  Interface.Amsterdam.initialState deployAddress code calldata gas

abbrev FrameEntry (code : ByteArray) (s : EVM.State) : Prop := Interface.Amsterdam.FrameEntry code s

/-- **Correctness** (`MlDsa65.Correct` on `Amsterdam`). -/
abbrev Correct (code : ByteArray) : Prop := Interface.Amsterdam.Correct params deployAddress code

/-- **Correctness with a gas bound** (`MlDsa65.CorrectWithSchedule` on `Amsterdam`). -/
abbrev CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  Interface.Amsterdam.CorrectWithSchedule params deployAddress code schedule

/-- **Frame-level correctness in any context, with a gas bound** (on `Amsterdam`). -/
abbrev CorrectInAnyContextWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  Interface.Amsterdam.CorrectInAnyContextWithSchedule params code schedule

/-- **Correctness in any top-level context** (on `Amsterdam`). -/
abbrev CorrectInAnyContext (code : ByteArray) : Prop :=
  Interface.Amsterdam.CorrectInAnyContext params code

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  Interface.Amsterdam.correct_of_schedule params deployAddress h

end MlDsa65.Amsterdam
