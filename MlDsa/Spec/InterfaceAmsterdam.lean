import MlDsa.Spec.Interface
set_option warningAsError true
/-!
# EIP-8355 verifier statements on Amsterdam (Glamsterdam), parametric in the parameter set

The statements of `MlDsa.Interface` with the frame on the `Amsterdam` fork
instead of `Osaka`, for bytecode that uses EIP-8024 (`DUPN`, `SWAPN`,
`EXCHANGE`) and EIP-7954's code size (`MlDsaOpt/NN/glam/`). Everything else
(`accepts`, `spec`, `CalldataFits`, the deployment address, the precompile
configuration and every other field of the fixed frame) is `MlDsa.Interface`'s:
`initialState` is `MlDsa.Interface.initialState` with only the fork changed, and
`FrameEntry` differs from `MlDsa.Interface.FrameEntry` only in its fork field.
`MlDsa44.Amsterdam` (`MlDsa44/SpecAmsterdam.lean`) is the same for ML-DSA-44's
own (non-parametric) statements.
-/

namespace MlDsa.Interface.Amsterdam

open EvmSemantics
open EvmSemantics.EVM

variable (P : Params) (deployAddress : AccountAddress)

/-- `MlDsa.Interface.initialState` on the `Amsterdam` fork. -/
def initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let s := Interface.initialState deployAddress code calldata gas
  { s with executionEnv := { s.executionEnv with fork := .Amsterdam } }

/-- **Correctness** (`MlDsa.Interface.Correct` on `Amsterdam`). -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval (initialState deployAddress code calldata g) (.returned (spec P calldata))

/-- **Correctness with a gas bound** (`MlDsa.Interface.CorrectWithSchedule` on `Amsterdam`). -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata → ∀ g : Nat,
    schedule calldata.size ≤ g →
      Eval (initialState deployAddress code calldata g) (.returned (spec P calldata))

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule P deployAddress code schedule) :
    Correct P deployAddress code :=
  fun calldata hfit => ⟨schedule calldata.size, fun g hg => h calldata hfit g hg⟩

/-- `s` is the first state of a fresh `Amsterdam` frame executing `code` as
bytecode (`MlDsa.Interface.FrameEntry` with the fork changed). -/
structure FrameEntry (code : ByteArray) (s : EVM.State) : Prop where
  code : s.executionEnv.code = code
  pc : s.pc = 0
  stack : s.stack = []
  memory : s.memory = .empty
  activeWords : s.activeWords = 0
  running : s.halt = .Running
  amsterdam : s.executionEnv.fork = .Amsterdam
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false
  calldataFits : CalldataFits s.executionEnv.calldata

/-- **Frame-level correctness in any context, with a gas bound**
(`MlDsa.Interface.CorrectInAnyContextWithSchedule` on `Amsterdam`). -/
def CorrectInAnyContextWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ s : EVM.State, FrameEntry code s →
    schedule s.executionEnv.calldata.size ≤ s.gasAvailable →
    ∃ t : EVM.State, Steps s t ∧
      t.halt = .Returned ∧ t.hReturn = spec P s.executionEnv.calldata ∧
      s.gasAvailable - schedule s.executionEnv.calldata.size ≤ t.gasAvailable ∧
      t = { s with pc := t.pc, stack := t.stack, memory := t.memory,
                   activeWords := t.activeWords, halt := t.halt, hReturn := t.hReturn,
                   gasAvailable := t.gasAvailable }

/-- **Correctness in any top-level context** (`MlDsa.Interface.CorrectInAnyContext` on `Amsterdam`). -/
def CorrectInAnyContext (code : ByteArray) : Prop :=
  ∀ s : EVM.State, FrameEntry code s → s.callStack = [] →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval { s with gasAvailable := g } (.returned (spec P s.executionEnv.calldata))

end MlDsa.Interface.Amsterdam
