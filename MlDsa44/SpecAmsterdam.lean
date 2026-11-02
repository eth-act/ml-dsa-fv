import MlDsa44.Spec
set_option warningAsError true
/-!
# ML-DSA-44 verifier on Amsterdam (Glamsterdam): the statement an auditor must accept

The statements of `MlDsa44/Spec.lean` with the frame on the `Amsterdam` fork
instead of `Osaka`, for bytecode that uses EIP-8024 (`DUPN`, `SWAPN`,
`EXCHANGE`) and EIP-7954's code size (`MlDsaOpt/44/glam/`). Everything else
(the interface, `accepts`, `spec`, `CalldataFits`, the deployment address,
the precompile configuration and every other field of the fixed frame) is
`MlDsa44`'s: `initialState` is `MlDsa44.initialState` with only the fork
changed, and `FrameEntry` differs from `MlDsa44.FrameEntry` only in its fork
field.
-/

namespace MlDsa44.Amsterdam

open EvmSemantics
open EvmSemantics.EVM

/-- `MlDsa44.initialState` on the `Amsterdam` fork. -/
def initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let s := MlDsa44.initialState code calldata gas
  { s with executionEnv := { s.executionEnv with fork := .Amsterdam } }

/-- **Correctness** (`MlDsa44.Correct` on `Amsterdam`). -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval (initialState code calldata g) (.returned (spec calldata))

/-- **Correctness with a gas bound** (`MlDsa44.CorrectWithSchedule` on `Amsterdam`). -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata → ∀ g : Nat,
    schedule calldata.size ≤ g →
      Eval (initialState code calldata g) (.returned (spec calldata))

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  fun calldata hfit => ⟨schedule calldata.size, fun g hg => h calldata hfit g hg⟩

/-- `s` is the first state of a fresh `Amsterdam` frame executing `code` as
bytecode (`MlDsa44.FrameEntry` with the fork changed). -/
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
(`MlDsa44.CorrectInAnyContextWithSchedule` on `Amsterdam`). -/
def CorrectInAnyContextWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ s : EVM.State, FrameEntry code s →
    schedule s.executionEnv.calldata.size ≤ s.gasAvailable →
    ∃ t : EVM.State, Steps s t ∧
      t.halt = .Returned ∧ t.hReturn = spec s.executionEnv.calldata ∧
      s.gasAvailable - schedule s.executionEnv.calldata.size ≤ t.gasAvailable ∧
      t = { s with pc := t.pc, stack := t.stack, memory := t.memory,
                   activeWords := t.activeWords, halt := t.halt, hReturn := t.hReturn,
                   gasAvailable := t.gasAvailable }

/-- **Correctness in any top-level context** (`MlDsa44.CorrectInAnyContext` on `Amsterdam`). -/
def CorrectInAnyContext (code : ByteArray) : Prop :=
  ∀ s : EVM.State, FrameEntry code s → s.callStack = [] →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval { s with gasAvailable := g } (.returned (spec s.executionEnv.calldata))

end MlDsa44.Amsterdam
