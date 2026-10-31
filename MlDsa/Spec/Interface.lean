import EvmSemantics.EVM.BigStep
import MlDsa.Spec.Fips204
set_option warningAsError true
/-!
# EIP-8355 verifier statements, parametric in the parameter set

The statements of `MlDsa44.Spec`, for any `P : Params` and deployment address.
EIP-8355 (`VERIFY_MLDSA44/65/87`): calldata is `pk ‖ σ ‖ M` with
`|pk| = pkLen P`, `|σ| = sigLen P`, no length fields, empty context string.
The contract always returns one 32-byte word: `1` if
`ML-DSA.Verify(pk, M, σ, "")` accepts and `0` otherwise, including for
calldata shorter than `pkLen P + sigLen P`. It never reverts for lack of
validity.

`MlDsa.Bridge44` proves that instantiating these with `Params.mldsa44` and
address `0x8212` gives exactly the definitions of `MlDsa44.Spec`.
-/

namespace MlDsa.Interface

open EvmSemantics
open EvmSemantics.EVM

variable (P : Params)

/-- Verification result for raw EIP-8355 calldata. -/
def accepts (input : ByteArray) : Bool :=
  decide (Fips204.pkLen P + Fips204.sigLen P ≤ input.size) &&
    Fips204.verify P (input.extract 0 (Fips204.pkLen P))
      (input.extract (Fips204.pkLen P + Fips204.sigLen P) input.size)
      (input.extract (Fips204.pkLen P) (Fips204.pkLen P + Fips204.sigLen P))

/-- The returned word: 31 zero bytes followed by `1` or `0`. -/
def spec (input : ByteArray) : ByteArray :=
  (ByteArray.mk (Array.replicate 31 0)).push (if accepts P input then 1 else 0)

/-- Calldata sizes realizable at the protocol boundary. -/
def CalldataFits (input : ByteArray) : Prop := input.size < 2 ^ 64

def executionConfig : PrecompileConfig := {}

variable (deployAddress : AccountAddress)

/-- The explicit fixed Osaka frame used to judge the bytecode, deployed at
`deployAddress`. -/
def initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let account : Account := { Account.empty with code }
  let accounts := AccountMap.empty.set deployAddress account
  let env : ExecutionEnv := {
    (default : ExecutionEnv) with
    address := deployAddress
    codeAddr := deployAddress
    origin := AccountAddress.ofNat 0
    caller := AccountAddress.ofNat 0
    weiValue := 0
    calldata
    code
    gasPrice := 0
    depth := 0
    permitStateMutation := true
    blobVersionedHashes := #[]
    fork := .Osaka
    precompileConfig := executionConfig
  }
  { (default : EVM.State) with
    pc := 0
    stack := []
    execLength := 0
    halt := .Running
    callStack := []
    gasAvailable := gas
    activeWords := 0
    memory := .empty
    returnData := .empty
    hReturn := .empty
    accountMap := accounts
    substate := { Substate.empty with originalAccountMap := accounts }
    executionEnv := env }

/-- **Correctness.** For every realizable calldata, every sufficiently large
gas budget returns the verification word. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval (initialState deployAddress code calldata g) (.returned (spec P calldata))

/-- **Correctness with a gas bound.** `schedule calldata.size` gas suffices. -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata → ∀ g : Nat,
    schedule calldata.size ≤ g →
      Eval (initialState deployAddress code calldata g) (.returned (spec P calldata))

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule P deployAddress code schedule) :
    Correct P deployAddress code :=
  fun calldata hfit => ⟨schedule calldata.size, fun g hg => h calldata hfit g hg⟩

/-! ## Any calling context

`Correct` fixes one fresh top-level frame. The statements below quantify over
every entry state of a frame running `code`: the world state, caller, origin,
call value, executing address, gas price, depth, static flag, precompile
configuration and the enclosing call stack are all arbitrary. They do not
depend on `deployAddress`. -/

/-- `s` is the first state of a fresh Osaka frame executing `code` as bytecode
(not as a native precompile). -/
structure FrameEntry (code : ByteArray) (s : EVM.State) : Prop where
  code : s.executionEnv.code = code
  pc : s.pc = 0
  stack : s.stack = []
  memory : s.memory = .empty
  activeWords : s.activeWords = 0
  running : s.halt = .Running
  osaka : s.executionEnv.fork = .Osaka
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false
  calldataFits : CalldataFits s.executionEnv.calldata

/-- **Frame-level correctness in any context, with a gas bound.** From any
frame entry with at least `schedule |calldata|` gas, execution reaches a state
where the frame has halted by `RETURN` with the verification word, having used
at most `schedule |calldata|` gas. That state differs from the entry state only
in frame-local machine fields (pc, stack, memory, memory size, halt flag,
return buffer, gas): accounts, storage, substate (logs, refunds, touched and
destroyed accounts), return data, environment and the enclosing call stack are
untouched. -/
def CorrectInAnyContextWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ s : EVM.State, FrameEntry code s →
    schedule s.executionEnv.calldata.size ≤ s.gasAvailable →
    ∃ t : EVM.State, Steps s t ∧
      t.halt = .Returned ∧ t.hReturn = spec P s.executionEnv.calldata ∧
      s.gasAvailable - schedule s.executionEnv.calldata.size ≤ t.gasAvailable ∧
      t = { s with pc := t.pc, stack := t.stack, memory := t.memory,
                   activeWords := t.activeWords, halt := t.halt, hReturn := t.hReturn,
                   gasAvailable := t.gasAvailable }

/-- **Correctness in any top-level context.** The `Correct` conclusion from
every frame entry with no suspended callers. -/
def CorrectInAnyContext (code : ByteArray) : Prop :=
  ∀ s : EVM.State, FrameEntry code s → s.callStack = [] →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval { s with gasAvailable := g } (.returned (spec P s.executionEnv.calldata))

end MlDsa.Interface
