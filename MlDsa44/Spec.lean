import EvmSemantics.EVM.BigStep
import MlDsa44.Spec.Fips204
set_option warningAsError true
/-!
# ML-DSA-44 verifier: the statement an auditor must accept

Interface (EIP-8355, `VERIFY_MLDSA44`): calldata is
`pk (1312 bytes) ‖ σ (2420 bytes) ‖ M (the remaining bytes)`, no length
fields, empty context string. The contract always returns one 32-byte word:
`1` if `ML-DSA.Verify(pk, M, σ, "")` accepts and `0` otherwise, including for
calldata shorter than 3732 bytes. It never reverts for lack of validity.

`Correct` fixes a fresh Osaka top-level frame (the same frame as the
eip8200-challenges statements) and quantifies over calldata and gas.
`CorrectWithSchedule` additionally fixes a gas budget that depends only on
the calldata length; it implies `Correct`.
-/

namespace MlDsa44

open EvmSemantics
open EvmSemantics.EVM

def pkLen : Nat := Fips204.pkLen
def sigLen : Nat := Fips204.sigLen

/-- Verification result for raw EIP-8355 calldata. -/
def accepts (input : ByteArray) : Bool :=
  decide (pkLen + sigLen ≤ input.size) &&
    Fips204.verify (input.extract 0 pkLen) (input.extract (pkLen + sigLen) input.size)
      (input.extract pkLen (pkLen + sigLen))

/-- The returned word: 31 zero bytes followed by `1` or `0`. -/
def spec (input : ByteArray) : ByteArray :=
  (ByteArray.mk (Array.replicate 31 0)).push (if accepts input then 1 else 0)

/-- Calldata sizes realizable at the protocol boundary. -/
def CalldataFits (input : ByteArray) : Prop := input.size < 2 ^ 64

/-- A non-precompile deployment address. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8212

def executionConfig : PrecompileConfig := {}

/-- The explicit fixed Osaka frame used to judge the bytecode. -/
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
gas budget returns the ML-DSA-44 verification word. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval (initialState code calldata g) (.returned (spec calldata))

/-- **Correctness with a gas bound.** `schedule calldata.size` gas suffices. -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata → ∀ g : Nat,
    schedule calldata.size ≤ g →
      Eval (initialState code calldata g) (.returned (spec calldata))

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  fun calldata hfit => ⟨schedule calldata.size, fun g hg => h calldata hfit g hg⟩

end MlDsa44
