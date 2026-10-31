import MlDsa.Spec.Interface
set_option warningAsError true
/-!
# ML-DSA-65 verifier: the statement an auditor must accept

Interface (EIP-8355, `VERIFY_MLDSA65`, precompile 0x13): calldata is
`pk (1952 bytes) ‖ σ (3309 bytes) ‖ M (the remaining bytes)`, no length
fields, empty context string. The contract always returns one 32-byte word:
`1` if `ML-DSA.Verify(pk, M, σ, "")` accepts for ML-DSA-65 and `0`
otherwise, including for calldata shorter than 5261 bytes. It never reverts
for lack of validity.

The definitions are `MlDsa.Interface` (the statements of `MlDsa44.Spec`,
parametric in the FIPS 204 parameter set) instantiated with
`Params.mldsa65` (`MlDsa/Spec/Params.lean`) and the deployment address
0x8213. The FIPS 204 transcription is `MlDsa/Spec/Fips204.lean`.
-/

namespace MlDsa65

open EvmSemantics
open MlDsa

abbrev params : Params := .mldsa65

def pkLen : Nat := Fips204.pkLen params
def sigLen : Nat := Fips204.sigLen params

example : pkLen = 1952 ∧ sigLen = 3309 := by decide

/-- Verification result for raw EIP-8355 calldata. -/
abbrev accepts (input : ByteArray) : Bool := Interface.accepts params input

/-- The returned word: 31 zero bytes followed by `1` or `0`. -/
abbrev spec (input : ByteArray) : ByteArray := Interface.spec params input

/-- A non-precompile deployment address. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8213

/-- The explicit fixed Osaka frame used to judge the bytecode. -/
abbrev initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  Interface.initialState deployAddress code calldata gas

abbrev FrameEntry (code : ByteArray) (s : EVM.State) : Prop := Interface.FrameEntry code s

/-- **Correctness.** -/
abbrev Correct (code : ByteArray) : Prop := Interface.Correct params deployAddress code

/-- **Correctness with a gas bound.** -/
abbrev CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  Interface.CorrectWithSchedule params deployAddress code schedule

/-- **Frame-level correctness in any context, with a gas bound.** -/
abbrev CorrectInAnyContextWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  Interface.CorrectInAnyContextWithSchedule params code schedule

/-- **Correctness in any top-level context.** -/
abbrev CorrectInAnyContext (code : ByteArray) : Prop :=
  Interface.CorrectInAnyContext params code

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  Interface.correct_of_schedule params deployAddress h

end MlDsa65
