import MlDsa.Spec.Interface
set_option warningAsError true
/-!
# ML-DSA-87 verifier: the statement an auditor must accept

Interface (EIP-8355, `VERIFY_MLDSA87`, precompile 0x14): calldata is
`pk (2592 bytes) ‖ σ (4627 bytes) ‖ M (the remaining bytes)`, no length
fields, empty context string. The contract always returns one 32-byte word:
`1` if `ML-DSA.Verify(pk, M, σ, "")` accepts for ML-DSA-87 and `0`
otherwise, including for calldata shorter than 7219 bytes. It never reverts
for lack of validity.

The definitions are `MlDsa.Interface` (the statements of `MlDsa44.Spec`,
parametric in the FIPS 204 parameter set) instantiated with
`Params.mldsa87` (`MlDsa/Spec/Params.lean`) and the deployment address
0x8214. The FIPS 204 transcription is `MlDsa/Spec/Fips204.lean`.
-/

namespace MlDsa87

open EvmSemantics
open MlDsa

abbrev params : Params := .mldsa87

def pkLen : Nat := Fips204.pkLen params
def sigLen : Nat := Fips204.sigLen params

example : pkLen = 2592 ∧ sigLen = 4627 := by decide

/-- Verification result for raw EIP-8355 calldata. -/
abbrev accepts (input : ByteArray) : Bool := Interface.accepts params input

/-- The returned word: 31 zero bytes followed by `1` or `0`. -/
abbrev spec (input : ByteArray) : ByteArray := Interface.spec params input

/-- A non-precompile deployment address. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8214

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

end MlDsa87
