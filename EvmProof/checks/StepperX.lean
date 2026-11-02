import EvmProof.StepperX
/-! End-to-end check of the EIP-8024 stepper
(`lake env lean EvmProof/checks/StepperX.lean`).

The EIP-8024 DUPN test case (`PUSH1 1; PUSH1 0; DUP1 ×15; DUPN 0x80`) as an
`XArtifact`: its byte equation and availability certificate are `rfl`, the
symbolic run is `rfl`, and `runXLocatedBlock_sound` turns it into a
gas-parametric trace of the relational semantics on an Amsterdam frame, with
the exact cost (18 instructions × 3 gas). On Osaka the certificate fails. -/

open EvmSemantics EvmSemantics.EVM EvmProof EvmProof.Stepper YulEvmCompiler

namespace EvmProof.StepperXCheck

def instrs : List XInstr :=
  [.base (.push 1 1), .base (.push 1 0)] ++ List.replicate 15 (.base (.op (.Dup ⟨0⟩))) ++
    [.dupN 0x80]

def code : ByteArray := mkCode
  [0x60, 0x01, 0x60, 0x00, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
   0x80, 0x80, 0x80, 0x80, 0xe6, 0x80]

def artifact : XArtifact := ⟨code, instrs, rfl⟩

theorem cert : XAllWellFormed artifact .Amsterdam := xallWellFormed_of_all (by decide)

example : ¬ (artifact.instructions.all (xwellFormedB .Osaka) = true) := by decide

def path : List (XLocated artifact .Amsterdam) :=
  (List.finRange 18).map (XLocated.ofIndex cert)

/-- The final stack: the DUPN copied the 17th item (the `1`). -/
def final : List UInt256 := [1] ++ List.replicate 16 0 ++ [1]

def s0 : State :=
  { (default : State) with
    gasAvailable := 1000
    executionEnv := { (default : ExecutionEnv) with code, fork := .Amsterdam } }

theorem run : runXLocatedBlock path s0 = some { s0 with stack := final, pc := 21 } := by
  rfl

/-- The relational semantics reaches the final stack from every gas budget of
at least 54. -/
def trace : GasSteps s0 { s0 with stack := final, pc := 21 } :=
  runXLocatedBlock_sound artifact .Amsterdam path rfl rfl run rfl rfl

example : trace.cost = 54 := by rfl

end EvmProof.StepperXCheck
