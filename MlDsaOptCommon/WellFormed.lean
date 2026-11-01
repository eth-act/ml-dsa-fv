import EvmProof.Stepper
set_option warningAsError true
/-!
A kernel-reducible Boolean form of `EvmProof.Stepper.WellFormed`, so a
whole-artifact certificate is one `rfl` instead of one tactic goal per
instruction.
-/

namespace MlDsaOptCommon

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def plainOpB : Operation → Bool
  | .Push _ | .DupN _ | .SwapN _ | .Exchange _ => false
  | _ => true

theorem plainOp_of_plainOpB {op : Operation} (h : plainOpB op = true) : plainOp op := by
  cases op <;> simp_all [plainOpB, plainOp]

def wellFormedB (fork : Fork) : Instr → Bool
  | .push width value =>
      decide (value.toNat < 256 ^ width.val) &&
        (Operation.Push ⟨width⟩).availableInFork fork
  | .op op =>
      decide (Decode.opcodeOf (Instr.opByte op) = some op) && plainOpB op &&
        op.availableInFork fork

theorem wellFormed_of_wellFormedB {fork : Fork} {i : Instr}
    (h : wellFormedB fork i = true) : EvmProof.Stepper.WellFormed fork i := by
  cases i with
  | push width value =>
    simp only [wellFormedB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  | op op =>
    simp only [wellFormedB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, plainOp_of_plainOpB h.1.2, h.2⟩

theorem allWellFormed_of_all {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (h : artifact.instructions.all (wellFormedB fork) = true) :
    EvmProof.Stepper.AllWellFormed artifact fork := by
  unfold EvmProof.Stepper.AllWellFormed
  rw [List.all_eq_true] at h ⊢
  intro i hi
  exact decide_eq_true (wellFormed_of_wellFormedB (h i hi))

end MlDsaOptCommon
