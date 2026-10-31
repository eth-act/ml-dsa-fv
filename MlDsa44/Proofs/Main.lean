import MlDsa44.Proofs.Bridge
import MlDsa44.Proofs.Gas
import MlDsa44.Proofs.Main.Valid
/-!
# End-to-end correctness and gas schedule of the frozen reference bytecode

`Main.short_trace` and `Main.valid_trace` are the two whole-program traces
(calldata shorter than `pk ‖ σ`, and the full verification path), from any
frame entry state. They are composed from the subroutine contracts in
`MlDsa44.Proofs.Fn.*`, the straight-line blocks of the program body, and
`MlDsa44.Proofs.Bridge`. The public theorems below follow from them.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

/-- The whole program from any frame entry, within `Gas.schedule` gas. -/
theorem frame_trace {s : State} (h : FrameEntry referenceBytecode s) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s final,
      g.cost ≤ Gas.schedule s.executionEnv.calldata.size ∧ final.halt = .Returned ∧
        final.hReturn = spec s.executionEnv.calldata ∧ Main.FrameLocal s final := by
  have h0 : Main.Ctx0 s := ⟨h.code, h.osaka, h.notPrecompile, h.running⟩
  have haw : s.activeWords.toNat = 0 := by rw [h.activeWords]; rfl
  have hpc : callState s 0 [] .empty = s := by
    have e : UInt256.ofNat 0 = s.pc := by rw [h.pc]; rfl
    unfold callState
    rw [e, ← h.stack, ← h.memory]
  by_cases hlen : s.executionEnv.calldata.size < 3732
  · obtain ⟨final, g, hcost, hres⟩ := Main.short_trace h0 haw hpc hlen
    exact ⟨final, g, by simpa [Gas.schedule, hlen] using hcost, hres⟩
  · exact Main.valid_trace h0 haw hpc h.calldataFits (Nat.le_of_not_lt hlen)

private theorem withGas_self (s : State) : EvmProof.withGas s s.gasAvailable = s := by
  cases s
  rfl

private theorem frameLocal_withGas {s f : State} (x : Nat) (hf : Main.FrameLocal s f) :
    Main.FrameLocal s (EvmProof.withGas f x) := by
  unfold Main.FrameLocal at hf ⊢
  rw [hf]
  rfl

/-- **Frame-level correctness in any context, with the public gas schedule.** -/
theorem reference_correctInAnyContextWithSchedule :
    CorrectInAnyContextWithSchedule referenceBytecode Gas.schedule := by
  intro s h hgas
  obtain ⟨final, g, hcost, hhalt, hret, hloc⟩ := frame_trace h
  have steps := g.trace s.gasAvailable (Nat.le_trans hcost hgas)
  rw [withGas_self] at steps
  refine ⟨_, steps, hhalt, hret, ?_, frameLocal_withGas _ hloc⟩
  change _ ≤ s.gasAvailable - g.cost
  omega

/-- **Correctness in any top-level context.** -/
theorem reference_correctInAnyContext : CorrectInAnyContext referenceBytecode := by
  intro s h hcs
  refine ⟨Gas.schedule s.executionEnv.calldata.size, fun g hg => ?_⟩
  have h' : FrameEntry referenceBytecode { s with gasAvailable := g } :=
    { h with }
  obtain ⟨t, steps, hhalt, hret, -, hloc⟩ :=
    reference_correctInAnyContextWithSchedule _ h' hg
  have hdone : t.isDone = true := by
    rw [hloc]
    simp [State.isDone, State.isHalted, State.isRunning, hhalt, hcs]
  have heval := EvmProof.eval_of_steps steps hdone
  rwa [State.toResult_returned t hhalt, hret] at heval

/-- The fixed frame of `Correct` is one frame entry. -/
theorem initialState_frameEntry (cd : ByteArray) (hfit : CalldataFits cd) (g : Nat) :
    FrameEntry referenceBytecode (initialState referenceBytecode cd g) where
  code := rfl
  pc := rfl
  stack := rfl
  memory := rfl
  activeWords := rfl
  running := rfl
  osaka := rfl
  notPrecompile := by simp [initialState]; decide
  calldataFits := hfit

/-- **Correctness with the public gas schedule.** -/
theorem reference_correctWithSchedule :
    CorrectWithSchedule referenceBytecode Gas.schedule := by
  intro cd hfit gas hgas
  have h := reference_correctInAnyContext _ (initialState_frameEntry cd hfit gas) rfl
  obtain ⟨t, steps, hhalt, hret, -, hloc⟩ :=
    reference_correctInAnyContextWithSchedule _ (initialState_frameEntry cd hfit gas) hgas
  have hdone : t.isDone = true := by
    rw [hloc]
    simp [State.isDone, State.isHalted, State.isRunning, hhalt, initialState]
  have heval := EvmProof.eval_of_steps steps hdone
  rwa [State.toResult_returned t hhalt, hret] at heval

theorem reference_correct : Correct referenceBytecode :=
  correct_of_schedule reference_correctWithSchedule

end MlDsa44.Proofs
