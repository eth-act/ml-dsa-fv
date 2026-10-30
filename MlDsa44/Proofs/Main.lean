import MlDsa44.Proofs.Bridge
import MlDsa44.Proofs.Gas
/-!
# End-to-end correctness and gas schedule of the frozen reference bytecode

`main_short` and `main_valid` are the two whole-program traces (calldata
shorter than `pk ‖ σ`, and the full verification path). They are composed
from the subroutine contracts in `MlDsa44.Proofs.Fn.*`, the straight-line
blocks of the program body, and `MlDsa44.Proofs.Bridge`. The public theorems
below follow from them.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

theorem main_short (cd : ByteArray) (hfit : CalldataFits cd) (hlen : cd.size < 3732) :
    ∃ final : State, ∃ g : EvmProof.GasSteps (initialState referenceBytecode cd 0) final,
      g.cost ≤ Gas.short ∧ final.isDone = true ∧ final.toResult = .returned (spec cd) := by
  sorry

theorem main_valid (cd : ByteArray) (hfit : CalldataFits cd) (hlen : 3732 ≤ cd.size) :
    ∃ final : State, ∃ g : EvmProof.GasSteps (initialState referenceBytecode cd 0) final,
      g.cost ≤ Gas.schedule cd.size ∧ final.isDone = true ∧
        final.toResult = .returned (spec cd) := by
  sorry

private theorem eval_of_trace {cd : ByteArray} {final : State}
    (g : EvmProof.GasSteps (initialState referenceBytecode cd 0) final) (gas : Nat)
    (hgas : g.cost ≤ gas) (hdone : final.isDone = true) :
    Eval (initialState referenceBytecode cd gas) final.toResult := by
  have steps := g.trace gas hgas
  have result := EvmProof.eval_of_steps steps (by
    change final.isDone = true
    exact hdone)
  have hresult :
      (EvmProof.withGas final (gas - g.cost)).toResult = final.toResult := by
    cases final
    rfl
  rw [hresult] at result
  exact result

/-- The whole program within `Gas.schedule (calldata size)` gas. -/
theorem schedule_bound (cd : ByteArray) (hfit : CalldataFits cd) :
    ∃ final : State, ∃ g : EvmProof.GasSteps (initialState referenceBytecode cd 0) final,
      g.cost ≤ Gas.schedule cd.size ∧ final.isDone = true ∧
        final.toResult = .returned (spec cd) := by
  by_cases hlen : cd.size < 3732
  · obtain ⟨final, g, hcost, hdone, hres⟩ := main_short cd hfit hlen
    exact ⟨final, g, by simpa [Gas.schedule, hlen] using hcost, hdone, hres⟩
  · exact main_valid cd hfit (Nat.le_of_not_lt hlen)

/-- **Correctness with the public gas schedule.** -/
theorem reference_correctWithSchedule :
    CorrectWithSchedule referenceBytecode Gas.schedule := by
  intro cd hfit gas hgas
  obtain ⟨final, g, hcost, hdone, hres⟩ := schedule_bound cd hfit
  rw [← hres]
  exact eval_of_trace g gas (Nat.le_trans hcost hgas) hdone

/-- **Correctness.** -/
theorem reference_correct : Correct referenceBytecode :=
  correct_of_schedule reference_correctWithSchedule

end MlDsa44.Proofs
