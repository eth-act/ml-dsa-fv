import MlDsaOptGlam65.Main.Valid
import MlDsa65.SpecAmsterdam
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main.lean` by `scripts/proofgen_port.py --glam 65`, then stated over `MlDsa65.Amsterdam`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# End-to-end correctness and gas schedule of `MlDsaOpt/65/glam/opt.hex`

`short_trace` and `valid_trace` are the two whole-program traces (calldata
shorter than `pk ‖ σ`, and the full verification path) from any frame entry
state. They compose the segments of `Main/Seg*.lean`, which use the
subroutine contracts of `MlDsaOpt65/Fn`, and the bridge
`accepts_eq_optAccepts`. The statements below are the audited
`MlDsa65.Amsterdam` definitions (`MlDsa65/SpecAmsterdam.lean`: `MlDsa65.Spec` on the
`Amsterdam` fork) with `code := MlDsaOptGlam65.optBytecode`.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- The whole program from any frame entry, within `Gas.schedule` gas. -/
theorem frame_trace {s : State} (h : MlDsa65.Amsterdam.FrameEntry optBytecode s) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s final,
      g.cost ≤ Gas.schedule s.executionEnv.calldata.size ∧ final.halt = .Returned ∧
        final.hReturn = MlDsa65.spec s.executionEnv.calldata ∧ FrameLocal s final := by
  have h0 : Ctx0 s := ⟨h.code, h.amsterdam, h.notPrecompile, h.running⟩
  have haw : s.activeWords.toNat = 0 := by rw [h.activeWords]; rfl
  have hpc : callState s 0 [] .empty = s := by
    have e : UInt256.ofNat 0 = s.pc := by rw [h.pc]; rfl
    unfold callState
    rw [e, ← h.stack, ← h.memory]
  by_cases hlen : s.executionEnv.calldata.size < 5261
  · obtain ⟨final, g, hcost, hres⟩ := short_trace h0 haw hpc hlen
    exact ⟨final, g, by simpa [Gas.schedule, hlen] using hcost, hres⟩
  · exact valid_trace h0 haw hpc h.calldataFits (Nat.le_of_not_lt hlen)

private theorem withGas_self (s : State) : EvmProof.withGas s s.gasAvailable = s := by
  cases s
  rfl

private theorem frameLocal_withGas {s f : State} (x : Nat) (hf : FrameLocal s f) :
    FrameLocal s (EvmProof.withGas f x) := by
  unfold FrameLocal at hf ⊢
  rw [hf]
  rfl

/-- **Frame-level correctness in any context, with the public gas schedule.** -/
theorem opt_correctInAnyContextWithSchedule :
    MlDsa65.Amsterdam.CorrectInAnyContextWithSchedule optBytecode Gas.schedule := by
  intro s h hgas
  obtain ⟨final, g, hcost, hhalt, hret, hloc⟩ := frame_trace h
  have steps := g.trace s.gasAvailable (Nat.le_trans hcost hgas)
  rw [withGas_self] at steps
  refine ⟨_, steps, hhalt, hret, ?_, frameLocal_withGas _ hloc⟩
  change _ ≤ s.gasAvailable - g.cost
  omega

/-- **Correctness in any top-level context.** -/
theorem opt_correctInAnyContext : MlDsa65.Amsterdam.CorrectInAnyContext optBytecode := by
  intro s h hcs
  refine ⟨Gas.schedule s.executionEnv.calldata.size, fun g hg => ?_⟩
  have h' : MlDsa65.Amsterdam.FrameEntry optBytecode { s with gasAvailable := g } :=
    { h with }
  obtain ⟨t, steps, hhalt, hret, -, hloc⟩ :=
    opt_correctInAnyContextWithSchedule _ h' hg
  have hdone : t.isDone = true := by
    rw [hloc]
    simp [State.isDone, State.isHalted, State.isRunning, hhalt, hcs]
  have heval := EvmProof.eval_of_steps steps hdone
  rwa [State.toResult_returned t hhalt, hret] at heval

/-- The fixed frame of `Amsterdam.Correct` is one frame entry. -/
theorem initialState_frameEntry (cd : ByteArray) (hfit : Interface.CalldataFits cd) (g : Nat) :
    MlDsa65.Amsterdam.FrameEntry optBytecode (MlDsa65.Amsterdam.initialState optBytecode cd g) where
  code := rfl
  pc := rfl
  stack := rfl
  memory := rfl
  activeWords := rfl
  running := rfl
  amsterdam := rfl
  notPrecompile := by
    simp [MlDsa65.Amsterdam.initialState, Interface.Amsterdam.initialState, Interface.initialState]; decide
  calldataFits := hfit

/-- **Correctness with the public gas schedule.** -/
theorem opt_correctWithSchedule :
    MlDsa65.Amsterdam.CorrectWithSchedule optBytecode Gas.schedule := by
  intro cd hfit gas hgas
  obtain ⟨t, steps, hhalt, hret, -, hloc⟩ :=
    opt_correctInAnyContextWithSchedule _ (initialState_frameEntry cd hfit gas) hgas
  have hdone : t.isDone = true := by
    rw [hloc]
    simp [State.isDone, State.isHalted, State.isRunning, hhalt, MlDsa65.Amsterdam.initialState,
      Interface.Amsterdam.initialState, Interface.initialState]
  have heval := EvmProof.eval_of_steps steps hdone
  rwa [State.toResult_returned t hhalt, hret] at heval

theorem opt_correct : MlDsa65.Amsterdam.Correct optBytecode :=
  MlDsa65.Amsterdam.correct_of_schedule opt_correctWithSchedule

end MlDsaOptGlam65.Proofs
