import MlDsa44.Proofs.Main.Result
import MlDsa44.Proofs.Gas
set_option warningAsError true
/-!
# The two whole-program traces

`short_trace`: calldata shorter than `pk ‖ σ` returns the zero word.
`valid_trace`: the full verification path, composed from the phases.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact
open MlDsa44.Proofs.Infra

theorem initial_activeWords (cd : ByteArray) :
    (initialState referenceBytecode cd 0).activeWords.toNat = 0 := rfl

theorem spec_eq (cd : ByteArray) :
    spec cd = Data.Bytes.natToBytesPadded (if accepts cd = true then 1 else 0) 32 := by
  unfold spec
  cases accepts cd <;> decide +kernel

theorem readPadded_mstore0 (M : ByteArray) (v : Nat) :
    MachineState.readPadded (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) 0) 0 32 =
      Data.Bytes.natToBytesPadded v 32 := by
  have := EvmProof.Memory.readPadded_writeBytes_same M (Data.Bytes.natToBytesPadded v 32) 0
  rwa [natToBytesPadded_size] at this

theorem short_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hcs : s₀.callStack = []) (hpc : callState s₀ 0 [] .empty = s₀)
    (hlen : s₀.executionEnv.calldata.size < 3732) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s₀ final,
      g.cost ≤ Gas.short ∧ final.isDone = true ∧
        final.toResult = .returned (spec s₀.executionEnv.calldata) := by
  have hrun := short_block h0 haw hlen
  obtain ⟨g, hg⟩ := (reach_block_pot (h0.callState 0 [] .empty) _ (cost := 264) (by decide +kernel)
    hrun).of_eq hpc rfl
  refine ⟨_, g, ?_, ?_, ?_⟩
  · refine hg.trans (le_of_eq ?_)
    change 264 + MachineState.memCost 1 - MachineState.memCost s₀.activeWords.toNat = 267
    rw [haw]; rfl
  · simp [State.isDone, State.isHalted, State.isRunning, callState, hcs]
  · have hacc : accepts s₀.executionEnv.calldata = false := by
      unfold accepts
      rw [pkLen_eq, sigLen_eq, decide_eq_false (by omega), Bool.false_and]
    change ExecutionResult.returned (MachineState.readPadded _ 0 32) = _
    rw [readPadded_mstore0, spec_eq, hacc]
    rfl

/-- The total cost of the valid path. -/
theorem valid_cost (mlen : Nat) (hml : mlen < 2 ^ 64) :
    281 + MachineState.memCost (sizedWords mlen) - MachineState.memCost 0 +
        hashCost mlen + sigCost + 4 * rowCost + 58 + Gas.shake 136 832 1 + 40 ≤
      Gas.schedule (mlen + 3732) := by
  unfold Gas.schedule
  rw [if_neg (by omega)]
  simp only [Nat.add_sub_cancel]
  have hw : (MSGIN + mlen + 288 + 31) / 32 = sizedWords mlen := by unfold sizedWords; omega
  rw [hw]
  have hm : Gas.memCost (sizedWords mlen) = MachineState.memCost (sizedWords mlen) := by
    unfold Gas.memCost MachineState.memCost; rw [Nat.pow_two]
  have h0 : MachineState.memCost 0 = 0 := rfl
  rw [hm, h0]
  clear hw hm h0
  unfold hashCost sigCost rowCost Gas.mainFixed
  omega

theorem valid_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hcs : s₀.callStack = []) (hpc : callState s₀ 0 [] .empty = s₀)
    (hfit : s₀.executionEnv.calldata.size < 2 ^ 64) (hlen : 3732 ≤ s₀.executionEnv.calldata.size) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s₀ final,
      g.cost ≤ Gas.schedule s₀.executionEnv.calldata.size ∧ final.isDone = true ∧
        final.toResult = .returned (spec s₀.executionEnv.calldata) := by
  -- size the memory
  have hrun := size_block h0 haw hlen hfit
  have hR0 := (reach_block_pot (h0.callState 0 [] .empty) _ (cost := 281) (by decide +kernel)
    hrun).of_eq hpc rfl
  generalize hcd0 : s₀.executionEnv.calldata = cd at hR0 hfit hlen ⊢
  generalize hmlen' : cd.size - 3732 = mlen at hR0
  have hml : mlen < 2 ^ 64 := by omega
  generalize hs1 : sized s₀ mlen = s₁ at hR0
  have hs : Ctx s₁ := hs1 ▸ sized_ctx h0 (hcd0 ▸ hfit) mlen hml
  have hW : MSGIN + mlen + 288 ≤ 32 * s₁.activeWords.toNat := hs1 ▸ sized_mem _ mlen hml
  have hcd : s₁.executionEnv.calldata = cd := by rw [← hs1, ← hcd0]; rfl
  have hmlen : mlen + 3732 = s₁.executionEnv.calldata.size := by rw [hcd]; omega
  -- phases
  obtain ⟨M2, hrc, hz, hmu, hR1⟩ := hash_phase hs hmlen hW _
  obtain ⟨M3, cH, hI, hc, hR2⟩ := sig_phase hs hmlen hW hrc hz hmu
  obtain ⟨M4, hI4, hD4, hR3⟩ := rows_phase hs hmlen _ hI
  have hR4 := exit_block hs mlen (fAllOf s₁.executionEnv.calldata
    ((fzOf s₁.executionEnv.calldata && fhOf s₁.executionEnv.calldata) && fcOf s₁.executionEnv.calldata)) M4
  obtain ⟨M5, hb5, -, hC5⟩ := shake_call hs
    (retOK_top (ret := 5267) (tail := [flag (fAllOf s₁.executionEnv.calldata
        ((fzOf s₁.executionEnv.calldata && fhOf s₁.executionEnv.calldata) &&
          fcOf s₁.executionEnv.calldata)), wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.shake, Stack.keccakF, Stack.xorBlock, Stack.loadLE64, Stack.storeLE64,
        Stack.bswap64, Stack.leaf]))
    (m := M4) (rate := 136) (ptr := W1) (len := 832) (out := XOF) (blocks := 1)
    (Or.inl rfl) (by norm_num) hI4.rc (by unfold ZETA W1; omega) (by unfold PADB W1; omega)
    (by unfold ZETA XOF; omega) (by unfold PADB XOF; omega) (by unfold W1 XOF; omega)
    (by unfold W1 XOF MSGIN at *; omega)
  have hR5 : Reach (callState s₁ 2680 [wd 136, wd W1, wd 832, wd XOF, wd 1, wd 5267,
        flag (fAllOf s₁.executionEnv.calldata ((fzOf s₁.executionEnv.calldata &&
          fhOf s₁.executionEnv.calldata) && fcOf s₁.executionEnv.calldata)), wd mlen] M4)
      (callState s₁ 5267 [flag (fAllOf s₁.executionEnv.calldata ((fzOf s₁.executionEnv.calldata &&
          fhOf s₁.executionEnv.calldata) && fcOf s₁.executionEnv.calldata)), wd mlen] M5)
      (Gas.shake 136 832 1) :=
    (Infra.call_iff.mp hC5).of_eq (by simp [Entry.shake]) (by simp)
  have hR6 := final_block hs mlen (fAllOf s₁.executionEnv.calldata
    ((fzOf s₁.executionEnv.calldata && fhOf s₁.executionEnv.calldata) && fcOf s₁.executionEnv.calldata)) M5
  have hx : BytesAt M5 XOF (Fips204.H (MachineState.readPadded M4 W1 832) 32) :=
    bytesAt_H hb5 (by norm_num)
  have hres := result_bool (by omega) hI4 hc hD4 hx
  -- assemble
  have h := (((((hR0.trans hR1).trans hR2).trans hR3).trans hR4).trans hR5).trans hR6
  obtain ⟨g, hg⟩ := h
  refine ⟨_, g, ?_, ?_, ?_⟩
  · refine hg.trans ?_
    simp only [callState]
    rw [← hs1, sized_activeWords _ _ hml, haw, show cd.size = mlen + 3732 by omega]
    exact valid_cost mlen hml
  · rw [← hs1]
    simp [finalState, State.isDone, State.isHalted, State.isRunning, callState, sized, hcs]
  · change ExecutionResult.returned (MachineState.readPadded _ 0 32) = _
    rw [readPadded_mstore0, spec_eq, ← hcd, ← hres]

end MlDsa44.Proofs.Main
