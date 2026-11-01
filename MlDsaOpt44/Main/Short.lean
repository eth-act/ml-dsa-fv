import MlDsaOpt44.Gas
import MlDsaOpt44.Bridge
set_option warningAsError true
/-!
# Short calldata

`PUSH2 3732; CALLDATASIZE; LT; PUSH2 short; JUMPI` → `short: JUMPDEST; PUSH0;
PUSH0; MSTORE; PUSH1 32; PUSH0; RETURN`: the zero word, 37 gas.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Artifact
open MlDsaOpt44.Proofs.Infra
open MlDsa44

theorem activeWordsAfter_zero (off : Nat) :
    MachineState.activeWordsAfter 0 off 32 = (off + 31) / 32 + 1 := by
  simp [MachineState.activeWordsAfter]

theorem short_block {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hlen : s.executionEnv.calldata.size < 3732) :
    runLocatedBlock (locatedPath [0, 1, 2, 3, 4, 2377, 2378, 2379, 2380, 2381, 2382, 2383])
      (callState s 0 [] .empty) =
    some { callState s 6704 [] (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) with
      halt := .Returned
      hReturn := MachineState.readPadded
        (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) 0 32
      activeWords := UInt256.ofNat 1 } := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  opt44_block [Ctx0.code, Ctx0.running, activeWordsAfter_zero, haw]

theorem readPadded_mstore0 (M : ByteArray) (v : Nat) :
    MachineState.readPadded (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) 0) 0 32 =
      Data.Bytes.natToBytesPadded v 32 := by
  have := EvmProof.Memory.readPadded_writeBytes_same M (Data.Bytes.natToBytesPadded v 32) 0
  rwa [natToBytesPadded_size] at this

theorem spec_eq (cd : ByteArray) :
    spec cd = Data.Bytes.natToBytesPadded (if accepts cd = true then 1 else 0) 32 := by
  unfold spec
  cases accepts cd <;> decide +kernel

theorem short_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hpc : callState s₀ 0 [] .empty = s₀)
    (hlen : s₀.executionEnv.calldata.size < 3732) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s₀ final,
      g.cost ≤ Gas.short ∧ final.halt = .Returned ∧
        final.hReturn = spec s₀.executionEnv.calldata ∧ FrameLocal s₀ final := by
  have hrun := short_block h0 haw hlen
  obtain ⟨g, hg⟩ := (reach_block_pot (h0.callState 0 [] .empty) _ (cost := 34) (by decide +kernel)
    hrun).of_eq hpc rfl
  refine ⟨_, g, ?_, rfl, ?_, rfl⟩
  · refine hg.trans (le_of_eq ?_)
    change 34 + MachineState.memCost 1 - MachineState.memCost s₀.activeWords.toNat = 37
    rw [haw]; rfl
  · have hacc : accepts s₀.executionEnv.calldata = false := by
      unfold accepts
      rw [pkLen_eq, sigLen_eq, decide_eq_false (by omega), Bool.false_and]
    change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hacc]
    rfl

end MlDsaOpt44.Proofs
