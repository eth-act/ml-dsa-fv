import MlDsaOpt87.Gas
import MlDsaOpt87.Bridge
set_option warningAsError true
/-!
# Short calldata (ML-DSA-87)

`PUSH2 7219; CALLDATASIZE; LT; PUSH2 short; JUMPI` → `short: JUMPDEST; PUSH0;
PUSH0; MSTORE; PUSH1 32; PUSH0; RETURN` (pcs 7480 … 7487, instruction indices
2611 … 2617): the zero word, 37 gas.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Artifact
open MlDsaOpt87.Proofs.Infra
open MlDsa87

theorem activeWordsAfter_zero (off : Nat) :
    MachineState.activeWordsAfter 0 off 32 = (off + 31) / 32 + 1 := by
  simp [MachineState.activeWordsAfter]

theorem short_block {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hlen : s.executionEnv.calldata.size < 7219) :
    runLocatedBlock (locatedPath [0, 1, 2, 3, 4, 2611, 2612, 2613, 2614, 2615, 2616, 2617])
      (callState s 0 [] .empty) =
    some { callState s 7487 [] (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) with
      halt := .Returned
      hReturn := MachineState.readPadded
        (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) 0 32
      activeWords := UInt256.ofNat 1 } := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  opt87_block [Ctx0.code, Ctx0.running, activeWordsAfter_zero, haw]

theorem readPadded_mstore0 (M : ByteArray) (v : Nat) :
    MachineState.readPadded (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) 0) 0 32 =
      Data.Bytes.natToBytesPadded v 32 := by
  have := EvmProof.Memory.readPadded_writeBytes_same M (Data.Bytes.natToBytesPadded v 32) 0
  rwa [natToBytesPadded_size] at this

theorem spec_eq (cd : ByteArray) :
    spec cd = Data.Bytes.natToBytesPadded (if accepts cd = true then 1 else 0) 32 := by
  unfold spec MlDsa.Interface.spec accepts
  cases MlDsa.Interface.accepts params cd <;> decide +kernel

theorem short_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hpc : callState s₀ 0 [] .empty = s₀)
    (hlen : s₀.executionEnv.calldata.size < 7219) :
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
      unfold accepts MlDsa.Interface.accepts
      rw [show MlDsa.Fips204.pkLen params + MlDsa.Fips204.sigLen params = 7219 by
        change MlDsa87.pkLen + MlDsa87.sigLen = 7219; rw [pkLen_eq, sigLen_eq],
        decide_eq_false (by omega), Bool.false_and]
    change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hacc]
    rfl

end MlDsaOpt87.Proofs
