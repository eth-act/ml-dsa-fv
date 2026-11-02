import MlDsaOptGlam65.Gas
import MlDsaOpt65.Bridge
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/Short.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Short calldata (ML-DSA-65)

`PUSH2 5261; CALLDATASIZE; LT; PUSH2 short; JUMPI` → `short: JUMPDEST; PUSH0;
PUSH0; MSTORE; PUSH1 32; PUSH0; RETURN` (instructions 0–4 and 2683–2680 of
`listing.tsv`, `RETURN` at pc 7065): the zero word, 37 gas.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Artifact
open MlDsaOptGlam65.Proofs.Infra
open MlDsa

theorem activeWordsAfter_zero (off : Nat) :
    MachineState.activeWordsAfter 0 off 32 = (off + 31) / 32 + 1 := by
  simp [MachineState.activeWordsAfter]

theorem short_block {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hlen : s.executionEnv.calldata.size < 5261) :
    runXLocatedBlock (locatedPath [0, 1, 2, 3, 4, 2538, 2539, 2540, 2541, 2542, 2543, 2544])
      (callState s 0 [] .empty) =
    some { callState s 6736 [] (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) with
      halt := .Returned
      hReturn := MachineState.readPadded
        (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) 0 32
      activeWords := UInt256.ofNat 1 } := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  glam65_block [Ctx0.code, Ctx0.running, activeWordsAfter_zero, haw]

theorem readPadded_mstore0 (M : ByteArray) (v : Nat) :
    MachineState.readPadded (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) 0) 0 32 =
      Data.Bytes.natToBytesPadded v 32 := by
  have := EvmProof.Memory.readPadded_writeBytes_same M (Data.Bytes.natToBytesPadded v 32) 0
  rwa [natToBytesPadded_size] at this

theorem spec_eq (cd : ByteArray) :
    MlDsa65.spec cd =
      Data.Bytes.natToBytesPadded (if MlDsa65.accepts cd = true then 1 else 0) 32 := by
  show Interface.spec _ cd =
    Data.Bytes.natToBytesPadded (if Interface.accepts MlDsa65.params cd = true then 1 else 0) 32
  unfold Interface.spec
  cases Interface.accepts MlDsa65.params cd <;> decide +kernel

theorem hdr_eq : Fips204.pkLen MlDsa65.params + Fips204.sigLen MlDsa65.params = 5261 := by
  have h1 := pkLen_eq
  have h2 := sigLen_eq
  unfold MlDsa65.pkLen at h1
  unfold MlDsa65.sigLen at h2
  rw [h1, h2]

theorem short_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hpc : callState s₀ 0 [] .empty = s₀)
    (hlen : s₀.executionEnv.calldata.size < 5261) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s₀ final,
      g.cost ≤ Gas.short ∧ final.halt = .Returned ∧
        final.hReturn = MlDsa65.spec s₀.executionEnv.calldata ∧ FrameLocal s₀ final := by
  have hrun := short_block h0 haw hlen
  obtain ⟨g, hg⟩ := (reach_block_pot (h0.callState 0 [] .empty) _ (cost := 34) (by decide +kernel)
    hrun).of_eq hpc rfl
  refine ⟨_, g, ?_, rfl, ?_, rfl⟩
  · refine hg.trans (le_of_eq ?_)
    change 34 + MachineState.memCost 1 - MachineState.memCost s₀.activeWords.toNat = 37
    rw [haw]; rfl
  · have hacc : MlDsa65.accepts s₀.executionEnv.calldata = false := by
      show Interface.accepts _ _ = false
      unfold Interface.accepts
      rw [hdr_eq, decide_eq_false (by omega), Bool.false_and]
    change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hacc]
    rfl

end MlDsaOptGlam65.Proofs
