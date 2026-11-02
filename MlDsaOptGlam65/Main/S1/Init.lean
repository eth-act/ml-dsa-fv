import MlDsaOptGlam65.Main.Base
import MlDsaOpt44.Math.Bswap
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
set_option warningAsError true
/-! # Segment `0 … 15`: size check and memory sizing (straight line).

v4's segment `0 … 992` (`MlDsaOpt65/Main/S1/Init.lean`) without the
`RC4` / `RC1` iota tables, which this artifact does not have (iota is a `PUSH`
immediate in the unrolled kernels). -/

namespace MlDsaOptGlam65.Proofs.S1

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs (byteN_word byteN)

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

/-- Memory after the sizing store (also the memory at `15`). -/
@[irreducible] def initM0 : ByteArray :=
  MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 108256

theorem init_run {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    EvmProof.Stepper.runXLocatedBlock (Artifact.locatedPath [0, 1, 2, 3, 4, 5, 6, 7])
      (callState s 0 [] .empty) = some (callState (sized s) 15 [] initM0) := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  simp only [sized, memWords, initM0]
  glam65_block [Ctx0.code, Ctx0.running, haw, MachineState.activeWordsAfter]
  rfl

theorem sized_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState (sized s) pc stk m).activeWords.toNat = memWords := sized_activeWords s

theorem callState_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState s pc stk m).activeWords = s.activeWords := rfl

theorem byteAt_ntb0 {k : Nat} (hk : k < 32) : byteAt (Data.Bytes.natToBytesPadded 0 32) k = 0 := by
  have hw := word_mstore ByteArray.empty 0 0 (by norm_num)
  have hb := byteN_word (MachineState.writeBytes ByteArray.empty (Data.Bytes.natToBytesPadded 0 32) 0) 0
    (q := 31 - k) (by omega)
  rw [hw, byteAt_writeBytes, natToBytesPadded_size, if_pos (by omega),
    show 0 + (31 - (31 - k)) - 0 = k by omega] at hb
  rw [← hb]; unfold byteN; simp

theorem initM0_zero : ZeroOn initM0 MISC TOP := by
  intro a h1 h2
  unfold initM0
  rw [byteAt_writeBytes, natToBytesPadded_size]
  split
  · exact byteAt_ntb0 (by omega)
  · unfold byteAt; rw [dif_neg (by simp)]

theorem inv0_initM0 : Inv0 initM0 where
  rc4 := trivial
  rc1 := trivial
  zero := initM0_zero

/-- `0 … 15` from the frame entry (memory empty, not yet sized). -/
theorem seg_init_proof {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    ∃ m, Inv0 m ∧
      Reach (callState s 0 [] .empty) (callState (sized s) 15 [] m)
        (Gas.pInit + MachineState.memCost memWords) := by
  have hA := reach_block_pot (h0.callState 0 [] .empty) [0, 1, 2, 3, 4, 5, 6, 7] (cost := 29)
    (by decide +kernel) (init_run h0 haw (by unfold HDR at hcd; exact hcd) hfit)
  have hm1 := sized_aw s 15 [] initM0
  have hm0 := (congrArg UInt256.toNat (callState_aw s 0 [] .empty)).trans haw
  rw [hm1, hm0] at hA
  refine ⟨initM0, inv0_initM0, hA.mono ?_⟩
  have : MachineState.memCost 0 = 0 := rfl
  unfold Gas.pInit
  omega

end MlDsaOptGlam65.Proofs.S1
