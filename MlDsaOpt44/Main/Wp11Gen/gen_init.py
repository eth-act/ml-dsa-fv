rows=[l.rstrip('\n').split('\t') for l in open('MlDsaOpt44/listing.tsv')][1:]
pc=lambda i:int(rows[i][1])
rc4=open('MlDsaOpt44/Main/Wp11Gen/rc4.txt').read(); rc1=open('MlDsaOpt44/Main/Wp11Gen/rc1.txt').read()
L=lambda a,b:', '.join(str(i) for i in range(a,b))
src=f'''import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Bswap
set_option warningAsError true
/-! # Segment `0 … 992`: size check, memory sizing, the `RC4`/`RC1` iota tables (straight line). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The `RC4` words as pushed by the code. -/
def rc4v (i : Nat) : Nat := [{rc4}].getD i 0

/-- The `RC1` words (`RC[i] · REP`, folded). -/
def rc1v (i : Nat) : Nat := [{rc1}].getD i 0

theorem rc4v_eq : ∀ i, i < 24 →
    rc4v i = il fun _ => (EvmSemantics.Crypto.Keccak.RC[i]!).toNat := by decide +kernel

theorem rc1v_eq : ∀ i, i < 24 → rc1v i = rep (EvmSemantics.Crypto.Keccak.RC[i]!).toNat := by
  decide +kernel

theorem rcv_lt : ∀ i, i < 24 → rc4v i < 2 ^ 256 ∧ rc1v i < 2 ^ 256 := by decide +kernel

/-- Memory after the sizing store. -/
@[irreducible] def initM0 : ByteArray := MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 66048

/-- Memory at `992`. -/
@[irreducible] def initMem : ByteArray := storeWords (storeWords initM0 RC4 rc4v 24) RC1 rc1v 24

theorem init_run {{s : State}} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    EvmProof.Stepper.runLocatedBlock (Artifact.locatedPath [{L(0,8)}]) (callState s 0 [] .empty) =
      some (callState (sized s) 15 [] initM0) := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  simp only [sized, memWords, initM0]
  opt44_block [Ctx0.code, Ctx0.running, haw, MachineState.activeWordsAfter]
  rfl

theorem init_rc4 {{s : State}} (hs : Ctx s) (M : ByteArray) :
    Reach (callState s 15 [] M) (callState s 664 [] (storeWords M RC4 rc4v 24)) 216 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2065 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [{L(8,80)}]
  rfl

theorem init_rc1a {{s : State}} (hs : Ctx s) (M : ByteArray) :
    Reach (callState s 664 [] M) (callState s {pc(141)} [wd {int(rows[80][2].split()[1],16)}] (storeWords M RC1 rc1v 12)) 207 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2065 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [{L(80,141)}]
  rfl

theorem init_rc1b {{s : State}} (hs : Ctx s) (M : ByteArray) :
    Reach (callState s {pc(141)} [wd {int(rows[80][2].split()[1],16)}] (storeWords M RC1 rc1v 12))
      (callState s 992 [] (storeWords M RC1 rc1v 24)) 206 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2065 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [{L(141,202)}]
  rfl

theorem initMem_frame : FrameExcept initM0 initMem [(RC4, RC4 + 768), (RC1, RC1 + 768)] := by
  unfold initMem
  exact (FrameExcept.storeWords initM0 RC4 rc4v 24).trans (FrameExcept.storeWords _ RC1 rc1v 24)

theorem sized_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState (sized s) pc stk m).activeWords.toNat = memWords := sized_activeWords s

theorem callState_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState s pc stk m).activeWords = s.activeWords := rfl

theorem byteAt_ntb0 {{k : Nat}} (hk : k < 32) : byteAt (Data.Bytes.natToBytesPadded 0 32) k = 0 := by
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

theorem inv0_initMem : Inv0 initMem where
  rc4 := fun i hi => by
    unfold initMem
    rw [FrameExcept.word (FrameExcept.storeWords _ RC1 rc1v 24) (by avoids_tac),
      word_storeWords (rcv_lt i hi).1 24 hi, rc4v_eq i hi]
  rc1 := fun i hi => by
    unfold initMem
    rw [word_storeWords (rcv_lt i hi).2 24 hi, rc1v_eq i hi]
  zero := initM0_zero.frame initMem_frame (by avoids_tac)

/-- `0 … 992` from the frame entry (memory empty, not yet sized). -/
theorem seg_init_proof {{s : State}} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    ∃ m, Inv0 m ∧
      Reach (callState s 0 [] .empty) (callState (sized s) 992 [] m)
        (Gas.pInit + MachineState.memCost memWords) := by
  have hs : Ctx (sized s) := sized_ctx h0 hfit
  have hA := reach_block_pot (h0.callState 0 [] .empty) [{L(0,8)}] (cost := 29)
    (by decide +kernel) (init_run h0 haw hcd hfit)
  have hm1 := sized_aw s 15 [] initM0
  have hm0 := (congrArg UInt256.toNat (callState_aw s 0 [] .empty)).trans haw
  rw [hm1, hm0] at hA
  refine ⟨initMem, inv0_initMem, ?_⟩
  rw [show initMem = storeWords (storeWords initM0 RC4 rc4v 24) RC1 rc1v 24 by unfold initMem; rfl]
  have h := ((hA.trans (init_rc4 hs _)).trans (init_rc1a hs _)).trans (init_rc1b hs _)
  refine h.mono ?_
  have : MachineState.memCost 0 = 0 := rfl
  unfold Gas.pInit
  omega

end MlDsaOpt44.Proofs
'''
import re
costs={'cA':None}
open('MlDsaOpt44/Main/Init/Blocks.lean','w').write(src)
