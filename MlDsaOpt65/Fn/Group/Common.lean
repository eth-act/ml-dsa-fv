import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Common.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
/-!
# Helpers for the `pass3*` accumulation loops (WP6)

The loops write `ACC[t]` for `t = 0, 1, …` in order, so the memory after `n`
stores is `storeWords m ACC v n` for the contract's value function `v`.
-/

namespace MlDsaOpt65.Proofs.GroupP

open MlDsaOpt44.Proofs  -- port: 44 `GroupP` is not imported

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

theorem land_m64 (x : Nat) : x &&& 18446744073709551615 = x % 18446744073709551616 :=
  Nat.and_two_pow_sub_one_eq_mod x 64

theorem land_m64' (x : Nat) : 18446744073709551615 &&& x = x % 18446744073709551616 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64

/-- The returning `JUMP` of a subroutine (proved without `opt65_block`, whose
simp set reduces `isValidJumpDest optBytecode ret` far too deeply for a
symbolic `ret`). -/
theorem reach_ret {s : State} (hs : Ctx s) (i : Fin 11461) {pc ret : Nat}  -- port: instruction count
    {tail : List UInt256} (M : ByteArray)
    (hok : MlDsaOpt65.Proofs.Infra.blockOK [i] 8 = true)
    (hi : MlDsaOpt65.Proofs.Infra.instrAt i.val = .op (.StackMemFlow .JUMP))
    (hpc : MlDsaOpt65.Proofs.Infra.pcAt i.val = pc) (hpc' : pc < 2 ^ 256)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (htail : tail.length ≤ 1000) :
    Reach (callState s pc (wd ret :: tail) M) (callState s ret tail M) 8 := by
  refine MlDsaOpt65.Proofs.Infra.reach_block hs [i] hok ?_
  have hpcw : (UInt256.ofNat pc).toNat = pc := toNat_ofNat_of_lt hpc'
  have hr' : ret % 2 ^ 256 = ret := Nat.mod_eq_of_lt (by omega)
  simp only [MlDsaOpt65.Proofs.Artifact.locatedPath, List.map_cons, List.map_nil,
    EvmProof.Stepper.runLocatedBlock]
  rw [show EvmProof.Stepper.runLocated (MlDsaOpt65.Proofs.Artifact.located i)
      (callState s pc (wd ret :: tail) M) =
      MlDsaOpt65.Proofs.Infra.stepL (some (callState s pc (wd ret :: tail) M))
        (MlDsaOpt65.Proofs.Artifact.located i) by
    rw [MlDsaOpt65.Proofs.Infra.stepL_some,
      MlDsaOpt65.Proofs.Infra.runIfRunning_of (s := callState s pc (wd ret :: tail) M) _ hs.running]]
  rw [MlDsaOpt65.Proofs.Infra.stepL_located, hi, hpc]
  simp only [callState, hs.running, MlDsaOpt65.Proofs.Infra.guardHalt_running, hpcw, if_true,
    EvmProof.Stepper.runInstr, wd, EvmProof.Word.word_toNat_ofNat, hs.code, hr', hj, List.length_cons]
  rw [if_pos (by omega)]

/-- Words outside the stored prefix are untouched. -/
theorem word_storeWords_out {m : ByteArray} {base : Nat} {v : Nat → Nat} {n a : Nat}
    (h : a + 32 ≤ base ∨ base + 32 * n ≤ a) : word (storeWords m base v n) a = word m a :=
  FrameExcept.word (FrameExcept.storeWords m base v n) (by
    simp only [Avoids, List.mem_singleton, forall_eq]; exact h)

/-- One more store at the next slot. -/
theorem storeWords_next {m : ByteArray} {base : Nat} {v : Nat → Nat} {n n' addr x : Nat}
    (hn' : n' = n + 1) (haddr : addr = base + 32 * n) (hx : x = v n) :
    MachineState.writeBytes (storeWords m base v n) (Data.Bytes.natToBytesPadded x 32) addr =
      storeWords m base v n' := by
  rw [hn', storeWords_succ, haddr, hx, Nat.mul_comm n 32]

end MlDsaOpt65.Proofs.GroupP
