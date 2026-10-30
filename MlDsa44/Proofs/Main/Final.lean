import MlDsa44.Proofs.Main.Rows
set_option warningAsError true
/-!
# Loop exit, the commitment hash and the returned word

The four row iterations, `shake256(μ ‖ w1Encode(w1))` squeezed into `XOF`,
`ok &= eq(mload(XOF), calldataload(1312))`, `mstore(0, ok)`, `return(0, 32)`.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact
open MlDsa44.Proofs.Infra

/-- All four rows of `Â` succeed. -/
def fAllOf (cd : ByteArray) (ok : Bool) : Bool :=
  (((ok && fAOf cd 0) && fAOf cd 1) && fAOf cd 2) && fAOf cd 3

theorem rows_phase {s : State} (hs : Ctx s) {mlen : Nat}
    (hmlen : mlen + 3732 = s.executionEnv.calldata.size) (ok : Bool)
    {M : ByteArray} {cH : Fips204.Poly} (hI : Inv s.executionEnv.calldata M cH) :
    ∃ M', Inv s.executionEnv.calldata M' cH ∧ RowsDone s.executionEnv.calldata M' cH 4 ∧
      Reach (callState s 5200 [wd 0, flag ok, wd mlen] M)
        (callState s 5200 [wd 4, flag (fAllOf s.executionEnv.calldata ok), wd mlen] M')
        (4 * rowCost) := by
  have hD0 : RowsDone s.executionEnv.calldata M cH 0 := fun j hj => absurd hj (Nat.not_lt_zero _)
  obtain ⟨M1, hI1, hD1, hR1⟩ := row_step hs hmlen (i := 0) (by norm_num) ok hI hD0
  obtain ⟨M2, hI2, hD2, hR2⟩ := row_step hs hmlen (i := 1) (by norm_num) _ hI1 hD1
  obtain ⟨M3, hI3, hD3, hR3⟩ := row_step hs hmlen (i := 2) (by norm_num) _ hI2 hD2
  obtain ⟨M4, hI4, hD4, hR4⟩ := row_step hs hmlen (i := 3) (by norm_num) _ hI3 hD3
  refine ⟨M4, hI4, hD4, ?_⟩
  have h := ((hR1.trans hR2).trans hR3).trans hR4
  exact h.mono (le_of_eq (by omega))

theorem exit_block {s : State} (hs : Ctx s) (mlen : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5200 [wd 4, flag a, wd mlen] M)
      (callState s 2680 [wd 136, wd W1, wd 832, wd XOF, wd 1, wd 5267, flag a, wd mlen] M) 58 := by
  evm_reach [3320, 3321, 3322, 3323, 3324, 3325, 3326, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357,
    3358] with [flag, W1, XOF]

theorem ite_land_decide (a : Bool) (p : Prop) [Decidable p] :
    ((if a = true then 1 else 0) &&& (if p then 1 else 0) : Nat) =
      if (a && decide p) = true then 1 else 0 := by
  cases a <;> by_cases hp : p <;> simp [hp]

/-- The halted state after `mstore(0, ok); return(0, 32)`. -/
def finalState (s : State) (mlen : Nat) (M : ByteArray) (v : Nat) : State :=
  { callState s 5288 [wd v, wd mlen]
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) 0) with
    halt := .Returned
    hReturn := MachineState.readPadded
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) 0) 0 32 }

theorem ite01_mod (c : Prop) [Decidable c] {n : Nat} (h : 2 ≤ n) :
    (if c then 1 else 0) % n = if c then 1 else 0 := by
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.zero_mod n

theorem final_run {s : State} (hs : Ctx s) (mlen : Nat) (a : Bool) (M : ByteArray) :
    runLocatedBlock (locatedPath [3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369,
      3370, 3371, 3372, 3373, 3374]) (callState s 5267 [flag a, wd mlen] M) =
    some (finalState s mlen M
      (if (a && decide (word M XOF = word s.executionEnv.calldata 1312)) = true then 1 else 0)) := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  unfold finalState
  evm_block [flag, ite_land_decide, XOF, ite01_mod]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem final_block {s : State} (hs : Ctx s) (mlen : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5267 [flag a, wd mlen] M)
      (finalState s mlen M
        (if (a && decide (word M XOF = word s.executionEnv.calldata 1312)) = true then 1 else 0)) 40 := by
  have h := reach_block_pot (cost := 40) ((Ctx.ctx0 hs).callState 5267 [flag a, wd mlen] M) _ (by decide +kernel)
    (final_run hs mlen a M)
  refine h.mono (le_of_eq ?_)
  change 40 + MachineState.memCost s.activeWords.toNat - MachineState.memCost s.activeWords.toNat = 40
  omega

end MlDsa44.Proofs.Main
