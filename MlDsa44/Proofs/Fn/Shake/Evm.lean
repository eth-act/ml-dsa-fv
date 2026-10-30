import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# EVM helpers for `shake`

* `reach_mcopy`: the `MCOPY` at instruction 1773 (pc 2806), whose cost depends
  on the copy length (so `evm_reach` refuses it);
* `byte0_word`: `BYTE 0` of an `MLOAD` is the addressed byte;
* `byteAt_storeWords_zero`: bytes after a run of zero-word stores.
-/

namespace MlDsa44.Proofs.Shake

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact

theorem reach_mcopy {s : State} (hs : Ctx s) {dst src sz : Nat} {rest : List UInt256}
    {m : ByteArray} (hrest : rest.length ≤ 1000)
    (hdst : dst + sz ≤ 32 * s.activeWords.toNat) (hsrc : src + sz ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 2806 (wd dst :: wd src :: wd sz :: rest) m)
      (callState s 2807 rest (MachineState.writeBytes m (MachineState.readPadded m src sz) dst))
      (3 + 3 * ((sz + 31) / 32)) := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hrun : runLocatedBlock (locatedPath [1773]) (callState s 2806 (wd dst :: wd src :: wd sz :: rest) m) =
      some (callState s 2807 rest (MachineState.writeBytes m (MachineState.readPadded m src sz) dst)) := by
    evm_block [EvmSemantics.EVM.State.activeWordsAfterUInt256_2]
  have hcode : (callState s 2806 (wd dst :: wd src :: wd sz :: rest) m).executionEnv.code =
      referenceArtifact.code := hs.code
  have hfork : (callState s 2806 (wd dst :: wd src :: wd sz :: rest) m).fork = .Osaka := hs.fork
  have hrunning : (callState s 2806 (wd dst :: wd src :: wd sz :: rest) m).halt = .Running :=
    hs.running
  have hnp := hs.notPrecompile
  let g := runLocatedBlock_sound referenceArtifact .Osaka (locatedPath [1773]) hcode hfork hrun
    hrunning hnp
  refine ⟨g, le_of_eq ?_⟩
  have hpot := EvmProof.Meter.runLocatedBlock_cost_potential (locatedPath [1773]) hrun
  change runLocatedBlockCost (locatedPath [1773]) (callState s 2806 _ m) = _
  change _ + MachineState.memCost s.activeWords.toNat =
    _ + MachineState.memCost s.activeWords.toNat at hpot
  have hw : EvmProof.Meter.runLocatedBlockCostWithoutMemory (locatedPath [1773])
      (callState s 2806 (wd dst :: wd src :: wd sz :: rest) m) = 3 + 3 * ((sz + 31) / 32) := by
    simp only [EvmProof.Meter.runLocatedBlockCostWithoutMemory, locatedPath, List.map_cons,
      List.map_nil, Infra.located_instruction_eq, Infra.instrAt_lit, Infra.finVal_lit,
      EvmProof.Meter.instrCostWithoutMemory, callState, Gas.copyWordCost, wd,
      Nat.add_zero]
    rw [Infra.toNat_ofNat_of_lt (by omega)]
    rfl
  omega

/-! ## Bytes of words -/

theorem beNat_succ (m : ByteArray) : ∀ (a w : Nat),
    Infra.beNat m a (w + 1) = byteAt m a * 256 ^ w + Infra.beNat m (a + 1) w
  | a, 0 => by simp [Infra.beNat]
  | a, w + 1 => by
    rw [Infra.beNat, beNat_succ m a w, Infra.beNat, show a + (w + 1) = a + 1 + w by omega,
      pow_succ]
    ring

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ w, Infra.beNat m a w < 256 ^ w
  | 0 => by simp [Infra.beNat]
  | w + 1 => by
    have h1 := beNat_lt m a w
    have h2 := Infra.byteAt_lt m (a + w)
    rw [Infra.beNat, pow_succ]
    have h3 : (Infra.beNat m a w + 1) * 256 ≤ 256 ^ w * 256 := Nat.mul_le_mul_right _ h1
    omega

theorem byte0_word (m : ByteArray) (a : Nat) :
    UInt256.byteAt (UInt256.ofNat 0) (UInt256.ofNat (word m a)) = UInt256.ofNat (byteAt m a) := by
  unfold UInt256.byteAt
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  rw [h0, if_neg (by omega), EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (Infra.word_lt m a),
    Infra.word_eq_beNat, beNat_succ, Nat.shiftRight_eq_div_pow]
  have hb := Infra.byteAt_lt m a
  have hr := beNat_lt m (a + 1) 31
  have : (byteAt m a * 256 ^ 31 + Infra.beNat m (a + 1) 31) / 2 ^ (8 * (31 - 0)) = byteAt m a := by
    rw [show (2 : Nat) ^ (8 * (31 - 0)) = 256 ^ 31 by norm_num, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [this, show (0xff : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega)]

theorem byteAt_zeroWord (m : ByteArray) (a b : Nat) :
    byteAt (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) a) b =
      if a ≤ b ∧ b < a + 32 then 0 else byteAt m b := by
  rw [Infra.byteAt_writeBytes, Infra.natToBytesPadded_size]
  split
  · rw [Infra.byteAt_eq_getD, YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _
      (by omega)]
    simp
  · rfl

theorem byteAt_storeWords_zero (m : ByteArray) (base : Nat) :
    ∀ n a, byteAt (Infra.storeWords m base (fun _ => 0) n) a =
      if base ≤ a ∧ a < base + 32 * n then 0 else byteAt m a
  | 0, a => by simp only [Infra.storeWords_zero]; rw [if_neg (by omega)]
  | n + 1, a => by
    rw [Infra.storeWords_succ, byteAt_zeroWord, byteAt_storeWords_zero m base n a]
    split_ifs <;> first | rfl | omega

/-- A single-byte write (`MSTORE8`). -/
theorem byteAt_write1 (m : ByteArray) (x : UInt8) (a b : Nat) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[x]) a) b =
      if b = a then x.toNat else byteAt m b := by
  rw [Infra.byteAt_writeBytes]
  have hs : (ByteArray.mk #[x]).size = 1 := rfl
  rw [hs]
  by_cases h : b = a
  · subst h
    rw [if_pos (by omega), if_pos rfl, Nat.sub_self]
    unfold byteAt; rw [dif_pos (by rw [hs]; omega)]; rfl
  · rw [if_neg (by omega), if_neg h]

/-- Weaken a frame by pointwise range reasoning. -/
theorem frame_cover {m m' : ByteArray} {rs rs' : List (Nat × Nat)} (h : FrameExcept m m' rs)
    (hc : ∀ a, (∀ r ∈ rs', a < r.1 ∨ r.2 ≤ a) → ∀ r ∈ rs, a < r.1 ∨ r.2 ≤ a) :
    FrameExcept m m' rs' := fun a ha => h a (hc a ha)


/-- Close a `frame_cover` side goal: unfold the range lists and use `omega`. -/
macro "frame_omega" : tactic => `(tactic| (
  intro a ha
  simp only [List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, MlDsa44.Proofs.ST, MlDsa44.Proofs.RC,
    MlDsa44.Proofs.PADB] at ha ⊢
  omega))
end MlDsa44.Proofs.Shake
