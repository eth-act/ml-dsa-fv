import MlDsaOptGlam44.Fn.Blk.Defs
import MlDsaOpt44.Fn.Blk.Proof
set_option warningAsError true
/-!
# Glam `blk`: what one unrolled iteration does to memory

`GInv m abp flp j0 N n M`: after the iterations `j0 … n − 1` of a run over
`[j0, N)`, memory differs from `m` only in the candidate words
`[256 j0 + abp, 256 N + abp)` and the flag words `[32 j0 + flp, 32 N + flp)`,
and those written so far hold v4's candidate and flag words of the `KS4` state
of `m`. `rnd` turns one iteration's block lemma (`Blk/Iters.lean`) into a step
of `GInv`. The candidate and flag algebra is v4's (`MlDsaOpt44/Fn/Blk/Proof.lean`).
-/

namespace MlDsaOptGlam44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Blk

/-- Placement of a run over the iterations `[j0, N)`. -/
structure GGeo (abp flp j0 N : Nat) : Prop where
  hN : N ≤ 7
  ha : 800 ≤ 256 * j0 + abp
  ha' : 256 * N + abp ≤ 16777216
  hf : 800 ≤ 32 * j0 + flp
  hf' : 32 * N + flp ≤ 16777216
  hd : 256 * N + abp ≤ 32 * j0 + flp ∨ 32 * N + flp ≤ 256 * j0 + abp

/-- Memory after the iterations `j0 … n − 1`. -/
def GInv (m : ByteArray) (abp flp j0 N n : Nat) (M : ByteArray) : Prop :=
  FrameExcept m M [(256 * j0 + abp, 256 * N + abp), (32 * j0 + flp, 32 * N + flp)] ∧
    ∀ S, KS4 m S →
      (∀ i, 8 * j0 ≤ i → i < 8 * n → word M (abp + 32 * i) = pack4 fun k => cand (S k) i) ∧
      (∀ g, j0 ≤ g → g < n → word M (flp + 32 * g) = flagWord S g)

theorem GInv.start (m : ByteArray) (abp flp j0 N : Nat) : GInv m abp flp j0 N j0 m :=
  ⟨FrameExcept.refl _ _, fun _ _ => ⟨fun _ h1 h2 => absurd h2 (by omega),
    fun _ h1 h2 => absurd h2 (by omega)⟩⟩

theorem ldw_frame {m M : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m M rs)
    {x : Nat} (ha : Avoids rs (32 * x) (32 * x + 32)) : ldw M x = ldw m x := by
  unfold ldw; rw [h.word ha]

/-- One iteration: the block lemma's memory satisfies the next `GInv`. -/
theorem rnd {s : State} {pa pb c : Nat} {tl : List UInt256} {m M : ByteArray} {abp flp j0 N : Nat}
    {l0 l1 l2 o fo : Nat} (it : Nat)
    (hR : Reach (callState s pa tl M) (callState s pb tl
      (MachineState.writeBytes
        (cmemO M abp o (unz U0 U1 U2 U3 U4 U5 l0) (unz U0 U1 U2 U3 U4 U5 l1) (unz U0 U1 U2 U3 U4 U5 l2))
        (Data.Bytes.natToBytesPadded (lfv (unz U0 U1 U2 U3 U4 U5 l0) (unz U0 U1 U2 U3 U4 U5 l1)
          (unz U0 U1 U2 U3 U4 U5 l2) % 2 ^ 256) 32) (fo + flp))) c)
    (hg : GGeo abp flp j0 N) (hit : j0 ≤ it) (hit' : it < N) (hI : GInv m abp flp j0 N it M)
    (e0 : l0 = ldw M (3 * it)) (e1 : l1 = ldw M (3 * it + 1)) (e2 : l2 = ldw M (3 * it + 2))
    (ho : o = 256 * it) (hfo : fo = 32 * it) :
    ∃ M', GInv m abp flp j0 N (it + 1) M' ∧ Reach (callState s pa tl M) (callState s pb tl M') c := by
  obtain ⟨hN, ha, ha', hf, hf', hdj⟩ := hg
  subst ho hfo
  rw [cmemO_eq] at hR
  refine ⟨_, ⟨?_, ?_⟩, hR⟩
  · refine ((hI.1.trans (frame_candMem _ _ _ _ _)).trans (FrameExcept.mstore _ _ _)).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., le_rfl, le_rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), le_rfl, le_rfl⟩
    · exact ⟨_, List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega,
        by simp only; omega⟩
  · intro S hKS
    obtain ⟨hcand, hflag⟩ := hI.2 S hKS
    have hD : ∀ w, w < 3 → ldw M (3 * it + w) = il (ln S it w) := by
      intro w hw
      rw [ldw_frame hI.1 (by simp only [avoids_cons, avoids_nil, and_true]; omega),
        ldw_lane hKS (by omega)]
      rfl
    have hD0 : unz U0 U1 U2 U3 U4 U5 l0 = pack4 (ln S it 0) := by
      rw [e0, show 3 * it = 3 * it + 0 by rfl, hD 0 (by omega), unz_il (ln_lt S _ 0)]
    have hD1 : unz U0 U1 U2 U3 U4 U5 l1 = pack4 (ln S it 1) := by
      rw [e1, hD 1 (by omega), unz_il (ln_lt S _ 1)]
    have hD2 : unz U0 U1 U2 U3 U4 U5 l2 = pack4 (ln S it 2) := by
      rw [e2, hD 2 (by omega), unz_il (ln_lt S _ 2)]
    rw [hD0, hD1, hD2]
    refine ⟨fun i hi1 hi => ?_, fun g hg1 hg => ?_⟩
    · rw [word_wb _ _ (by omega), if_neg (by omega)]
      by_cases hij : i < 8 * it
      · rw [word_candMem_disjoint _ _ _ _ _ (by omega)]
        exact hcand i hi1 hij
      · obtain ⟨k, rfl⟩ : ∃ k, i = 8 * it + k := ⟨i - 8 * it, by omega⟩
        rw [show abp + 32 * (8 * it + k) = 256 * it + abp + 32 * k by ring,
          word_candMem _ _ _ _ _ (by omega), cw_cand S it (by omega)]
    · by_cases hgn : g < it
      · rw [word_wb _ _ (by omega), if_neg (by omega),
          word_candMem_disjoint _ _ _ _ _ (by omega)]
        exact hflag g hg1 hgn
      · obtain rfl : g = it := by omega
        rw [word_wb _ _ (by omega), if_pos (by ring)]
        exact lfv_flag S g

end MlDsaOptGlam44.Proofs.Blk
