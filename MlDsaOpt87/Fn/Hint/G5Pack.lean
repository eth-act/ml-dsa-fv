import MlDsaOpt87.Fn.Hint.G5PackBlocks
set_option warningAsError true
/-!
# `pack` (ML-DSA-87): memory of the loop, the loop and the contract body (see `G5PackBlocks`)
-/

namespace MlDsaOpt87.Proofs.G5PK

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt65.Proofs.G5H
open MlDsaOpt44.Proofs.PK (Xl)

/-! ## Memory -/

theorem wrN_word (nr : Nat) (M : ByteArray) (x : UInt256) (fp : Nat) {a : Nat}
    (h : ∀ r, r < 4 → a + 32 ≤ fp + 512 * r ∨ fp + 512 * r + 32 ≤ a) : word (wrN nr M x fp) a = word M a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold wrN; split_ifs
  · simp (disch := omega) only [wr2, word_mstore_disjoint]
  · simp (disch := omega) only [wr4, wr2, word_mstore_disjoint]

theorem wrN_byte (nr : Nat) (M : ByteArray) (x : UInt256) (fp : Nat) {a : Nat}
    (h : a < fp ∨ fp + 512 * (if nr ≤ 2 then 1 else 3) + 32 ≤ a) : byteAt (wrN nr M x fp) a = byteAt M a := by
  unfold wrN; split_ifs with hn
  · rw [if_pos hn] at h
    simp (disch := (rw [natToBytesPadded_size]; omega)) only [wr2, byteAt_writeBytes_of_not_mem]
  · rw [if_neg hn] at h
    simp (disch := (rw [natToBytesPadded_size]; omega)) only [wr4, wr2, byteAt_writeBytes_of_not_mem]

theorem wrN_hit {nr : Nat} (hnr : nr = 2 ∨ nr = 4) (M : ByteArray) (x : UInt256) (fp : Nat) {r : Nat}
    (hr : r < nr) : word (wrN nr M x fp) (fp + 512 * r) = rep (Xl x r) := by
  have hl := MlDsaOpt44.Proofs.PK.u_toNat_lt
  rcases hnr with rfl | rfl
  · unfold wrN; rw [if_pos (by omega)]
    interval_cases r
    · simp (disch := first | omega | exact hl _) only [wr2, word_mstore_disjoint, word_mstore,
        Nat.mul_zero, Nat.add_zero]
      exact pw0_eq x
    · simp (disch := first | omega | exact hl _) only [wr2, word_mstore,
        show fp + 512 * 1 = 512 + fp by omega]
      exact pw1_eq x
  · unfold wrN; rw [if_neg (by omega)]
    interval_cases r
    · simp (disch := first | omega | exact hl _) only [wr4, wr2, word_mstore_disjoint, word_mstore,
        Nat.mul_zero, Nat.add_zero]
      exact pw0_eq x
    · simp (disch := first | omega | exact hl _) only [wr4, wr2, word_mstore_disjoint, word_mstore,
        show fp + 512 * 1 = 512 + fp by omega]
      exact pw1_eq x
    · simp (disch := first | omega | exact hl _) only [wr4, wr2, word_mstore_disjoint, word_mstore,
        show fp + 512 * 2 = 1024 + fp by omega]
      exact pw2_eq x
    · simp (disch := first | omega | exact hl _) only [wr4, wr2, word_mstore,
        show fp + 512 * 3 = 1536 + fp by omega]
      exact pw3_eq x

/-- Memory after `i` iterations (`B` coefficients, `F` stream). -/
def Mi (nr : Nat) (m : ByteArray) (B F : Nat) : Nat → ByteArray
  | 0 => m
  | i + 1 => wrN nr (Mi nr m B F i) (pkA (Mi nr m B F i) (B + 512 * i)) (F + 32 * i)

theorem Mi_low (nr : Nat) (m : ByteArray) (B F : Nat) {a : Nat} (h : a + 32 ≤ F) :
    ∀ i, word (Mi nr m B F i) a = word m a
  | 0 => rfl
  | i + 1 => by
    show word (wrN nr _ _ _) a = _
    rw [wrN_word nr _ _ _ (fun r _ => by omega), Mi_low nr m B F h i]

theorem Mi_far (nr : Nat) (m : ByteArray) (B F : Nat) {j r : Nat} (hj : j < 16) (hr : r < 4) :
    ∀ i, j + 1 ≤ i → i ≤ 16 →
      word (Mi nr m B F i) (F + 32 * j + 512 * r) = word (Mi nr m B F (j + 1)) (F + 32 * j + 512 * r)
  | 0, h1, _ => by omega
  | i + 1, h1, h2 => by
    by_cases hi : j + 1 = i + 1
    · rw [hi]
    · show word (wrN nr _ _ _) _ = _
      rw [wrN_word nr _ _ _ (fun r' hr' => by omega), Mi_far nr m B F hj hr i (by omega) (by omega)]

theorem Mi_byte (nr : Nat) (m : ByteArray) (B F : Nat) {a : Nat}
    (h : a < F ∨ F + 512 * (if nr ≤ 2 then 2 else 4) ≤ a) :
    ∀ i, i ≤ 16 → byteAt (Mi nr m B F i) a = byteAt m a
  | 0, _ => rfl
  | i + 1, hi => by
    show byteAt (wrN nr _ _ _) a = _
    rw [wrN_byte nr _ _ _ (by split_ifs at h ⊢ <;> omega), Mi_byte nr m B F h i (by omega)]

theorem pkA_congr {M M' : ByteArray} {wp : Nat}
    (h : ∀ a, wp ≤ a → a + 32 ≤ wp + 512 → word M a = word M' a) : pkA M wp = pkA M' wp := by
  simp (disch := omega) only [pkA, h]

/-! ## The loop and the contract -/

theorem pk_loop {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (m : ByteArray) {nr : Nat} (hnr : nr = 2 ∨ nr = 4) {B F : Nat}
    (hB : B + 8192 ≤ 90656) (hF : F + 2048 ≤ 90656) :
    Reach (callState s 17413 (wd nr :: wd F :: wd B :: wd (8192 + B) :: wd ret :: tail) m)
      (callState s 17782 (wd nr :: wd (32 + (F + 32 * 15)) :: wd (512 + (B + 512 * 15)) ::
        wd (8192 + B) :: wd ret :: tail) (Mi nr m B F 16)) (15 * cI nr + cI nr) := by
  have hstep : ∀ i, i < 15 → Reach
      (callState s 17413 (wd nr :: wd (F + 32 * i) :: wd (B + 512 * i) :: wd (8192 + B) :: wd ret :: tail)
        (Mi nr m B F i))
      (callState s 17413 (wd nr :: wd (F + 32 * (i + 1)) :: wd (B + 512 * (i + 1)) :: wd (8192 + B) ::
        wd ret :: tail) (Mi nr m B F (i + 1))) (cI nr) := by
    intro i hi
    have h := pk_iter hs (ret := ret) htail (Mi nr m B F i) hnr (B + 512 * i) (F + 32 * i) (8192 + B)
      (by omega) (by omega) (by omega) (by omega)
    rw [show 32 + (F + 32 * i) = F + 32 * (i + 1) by ring,
      show 512 + (B + 512 * i) = B + 512 * (i + 1) by ring] at h
    exact h
  have hloop := Reach.loop (I := fun i => callState s 17413 (wd nr :: wd (F + 32 * i) ::
    wd (B + 512 * i) :: wd (8192 + B) :: wd ret :: tail) (Mi nr m B F i)) 15 hstep
  have hlast := pk_iterx hs (ret := ret) htail (Mi nr m B F 15) hnr (B + 512 * 15) (F + 32 * 15)
    (8192 + B) (by omega) (by omega) (by omega) (by omega)
  exact (hloop.of_eq (by simp [Mi]) rfl).trans hlast

theorem pack_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pack ret tail) (m : ByteArray) {g nr : Nat} (hg : g < 2)
    (hnr : nr = 2 ∨ nr = 4) :
    ∃ m', ((∀ t, t < 256 → ∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t)) r < 16) →
        ∀ r, r < nr → ∀ j, j < 16 → word m' (FIN + 256 + 2048 * g + 32 * (16 * r + j)) =
          rep (le64 (Fips204.simpleBitPack (lanesPoly m (ACC + 0x2000 * g) r) 15) (8 * j))) ∧
      FrameExcept m m' [(FIN + 256 + 2048 * g, FIN + 256 + 2048 * g + 512 * nr)] ∧
      Call s Entry.pack [wd nr, wd (FIN + 256 + 2048 * g), wd (ACC + 0x2000 * g)] ret tail m []
        m' (Gas.pack nr) := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pack, Stack.leaf] at this; omega
  have hB : ACC + 0x2000 * g + 8192 ≤ FIN + 256 + 2048 * g := by unfold ACC FIN; omega
  have hF : FIN + 256 + 2048 * g + 2048 ≤ 90656 := by unfold FIN; omega
  have hnr4 : nr ≤ 4 := by omega
  refine ⟨Mi nr m (ACC + 0x2000 * g) (FIN + 256 + 2048 * g) 16, fun hA r hr' j hj => ?_,
    fun a ha => ?_, ?_⟩
  · rw [show FIN + 256 + 2048 * g + 32 * (16 * r + j) = FIN + 256 + 2048 * g + 32 * j + 512 * r by ring,
      Mi_far nr m _ _ hj (by omega) 16 (by omega) le_rfl]
    show word (wrN nr _ _ _) _ = _
    rw [wrN_hit hnr _ _ _ hr', pkA_congr (M' := m) (fun a h1 h2 => Mi_low nr m _ _ (by omega) j),
      Xl_pkA_le64 m _ j hj (fun t r ht hr => hA t ht r hr) (by omega)]
  · have h : a < FIN + 256 + 2048 * g ∨ FIN + 256 + 2048 * g + 512 * (if nr ≤ 2 then 2 else 4) ≤ a := by
      have := ha (FIN + 256 + 2048 * g, FIN + 256 + 2048 * g + 512 * nr) (by simp)
      have hk : 512 * (if nr ≤ 2 then 2 else 4) = 512 * nr := by rcases hnr with rfl | rfl <;> rfl
      omega
    exact Mi_byte nr m _ _ h 16 le_rfl
  · rw [call_iff, Entry.pack]
    have h := ((pk_entry hs (ret := ret) htail m nr (FIN + 256 + 2048 * g) (ACC + 0x2000 * g)).trans
      (pk_loop hs htail m hnr (by omega) hF)).trans
      (pk_exit hs htail hr.jumpdest hr.small (Mi nr m _ _ 16) _ _ _ _)
    refine h.mono ?_
    unfold cI Gas.pack; rcases hnr with rfl | rfl <;> norm_num

end MlDsaOpt87.Proofs.G5PK
