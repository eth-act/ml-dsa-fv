import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
import MlDsaOpt44.Fn.Blk.Mem
import MlDsaOpt87.Fn.Blk.Blocks
import MlDsaOpt87.Fn.Blk.BodyA
import MlDsaOpt44.Fn.Blk.Defs
/- Ported from `MlDsaOpt44/Fn/Blk/Proof.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# `blk`: proof of `blk_call` (WP3)

Entry `[flp, abp, ret]`. Un-complements the rate lanes of `KS` in place
(restoring them at the end), de-interleaves 3 words at a time with 6 delta
swaps (bit `4b + k` ↦ `64k + b`) and writes, per 8 candidates, 8 row-packed
candidate words at `abp` (lane = slot) and one rejection-flag word at `flp`.
The block number `b ≤ 5` selects `abp = ABUF + 1792 b`, `flp = FL + 224 b`.

Proof: prologue `Blk.pro` (111 gas), seven loop iterations `Blk.bodyA` +
`Blk.bodyB_loop`/`Blk.bodyB_exit` (1087 gas each), epilogue `Blk.epi` (116 gas):
exactly `Gas.blk = 7836`. Bit facts in `Blk/Bits.lean`, memory facts in
`Blk/Mem.lean`.
-/

namespace MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

namespace Blk

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Blk

/-! ## Candidates in lane form -/

theorem sbyte_lin (S : Fips202.SpongeState) (j c : Nat) :
    sbyte S (24 * j + c) = laneOf S (3 * j + c / 8) / 2 ^ (8 * (c % 8)) % 256 := by
  unfold sbyte
  rw [show (24 * j + c) / 8 = 3 * j + c / 8 by omega, show (24 * j + c) % 8 = c % 8 by omega]

theorem cand_lin (S : Fips202.SpongeState) (j k : Nat) :
    cand S (8 * j + k) = laneOf S (3 * j + 3 * k / 8) / 2 ^ (8 * (3 * k % 8)) % 256 +
      256 * (laneOf S (3 * j + (3 * k + 1) / 8) / 2 ^ (8 * ((3 * k + 1) % 8)) % 256) +
      65536 * (laneOf S (3 * j + (3 * k + 2) / 8) / 2 ^ (8 * ((3 * k + 2) % 8)) % 256 % 128) := by
  unfold cand
  rw [show 3 * (8 * j + k) = 24 * j + 3 * k by ring, show 24 * j + 3 * k + 1 = 24 * j + (3 * k + 1) by ring,
    show 24 * j + 3 * k + 2 = 24 * j + (3 * k + 2) by ring, sbyte_lin, sbyte_lin, sbyte_lin]

/-- Lanes `3j + w` of the four states. -/
def ln (S : Nat → Fips202.SpongeState) (j w : Nat) (k : Nat) : Nat := laneOf (S k) (3 * j + w)

theorem ln_lt (S : Nat → Fips202.SpongeState) (j w : Nat) : ∀ k, k < 4 → ln S j w k < 2 ^ 64 :=
  fun _ _ => laneOf_lt _ _

theorem pack4_lt' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) : pack4 v < 2 ^ 256 := by
  have := h 0 (by omega); have := h 1 (by omega); have := h 2 (by omega); have := h 3 (by omega)
  unfold pack4; omega

/-- The lane value of candidate `8j + k` (the shape `c_pack4` produces). -/
def X (S : Nat → Fips202.SpongeState) (j k : Nat) (s : Nat) : Nat :=
  match k with
  | 0 => ln S j 0 s % 2 ^ 23
  | 1 => ln S j 0 s / 2 ^ 24 % 2 ^ 23
  | 2 => ln S j 0 s / 2 ^ 48 % 2 ^ 16 + 2 ^ 16 * (ln S j 1 s % 2 ^ 7)
  | 3 => ln S j 1 s / 2 ^ 8 % 2 ^ 23
  | 4 => ln S j 1 s / 2 ^ 32 % 2 ^ 23
  | 5 => ln S j 1 s / 2 ^ 56 % 2 ^ 8 + 2 ^ 8 * (ln S j 2 s % 2 ^ 15)
  | 6 => ln S j 2 s / 2 ^ 16 % 2 ^ 23
  | _ => ln S j 2 s / 2 ^ 40 % 2 ^ 23

theorem X_eq (S : Nat → Fips202.SpongeState) (j : Nat) {k : Nat} (hk : k < 8) (s : Nat) :
    X S j k s = cand (S s) (8 * j + k) := by
  rw [cand_lin]
  interval_cases k <;> simp only [X, ln] <;> norm_num <;> omega

theorem cw_pack4 (S : Nat → Fips202.SpongeState) (j : Nat) {k : Nat} (hk : k < 8) :
    cw k (pack4 (ln S j 0)) (pack4 (ln S j 1)) (pack4 (ln S j 2)) = pack4 (X S j k) := by
  have h0 := ln_lt S j 0; have h1 := ln_lt S j 1; have h2 := ln_lt S j 2
  interval_cases k
  · exact c0_pack4 h0 h1 h2
  · exact c1_pack4 h0 h1 h2
  · exact c2_pack4 h0 h1 h2
  · exact c3_pack4 h0 h1 h2
  · exact c4_pack4 h0 h1 h2
  · exact c5_pack4 h0 h1 h2
  · exact c6_pack4 h0 h1 h2
  · exact c7_pack4 h0 h1 h2

theorem X_lt (S : Nat → Fips202.SpongeState) (j : Nat) {k : Nat} (hk : k < 8) :
    ∀ s, s < 4 → X S j k s < 2 ^ 23 := by
  intro s _
  interval_cases k <;> simp only [X] <;> omega

theorem cw_cand (S : Nat → Fips202.SpongeState) (j : Nat) {k : Nat} (hk : k < 8) :
    cw k (pack4 (ln S j 0)) (pack4 (ln S j 1)) (pack4 (ln S j 2)) % 2 ^ 256 =
      pack4 fun s => cand (S s) (8 * j + k) := by
  rw [cw_pack4 S j hk, Nat.mod_eq_of_lt (pack4_lt' fun s hs => by have := X_lt S j hk s hs; omega)]
  exact congrArg pack4 (funext fun s => X_eq S j hk s)

theorem foldl_or_lt {n : Nat} : ∀ (l : List Nat) (acc : Nat), acc < 2 ^ n → (∀ x ∈ l, x < 2 ^ n) →
    l.foldl (· ||| ·) acc < 2 ^ n
  | [], _, h, _ => h
  | x :: l, _, h, hl => foldl_or_lt l _ (Nat.or_lt_two_pow h (hl x (by simp)))
      (fun y hy => hl y (by simp [hy]))

theorem flagWord_lt (S : Nat → Fips202.SpongeState) (j : Nat) : flagWord S j < 2 ^ 256 := by
  unfold flagWord orList
  refine foldl_or_lt _ 0 (by positivity) fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have hk8 : k < 8 := List.mem_range.mp hk
  refine pack4_lt' fun s hs => ?_
  have := X_lt S j hk8 s hs
  rw [X_eq S j hk8 s] at this
  unfold Fips204.q; omega

theorem lfv_flag (S : Nat → Fips202.SpongeState) (j : Nat) :
    lfv (pack4 (ln S j 0)) (pack4 (ln S j 1)) (pack4 (ln S j 2)) % 2 ^ 256 = flagWord S j := by
  have e : ∀ k, k < 8 → CF + cw k (pack4 (ln S j 0)) (pack4 (ln S j 1)) (pack4 (ln S j 2)) =
      pack4 fun s => cand (S s) (8 * j + k) + 2 ^ 23 - Fips204.q := by
    intro k hk
    rw [cw_pack4 S j hk, CF_add_pack4]
    exact congrArg pack4 (funext fun s => by rw [X_eq S j hk s]; unfold Fips204.q; omega)
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega)
  simp only [cw] at e0 e1 e2 e3 e4 e5 e6 e7
  have heq : lfv (pack4 (ln S j 0)) (pack4 (ln S j 1)) (pack4 (ln S j 2)) = flagWord S j := by
    unfold lfv
    rw [e0, e1, e2, e3, e4, e5, e6, e7, lor8]
    unfold flagWord
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
  rw [heq]
  exact Nat.mod_eq_of_lt (flagWord_lt S j)

/-! ## The loop -/

/-- Loop-head stack of iteration `j`. -/
def stk (b ret : Nat) (tail : List UInt256) (j : Nat) : List UInt256 :=
  wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd (96 * j) :: wd (FL + 224 * b + 32 * j) ::
    wd (ABUF + 1792 * b + 256 * j) :: wd ret :: tail

/-- Memory after `j` iterations. -/
def Inv (m : ByteArray) (b j : Nat) (M : ByteArray) : Prop :=
  FrameExcept (flip6 m) M [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)] ∧
    ∀ S, KS4 m S →
      (∀ i, i < 8 * j → word M (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (S k) i) ∧
      (∀ g, g < j → word M (FL + 224 * b + 32 * g) = flagWord S g)

theorem step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960)
    (m : ByteArray) {b : Nat} (hb : b ≤ 5) {j : Nat} (hj : j < 7) (M : ByteArray) (hI : Inv m b j M) :
    ∃ M', Inv m b (j + 1) M' ∧
      Reach (callState s 10991 (stk b ret tail j) M)
        (callState s (if j + 1 < 7 then 10991 else 11887) (stk b ret tail (j + 1)) M') 1087 := by
  have hABUF : ABUF = 20480 := rfl
  have hFL : FL = 31232 := rfl
  have hA := bodyA hs (rest := wd ret :: tail) (by simp only [List.length_cons]; omega)
    U5 U4 U3 U2 U1 U0 (96 * j) (FL + 224 * b + 32 * j) (ABUF + 1792 * b + 256 * j) M (by omega)
    (by omega)
  generalize hD0 : unz U0 U1 U2 U3 U4 U5 (word M (96 * j)) = D0 at hA
  generalize hD1 : unz U0 U1 U2 U3 U4 U5 (word M (32 + 96 * j)) = D1 at hA
  generalize hD2 : unz U0 U1 U2 U3 U4 U5 (word M (64 + 96 * j)) = D2 at hA
  have e1 : 96 + 96 * j = 96 * (j + 1) := by ring
  have e2 : 32 + (FL + 224 * b + 32 * j) = FL + 224 * b + 32 * (j + 1) := by ring
  have e3 : 256 + (ABUF + 1792 * b + 256 * j) = ABUF + 1792 * b + 256 * (j + 1) := by ring
  refine ⟨MachineState.writeBytes (candMem M (ABUF + 1792 * b + 256 * j) D0 D1 D2)
    (Data.Bytes.natToBytesPadded (lfv D0 D1 D2 % 2 ^ 256) 32) (FL + 224 * b + 32 * j), ?_, ?_⟩
  · -- the invariant
    refine ⟨?_, ?_⟩
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
      have hfr : ∀ a, a + 32 ≤ 672 → word M a = word (flip6 m) a := fun a ha =>
        hI.1.word (by simp only [avoids_cons, avoids_nil, and_true]; omega)
      have hD : ∀ w, w < 3 → word M (32 * w + 96 * j) = il (ln S j w) := by
        intro w hw
        rw [hfr _ (by omega), show 32 * w + 96 * j = 32 * (3 * j + w) by ring, ks_lane hKS (by omega)]
        rfl
      have hD0' : D0 = pack4 (ln S j 0) := by
        rw [← hD0, show 96 * j = 32 * 0 + 96 * j by ring, hD 0 (by omega), unz_il (ln_lt S j 0)]
      have hD1' : D1 = pack4 (ln S j 1) := by
        rw [← hD1, show 32 + 96 * j = 32 * 1 + 96 * j by ring, hD 1 (by omega), unz_il (ln_lt S j 1)]
      have hD2' : D2 = pack4 (ln S j 2) := by
        rw [← hD2, show 64 + 96 * j = 32 * 2 + 96 * j by ring, hD 2 (by omega), unz_il (ln_lt S j 2)]
      subst hD0' hD1' hD2'
      refine ⟨fun i hi => ?_, fun g hg => ?_⟩
      · rw [word_wb _ _ (by omega), if_neg (by omega)]
        by_cases hij : i < 8 * j
        · rw [word_candMem_disjoint _ _ _ _ _ (by omega)]
          exact hcand i hij
        · obtain ⟨k, rfl⟩ : ∃ k, i = 8 * j + k := ⟨i - 8 * j, by omega⟩
          rw [show ABUF + 1792 * b + 32 * (8 * j + k) = ABUF + 1792 * b + 256 * j + 32 * k by ring,
            word_candMem _ _ _ _ _ (by omega)]
          exact cw_cand S j (by omega)
      · by_cases hgj : g < j
        · rw [word_wb _ _ (by omega), if_neg (by omega),
            word_candMem_disjoint _ _ _ _ _ (by omega)]
          exact hflag g hgj
        · obtain rfl : g = j := by omega
          rw [word_wb _ _ (by omega), if_pos rfl]
          exact lfv_flag S g
  · -- the trace
    by_cases hj7 : j + 1 < 7
    · have hB := bodyB_loop hs htail (lfv D0 D1 D2) D2 D1 D0 U5 U4 U3 U2 U1 U0 (96 * j)
        (FL + 224 * b + 32 * j) (ABUF + 1792 * b + 256 * j) ret
        (candMem M (ABUF + 1792 * b + 256 * j) D0 D1 D2) (by omega) (by omega)
      rw [e1, e2, e3] at hB
      rw [if_pos hj7]
      exact (hA.trans hB).mono (by omega)
    · have hB := bodyB_exit hs htail (lfv D0 D1 D2) D2 D1 D0 U5 U4 U3 U2 U1 U0 (96 * j)
        (FL + 224 * b + 32 * j) (ABUF + 1792 * b + 256 * j) ret
        (candMem M (ABUF + 1792 * b + 256 * j) D0 D1 D2) (by omega) (by omega)
      rw [e1, e2, e3] at hB
      rw [if_neg hj7]
      exact (hA.trans hB).mono (by omega)

theorem loop {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960)
    (m : ByteArray) {b : Nat} (hb : b ≤ 5) :
    ∀ j, j ≤ 7 → ∃ M, Inv m b j M ∧
      Reach (callState s 10991 (stk b ret tail 0) (flip6 m))
        (callState s (if j < 7 then 10991 else 11887) (stk b ret tail j) M) (1087 * j)
  | 0, _ => ⟨flip6 m, ⟨FrameExcept.refl _ _, fun _ _ => ⟨fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩⟩,
      by rw [if_pos (by omega), Nat.mul_zero]; exact Reach.refl _⟩
  | j + 1, hj => by
    obtain ⟨M, hI, hR⟩ := loop hs htail m hb j (by omega)
    rw [if_pos (by omega)] at hR
    obtain ⟨M', hI', hR'⟩ := step hs htail m hb (j := j) (by omega) M hI
    exact ⟨M', hI', (hR.trans hR').mono (by omega)⟩

end Blk

open Blk MlDsaOpt44.Proofs.Blk in
theorem blk_call_proof {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {b : Nat} (hb : b ≤ 5) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 56 → word m' (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 7 → word m' (FL + 224 * b + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)] ∧
      Call s Entry.blk [wd (FL + 224 * b), wd (ABUF + 1792 * b)] ret tail m [] m' Gas.blk := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.blk, Stack.leaf] at this; omega
  have hABUF : ABUF = 20480 := rfl
  have hFL : FL = 31232 := rfl
  obtain ⟨Mf, hI, hL⟩ := loop hs htail m hb 7 le_rfl
  rw [if_neg (by omega)] at hL
  have hpro := pro hs htail (FL + 224 * b) (ABUF + 1792 * b) ret m
  have hepi := epi hs htail U5 U4 U3 U2 U1 U0 (96 * 7) (FL + 224 * b + 32 * 7)
    (ABUF + 1792 * b + 256 * 7) ret Mf hr.jumpdest hr.small
  refine ⟨flip6 Mf, fun S _ hKS => ?_, ?_, ?_⟩
  · obtain ⟨hcand, hflag⟩ := hI.2 S hKS
    refine ⟨fun i hi => ?_, fun g hg => ?_⟩
    · rw [word_flip6_high _ (by omega)]; exact hcand i (by omega)
    · rw [word_flip6_high _ (by omega)]; exact hflag g hg
  · exact flip6_frame (by simp only [avoids_cons, avoids_nil, and_true]; omega) hI.1
  · rw [call_iff]
    have h := (hpro.trans hL).trans hepi
    simp only [List.cons_append, List.nil_append, Entry.blk, Gas.blk]
    exact h.mono (by norm_num)

end MlDsaOpt87.Proofs
