import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
import MlDsaOpt44.Fn.Blk.Mem
import MlDsaOpt44.Fn.Blk.Blocks
import MlDsaOpt44.Fn.Blk.BodyA
import MlDsaOpt44.Fn.Blk.Defs
/-!
# `blk`, `blkh`, `blkt`: proofs (WP3, v4)

The three entries push the lane range `[xp, xe)` (`blkt` also its `abp`, `flp`)
and run one shared body: un-complement the rate lanes of `KS` in
place (restored at the end), de-interleave 3 words at a time with 6 delta
swaps (bit `4b + k` ↦ `64k + b`) and write, per 8 candidates, 8 row-packed
candidate words at `abp` (lane = slot) and one rejection-flag word at `flp`.

Proof: `Blk.run` is the body over iterations `j0 … j0 + N − 1` at any placement
`Geo`: prologue `Blk.pro` (109 gas), `N` loop iterations `Blk.bodyA` +
`Blk.bodyB_loop`/`Blk.bodyB_exit` (1087 gas each, 2 more for the exit's
`POP`), epilogue `Blk.epi` (116 gas). With the entries (6, 17, 24 gas) this is
exactly `Gas.blk`, `Gas.blkh`, `Gas.blkt`. Bit facts in `Blk/Bits.lean`, memory
facts in `Blk/Mem.lean`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

namespace Blk

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

/-- Placement of a run over the lanes `[3 j0, 3 (j0 + N))`: candidate words
from `abp0`, flag words from `flp0`, both above the lane flips and disjoint. -/
structure Geo (j0 N abp0 flp0 : Nat) : Prop where
  hj : j0 + N ≤ 7
  ha : 800 ≤ abp0
  ha' : abp0 + 256 * N ≤ 66080
  hf : 800 ≤ flp0
  hf' : flp0 + 32 * N ≤ 66080
  hd : abp0 + 256 * N ≤ flp0 ∨ flp0 + 32 * N ≤ abp0

/-- Loop-head stack after `n` iterations. -/
def stk (j0 N abp0 flp0 ret : Nat) (tail : List UInt256) (n : Nat) : List UInt256 :=
  wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd (96 * (j0 + N)) :: wd (96 * (j0 + n)) ::
    wd (flp0 + 32 * n) :: wd (abp0 + 256 * n) :: wd ret :: tail

/-- Memory after `n` iterations. -/
def Inv (m : ByteArray) (j0 N abp0 flp0 n : Nat) (M : ByteArray) : Prop :=
  FrameExcept (flip6 m) M [(abp0, abp0 + 256 * N), (flp0, flp0 + 32 * N)] ∧
    ∀ S, KS4 m S →
      (∀ i, i < 8 * n → word M (abp0 + 32 * i) = pack4 fun k => cand (S k) (8 * j0 + i)) ∧
      (∀ g, g < n → word M (flp0 + 32 * g) = flagWord S (j0 + g))

/-- The state after `n` iterations: the loop head, or the epilogue after the last. -/
def hd (s : State) (j0 N abp0 flp0 ret : Nat) (tail : List UInt256) (n : Nat) (M : ByteArray) :
    State :=
  if n < N then callState s 9248 (stk j0 N abp0 flp0 ret tail n) M
  else callState s 10143 (stk j0 N abp0 flp0 ret tail n).tail M

theorem step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960)
    (m : ByteArray) {j0 N abp0 flp0 : Nat} (hg : Geo j0 N abp0 flp0) {n : Nat} (hn : n < N)
    (M : ByteArray) (hI : Inv m j0 N abp0 flp0 n M) :
    ∃ M', Inv m j0 N abp0 flp0 (n + 1) M' ∧
      Reach (callState s 9248 (stk j0 N abp0 flp0 ret tail n) M)
        (hd s j0 N abp0 flp0 ret tail (n + 1) M') (if n + 1 < N then 1087 else 1089) := by
  obtain ⟨hj, ha, ha', hf, hf', hdj⟩ := hg
  have hA := bodyA hs (rest := wd ret :: tail) (by simp only [List.length_cons]; omega)
    U5 U4 U3 U2 U1 U0 (96 * (j0 + N)) (96 * (j0 + n)) (flp0 + 32 * n) (abp0 + 256 * n) M
    (by omega) (by omega)
  generalize hD0 : unz U0 U1 U2 U3 U4 U5 (word M (96 * (j0 + n))) = D0 at hA
  generalize hD1 : unz U0 U1 U2 U3 U4 U5 (word M (32 + 96 * (j0 + n))) = D1 at hA
  generalize hD2 : unz U0 U1 U2 U3 U4 U5 (word M (64 + 96 * (j0 + n))) = D2 at hA
  have e1 : 96 + 96 * (j0 + n) = 96 * (j0 + (n + 1)) := by ring
  have e2 : 32 + (flp0 + 32 * n) = flp0 + 32 * (n + 1) := by ring
  have e3 : 256 + (abp0 + 256 * n) = abp0 + 256 * (n + 1) := by ring
  refine ⟨MachineState.writeBytes (candMem M (abp0 + 256 * n) D0 D1 D2)
    (Data.Bytes.natToBytesPadded (lfv D0 D1 D2 % 2 ^ 256) 32) (flp0 + 32 * n), ?_, ?_⟩
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
      have hD : ∀ w, w < 3 → word M (32 * w + 96 * (j0 + n)) = il (ln S (j0 + n) w) := by
        intro w hw
        rw [hfr _ (by omega), show 32 * w + 96 * (j0 + n) = 32 * (3 * (j0 + n) + w) by ring,
          ks_lane hKS (by omega)]
        rfl
      have hD0' : D0 = pack4 (ln S (j0 + n) 0) := by
        rw [← hD0, show 96 * (j0 + n) = 32 * 0 + 96 * (j0 + n) by ring, hD 0 (by omega),
          unz_il (ln_lt S _ 0)]
      have hD1' : D1 = pack4 (ln S (j0 + n) 1) := by
        rw [← hD1, show 32 + 96 * (j0 + n) = 32 * 1 + 96 * (j0 + n) by ring, hD 1 (by omega),
          unz_il (ln_lt S _ 1)]
      have hD2' : D2 = pack4 (ln S (j0 + n) 2) := by
        rw [← hD2, show 64 + 96 * (j0 + n) = 32 * 2 + 96 * (j0 + n) by ring, hD 2 (by omega),
          unz_il (ln_lt S _ 2)]
      subst hD0' hD1' hD2'
      refine ⟨fun i hi => ?_, fun g hg => ?_⟩
      · rw [word_wb _ _ (by omega), if_neg (by omega)]
        by_cases hij : i < 8 * n
        · rw [word_candMem_disjoint _ _ _ _ _ (by omega)]
          exact hcand i hij
        · obtain ⟨k, rfl⟩ : ∃ k, i = 8 * n + k := ⟨i - 8 * n, by omega⟩
          rw [show abp0 + 32 * (8 * n + k) = abp0 + 256 * n + 32 * k by ring,
            word_candMem _ _ _ _ _ (by omega), cw_cand S (j0 + n) (by omega),
            show 8 * (j0 + n) + k = 8 * j0 + (8 * n + k) by ring]
      · by_cases hgn : g < n
        · rw [word_wb _ _ (by omega), if_neg (by omega),
            word_candMem_disjoint _ _ _ _ _ (by omega)]
          exact hflag g hgn
        · obtain rfl : g = n := by omega
          rw [word_wb _ _ (by omega), if_pos rfl]
          exact lfv_flag S (j0 + g)
  · -- the trace
    unfold hd
    by_cases hn1 : n + 1 < N
    · have hB := bodyB_loop hs htail (lfv D0 D1 D2) D2 D1 D0 U5 U4 U3 U2 U1 U0 (96 * (j0 + N))
        (96 * (j0 + n)) (flp0 + 32 * n) (abp0 + 256 * n) ret
        (candMem M (abp0 + 256 * n) D0 D1 D2) (by omega) (by omega) (by omega)
      rw [e1, e2, e3] at hB
      rw [if_pos hn1, if_pos hn1]
      exact (hA.trans hB).mono (by omega)
    · have hB := bodyB_exit hs htail (lfv D0 D1 D2) D2 D1 D0 U5 U4 U3 U2 U1 U0 (96 * (j0 + N))
        (96 * (j0 + n)) (flp0 + 32 * n) (abp0 + 256 * n) ret
        (candMem M (abp0 + 256 * n) D0 D1 D2) (by omega) (by omega) (by omega)
      rw [e1, e2, e3] at hB
      rw [if_neg hn1, if_neg hn1]
      exact (hA.trans hB).mono (by omega)

theorem loop {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960)
    (m : ByteArray) {j0 N abp0 flp0 : Nat} (hg : Geo j0 N abp0 flp0) (hN : 0 < N) :
    ∀ n, n ≤ N → ∃ M, Inv m j0 N abp0 flp0 n M ∧
      Reach (callState s 9248 (stk j0 N abp0 flp0 ret tail 0) (flip6 m))
        (hd s j0 N abp0 flp0 ret tail n M) (1087 * n + if n < N then 0 else 2)
  | 0, _ => ⟨flip6 m, ⟨FrameExcept.refl _ _, fun _ _ => ⟨fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩⟩,
      by unfold hd; rw [if_pos hN, if_pos hN]; exact Reach.refl _⟩
  | n + 1, hn => by
    obtain ⟨M, hI, hR⟩ := loop hs htail m hg hN n (by omega)
    unfold hd at hR
    rw [if_pos (by omega), if_pos (by omega)] at hR
    obtain ⟨M', hI', hR'⟩ := step hs htail m hg (n := n) (by omega) M hI
    refine ⟨M', hI', (hR.trans hR').mono ?_⟩
    split <;> omega

/-- The shared body from pc 9030 (`[xe, xp, flp, abp, ret]`) to the return. -/
theorem run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (m : ByteArray) {j0 N abp0 flp0 : Nat} (hg : Geo j0 N abp0 flp0) (hN : 0 < N) :
    ∃ m', (∀ S, KS4 m S →
        (∀ i, i < 8 * N → word m' (abp0 + 32 * i) = pack4 fun k => cand (S k) (8 * j0 + i)) ∧
        (∀ g, g < N → word m' (flp0 + 32 * g) = flagWord S (j0 + g))) ∧
      FrameExcept m m' [(abp0, abp0 + 256 * N), (flp0, flp0 + 32 * N)] ∧
      Reach (callState s 9030 (wd (96 * (j0 + N)) :: wd (96 * j0) :: wd flp0 :: wd abp0 :: wd ret ::
          tail) m) (callState s ret tail m') (1087 * N + 227) := by
  obtain ⟨Mf, hI, hL⟩ := loop hs htail m hg hN (ret := ret) N le_rfl
  unfold hd at hL
  rw [if_neg (by omega), if_neg (by omega)] at hL
  have hpro := pro hs htail (96 * (j0 + N)) (96 * j0) flp0 abp0 ret m
  have hepi := epi hs htail U4 U3 U2 U1 U0 (96 * (j0 + N)) (96 * (j0 + N))
    (flp0 + 32 * N) (abp0 + 256 * N) ret Mf hj hret
  have hg' := hg
  obtain ⟨_, ha, _, hf, _, _⟩ := hg'
  refine ⟨flip6 Mf, fun S hKS => ?_, ?_, ?_⟩
  · obtain ⟨hcand, hflag⟩ := hI.2 S hKS
    refine ⟨fun i hi => ?_, fun g hg => ?_⟩
    · rw [word_flip6_high _ (by omega)]; exact hcand i hi
    · rw [word_flip6_high _ (by omega)]; exact hflag g hg
  · exact flip6_frame (by simp only [avoids_cons, avoids_nil, and_true]; omega) hI.1
  · have hpro' : Reach (callState s 9030 (wd (96 * (j0 + N)) :: wd (96 * j0) :: wd flp0 :: wd abp0 ::
        wd ret :: tail) m) (callState s 9248 (stk j0 N abp0 flp0 ret tail 0) (flip6 m)) 109 := by
      simpa only [stk, Nat.add_zero, Nat.mul_zero] using hpro
    have hepi' : Reach (callState s 10143 (stk j0 N abp0 flp0 ret tail N).tail Mf)
        (callState s ret tail (flip6 Mf)) 116 := by
      simpa only [stk, List.tail_cons] using hepi
    exact ((hpro'.trans hL).trans hepi').mono (by omega)

end Blk

open Blk

/-- **blk** (proof). -/
theorem blk_call_proof {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {abp flp : Nat}
    (ha : KS + 800 ≤ abp) (ha' : abp + 1792 ≤ TOP) (hf : KS + 800 ≤ flp) (hf' : flp + 224 ≤ TOP)
    (hd : abp + 1792 ≤ flp ∨ flp + 224 ≤ abp) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 56 → word m' (abp + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 7 → word m' (flp + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(abp, abp + 1792), (flp, flp + 224)] ∧
      Call s Entry.blk [wd flp, wd abp] ret tail m [] m' Gas.blk := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.blk, Stack.leaf] at this; omega
  simp only [KS, TOP] at ha ha' hf hf'
  obtain ⟨m', hpost, hfr, hreach⟩ := run hs htail hr.jumpdest hr.small m (j0 := 0) (N := 7)
    (abp0 := abp) (flp0 := flp) ⟨by omega, ha, by omega, hf, by omega, by omega⟩ (by omega)
  refine ⟨m', fun S _ hKS => ?_, by simpa using hfr, ?_⟩
  · obtain ⟨h1, h2⟩ := hpost S hKS
    exact ⟨fun i hi => by simpa using h1 i (by omega), fun g hg => by simpa using h2 g hg⟩
  · rw [call_iff]
    have he := ent_blk hs htail flp abp ret m
    simp only [List.cons_append, List.nil_append, Entry.blk, Gas.blk]
    exact (he.trans (by simpa using hreach)).mono (by norm_num)

/-- **blkh** (proof). -/
theorem blkh_call_proof {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {abp flp : Nat}
    (ha : KS + 800 ≤ abp) (ha' : abp + 1024 ≤ TOP) (hf : KS + 800 ≤ flp) (hf' : flp + 128 ≤ TOP)
    (hd : abp + 1024 ≤ flp ∨ flp + 128 ≤ abp) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 32 → word m' (abp + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 4 → word m' (flp + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(abp, abp + 1024), (flp, flp + 128)] ∧
      Call s Entry.blkh [wd flp, wd abp] ret tail m [] m' Gas.blkh := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.blk, Stack.leaf] at this; omega
  simp only [KS, TOP] at ha ha' hf hf'
  obtain ⟨m', hpost, hfr, hreach⟩ := run hs htail hr.jumpdest hr.small m (j0 := 0) (N := 4)
    (abp0 := abp) (flp0 := flp) ⟨by omega, ha, by omega, hf, by omega, by omega⟩ (by omega)
  refine ⟨m', fun S _ hKS => ?_, by simpa using hfr, ?_⟩
  · obtain ⟨h1, h2⟩ := hpost S hKS
    exact ⟨fun i hi => by simpa using h1 i (by omega), fun g hg => by simpa using h2 g hg⟩
  · rw [call_iff]
    have he := ent_blkh hs htail flp abp ret m
    simp only [List.cons_append, List.nil_append, Entry.blkh, Gas.blkh]
    exact (he.trans (by simpa using hreach)).mono (by norm_num)

/-- **blkt** (proof). -/
theorem blkt_call_proof {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, 32 ≤ i → i < 56 → word m' (ABUF + 1792 * 4 + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, 4 ≤ g → g < 7 → word m' (FL + 224 * 4 + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(ABUF + 1792 * 4 + 1024, ABUF + 1792 * 5), (FL + 224 * 4 + 128, FL + 224 * 5)] ∧
      Call s Entry.blkt [] ret tail m [] m' Gas.blkt := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.blk, Stack.leaf] at this; omega
  obtain ⟨m', hpost, hfr, hreach⟩ := run hs htail hr.jumpdest hr.small m (j0 := 4) (N := 3)
    (abp0 := 28672) (flp0 := 32256) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    (by omega)
  refine ⟨m', fun S _ hKS => ?_, by simpa [ABUF, FL] using hfr, ?_⟩
  · obtain ⟨h1, h2⟩ := hpost S hKS
    refine ⟨fun i hi hi' => ?_, fun g hg hg' => ?_⟩
    · have := h1 (i - 32) (by omega)
      rw [show 8 * 4 + (i - 32) = i by omega, show 28672 + 32 * (i - 32) = ABUF + 1792 * 4 + 32 * i by
        simp only [ABUF]; omega] at this
      exact this
    · have := h2 (g - 4) (by omega)
      rw [show 4 + (g - 4) = g by omega, show 32256 + 32 * (g - 4) = FL + 224 * 4 + 32 * g by
        simp only [FL]; omega] at this
      exact this
  · rw [call_iff]
    have he := ent_blkt hs htail ret m
    simp only [List.nil_append, Entry.blkt, Gas.blkt]
    exact (he.trans (by simpa using hreach)).mono (by norm_num)

end MlDsaOpt44.Proofs
