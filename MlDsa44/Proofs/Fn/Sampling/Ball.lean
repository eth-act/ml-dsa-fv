import MlDsa44.Proofs.Fn.Sampling.BallBlocks
import MlDsa44.Proofs.Math.Sampling.Ball
set_option warningAsError true
/-!
# `sampleInBall`: the loop

Iteration `k` of the bytecode loop (position `p = 8 + k`) is `ballStep bs · p`;
the memory after `k` iterations is `ballMem m0 bs k`, where `m0` is the memory
after `zeroPoly(CH)`. Per-iteration cost: 256 (accept), 119 (reject), 77
(all 39 placed); worst case 18 + zeroPoly + 7 + 39·256 + 225·119 + 59.
-/

namespace MlDsa44.Proofs.Sampling

open EvmSemantics
open EvmSemantics.EVM

/-- The sign bit for index `i` as the bytecode computes it. -/
def ballSg (bs : ByteArray) (i : Nat) : Nat := bs[(i - 217) / 8]!.toNat / 2 ^ ((i - 217) % 8) &&& 1

theorem ballSg_le (bs : ByteArray) (i : Nat) : ballSg bs i ≤ 1 := by
  unfold ballSg; rw [Nat.and_one_is_mod]; omega

/-- `1 + sg (q − 2)` is the stored form of the sign. -/
theorem ballSign_mod (bs : ByteArray) (i : Nat) (hi : 217 ≤ i) :
    ((1 + ballSg bs i * 8380415 : Nat) : Int) = ballSign bs i % (Fips204.q : Int) := by
  unfold ballSg ballSign Fips204.bit
  rw [Nat.and_one_is_mod, show i + Fips204.tau - 256 = i - 217 by simp only [Fips204.tau]; omega]
  have := Nat.mod_lt (bs[(i - 217) / 8]!.toNat / 2 ^ ((i - 217) % 8)) (show 0 < 2 by decide)
  split
  · rename_i h; rw [h]; decide
  · have h0 : bs[(i - 217) / 8]!.toNat / 2 ^ ((i - 217) % 8) % 2 = 0 := by omega
    rw [h0]; decide

/-- Memory after `k` iterations, from the zeroed memory `m0`. -/
def ballMem (m0 : ByteArray) (bs : ByteArray) : Nat → ByteArray
  | 0 => m0
  | k + 1 =>
    if (ballFold bs k).2 < 256 ∧ bs[8 + k]!.toNat ≤ (ballFold bs k).2 then
      ballWrite (ballMem m0 bs k) (ballFold bs k).2 bs[8 + k]!.toNat (ballSg bs (ballFold bs k).2)
    else ballMem m0 bs k

theorem frame_CH {m M : ByteArray} (h : FrameExcept m M [(CH, CH + POLY)]) (a : Nat)
    (ha : a + 1 ≤ CH ∨ CH + POLY ≤ a) : byteAt M a = byteAt m a :=
  Infra.FrameExcept.byteAt h (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true]; omega)

theorem frame_CH_mstore (M : ByteArray) (x v : Nat) (hx : x < 256) :
    FrameExcept M (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) (43488 + x * 32))
      [(CH, CH + POLY)] := by
  apply Infra.FrameExcept.mono (Infra.FrameExcept.mstore _ _ _)
  intro r hr
  refine ⟨(CH, CH + POLY), by simp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only [CH, POLY]; omega

theorem ballMem_inv (m0 bs : ByteArray)
    (hm0 : ∀ x, x < 256 → word m0 (CH + 32 * x) = 0) : ∀ k,
    FrameExcept m0 (ballMem m0 bs k) [(CH, CH + POLY)] ∧
      ∀ x, x < 256 →
        (word (ballMem m0 bs k) (CH + 32 * x) : Int) = (ballFold bs k).1[x]! % (Fips204.q : Int)
  | 0 => ⟨Infra.FrameExcept.refl _ _, fun x hx => by
      simp only [ballMem]; rw [hm0 x hx]; simp [ballFold_zero, Fips204.zeroPoly, hx]⟩
  | k + 1 => by
    obtain ⟨hf, hw⟩ := ballMem_inv m0 bs hm0 k
    obtain ⟨hsz, hi1, -, -⟩ := ballFold_inv bs k
    simp only [ballMem, ballFold_succ, ballStep]
    split
    · rename_i h
      obtain ⟨hi, hj⟩ := h
      set i := (ballFold bs k).2
      set j := bs[8 + k]!.toNat
      set c := (ballFold bs k).1
      refine ⟨?_, fun x hx => ?_⟩
      · have := Infra.FrameExcept.trans (Infra.FrameExcept.trans hf
          (frame_CH_mstore (ballMem m0 bs k) i (word (ballMem m0 bs k) (43488 + j * 32)) hi))
          (frame_CH_mstore _ j (1 + ballSg bs i * 8380415) (by omega))
        exact Infra.FrameExcept.mono this (fun r hr => ⟨(CH, CH + POLY), by simp, by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl <;> omega⟩)
      · simp only [ballWrite, ballCopy, ballSet]
        rw [getElem!_set!, getElem!_set!, size_set!, hsz]
        have hCH : ∀ y, CH + 32 * y = 43488 + y * 32 := fun y => by simp only [CH]; omega
        by_cases hxj : x = j
        · subst hxj
          rw [if_pos ⟨rfl, by omega⟩, hCH, Infra.word_mstore _ _ _ (by
            have := ballSg_le bs i; omega)]
          exact ballSign_mod bs i hi1
        · rw [if_neg (fun h => hxj h.1), hCH,
            Infra.word_mstore_disjoint _ _ (by omega)]
          by_cases hxi : x = i
          · subst hxi
            rw [if_pos ⟨rfl, by omega⟩, Infra.word_mstore _ _ _ (Infra.word_lt _ _), ← hCH]
            exact hw j (by omega)
          · rw [if_neg (fun h => hxi h.1), Infra.word_mstore_disjoint _ _ (by omega), ← hCH]
            exact hw x hx
    · exact ⟨hf, hw⟩

/-- Per-iteration cost. -/
def ballCost (bs : ByteArray) (k : Nat) : Nat :=
  if (ballFold bs k).2 < 256 then (if bs[8 + k]!.toNat ≤ (ballFold bs k).2 then 256 else 119)
  else 77

theorem ballCost_sum (bs : ByteArray) : ∀ n,
    ((List.range n).map (ballCost bs)).sum + 137 * 217 ≤ 119 * n + 137 * (ballFold bs n).2
  | 0 => by simp [ballFold_zero]
  | n + 1 => by
    have ih := ballCost_sum bs n
    rw [List.range_succ, List.map_append, List.sum_append, ballFold_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ballCost, ballStep]
    by_cases h1 : (ballFold bs n).2 < 256
    · by_cases h2 : bs[8 + n]!.toNat ≤ (ballFold bs n).2
      · simp only [h1, h2, and_self, ↓reduceIte]; omega
      · simp only [h1, h2, and_false, ↓reduceIte]; omega
    · simp only [h1, false_and, ↓reduceIte]; omega

theorem sampleInBall_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sampleInBall ret tail) {m : ByteArray} {bs : ByteArray}
    (hbs : BytesAt m XOF bs) (hsize : bs.size = Fips204.sampleInBallLimit)
    {m0 : ByteArray} {G : Nat} (hm0 : PolyAt m0 CH Fips204.zeroPoly)
    (hf0 : FrameExcept m m0 [(CH, CH + POLY)])
    (hz : Infra.Reach (callState s 3067 (wd 43488 :: wd 3648 :: wd 0 :: wd ret :: tail) m)
      (callState s 3648 (wd 0 :: wd ret :: tail) m0) G) :
    ∃ m', (∃ c', PolyAt m' CH c' ∧ Reduced c') ∧
      (∀ c, Fips204.sampleInBallOf bs = some c →
        PolyAt m' CH (c.map (· % (Fips204.q : Int))) ∧ Reduced (c.map (· % (Fips204.q : Int)))) ∧
      FrameExcept m m' [(CH, CH + POLY)] ∧
      Call s Entry.sampleInBall [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m'
        (G + 36843) := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.sampleInBall, Stack.zeroPoly, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := by
    have := hs.small; norm_num at this; exact this
  have hsized : 2535 ≤ s.activeWords.toNat := hs.sized
  simp only [Fips204.sampleInBallLimit] at hsize
  have hm0' : ∀ x, x < 256 → word m0 (CH + 32 * x) = 0 := fun x hx => by
    have := hm0.2 x hx; simp [Fips204.zeroPoly, hx] at this; exact_mod_cast this
  let M : Nat → ByteArray := ballMem m0 bs
  have hframe : ∀ k, FrameExcept m (M k) [(CH, CH + POLY)] := fun k =>
    Infra.FrameExcept.mono (Infra.FrameExcept.trans hf0 (ballMem_inv m0 bs hm0' k).1)
      (fun r hr => ⟨(CH, CH + POLY), by simp, by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl <;> omega⟩)
  have hxof : ∀ (M' : ByteArray), FrameExcept m M' [(CH, CH + POLY)] → ∀ q', q' < 272 →
      byteAt M' (77280 + q' + 0) = bs[q']!.toNat := by
    intro M' hM' q' hq'
    rw [frame_CH hM' _ (by simp only [CH, POLY]; omega)]
    have := hbs q' (by omega)
    simpa only [XOF, Nat.add_zero] using this
  let I : Nat → State := fun k => ballSt s ret tail (8 + k) (ballFold bs k).2 (M k)
  have hbody : ∀ k, k < 264 → Infra.Reach (I k) (I (k + 1)) (ballCost bs k) := by
    intro k hk
    obtain ⟨-, hi1, hi2, -⟩ := ballFold_inv bs k
    have hj := hxof (M k) (hframe k) (8 + k) (by omega)
    simp only [I, M, ballCost, ballMem, ballFold_succ, ballStep]
    rw [show 8 + (k + 1) = 8 + k + 1 by omega]
    by_cases h1 : (ballFold bs k).2 < 256
    · by_cases h2 : bs[8 + k]!.toNat ≤ (ballFold bs k).2
      · simp only [h1, h2, and_self, ↓reduceIte]
        have hc : FrameExcept m (ballCopy (M k) (ballFold bs k).2 bs[8 + k]!.toNat)
            [(CH, CH + POLY)] :=
          Infra.FrameExcept.mono (Infra.FrameExcept.trans (hframe k)
            (frame_CH_mstore (M k) _ _ h1))
            (fun r hr => ⟨(CH, CH + POLY), by simp, by
              simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
                or_false] at hr
              rcases hr with rfl | rfl <;> omega⟩)
        have hb := hxof _ hc (((ballFold bs k).2 - 217) / 8) (by omega)
        exact ball_accept hs htail haw hsized (M k) (8 + k) _ (by omega) h1 hi1 _ hj h2 _ hb
          (UInt8.toNat_lt _) _ rfl (ballSg_le bs _)
      · simp only [h1, h2, and_false, ↓reduceIte]
        exact ball_reject hs htail haw hsized (M k) (8 + k) _ (by omega) h1 _ hj (by omega)
          (UInt8.toNat_lt _)
    · simp only [h1, false_and, ↓reduceIte]
      exact ball_skip hs htail (M k) (8 + k) _ (by omega) (by omega) hi2
  obtain ⟨hsz, -, hi, -⟩ := ballFold_inv bs 264
  have hexit := ball_exit hs htail hr (M 264) _ hi
  have hcost := ballCost_sum bs 264
  have hloop := Infra.Reach.loopSum (I := I) 264 hbody
  have hall := (((ball_entry hs htail m).trans hz).trans
    ((ball_start hs htail m0).trans hloop)).trans hexit
  obtain ⟨-, hw⟩ := ballMem_inv m0 bs hm0' 264
  have hpoly : PolyAt (M 264) CH ((ballFold bs 264).1.map (· % (Fips204.q : Int))) ∧
      Reduced ((ballFold bs 264).1.map (· % (Fips204.q : Int))) := by
    refine ⟨⟨by simp [hsz], fun x hx => ?_⟩, fun x hx => ?_⟩
    · rw [hw x hx]; simp [hsz, hx]
    · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        hsz, hx, getElem?_pos, Option.map_some, Option.getD_some]
      exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  refine ⟨M 264, ⟨_, hpoly⟩, fun c hc => ?_, hframe 264, ?_⟩
  · rw [sampleInBallOf_eq] at hc
    split at hc
    · exact absurd hc (by simp)
    · simp only [Option.some.injEq] at hc
      subst hc
      exact hpoly
  · rw [Infra.call_iff, Entry.sampleInBall]
    have hflag : flag (Fips204.sampleInBallOf bs).isSome =
        wd (if (ballFold bs 264).2 < 256 then 0 else 1) := by
      rw [sampleInBallOf_eq]
      by_cases h : (ballFold bs 264).2 < 256 <;> simp [h, flag]
    rw [hflag]
    refine (hall.mono ?_).of_eq rfl rfl
    have hi' : (ballFold bs 264).2 ≤ 256 := hi
    omega

end MlDsa44.Proofs.Sampling
