import MlDsa44.Proofs.Fn.Sampling.RejBlocks
import MlDsa44.Proofs.Math.Sampling.Rej
set_option warningAsError true
/-!
# `rejSample`: the loop

Iteration `t` of the bytecode loop is `rejStep bs · t`; the memory after `t`
iterations is `rejMem m dst bs t`. Per-iteration cost: 212 (accept),
177 (reject), 77 (count already 256); worst case 5 + 256·212 + 80·177 + 61.
-/

namespace MlDsa44.Proofs.Sampling

open EvmSemantics
open EvmSemantics.EVM

/-- Memory after `t` iterations. -/
def rejMem (m : ByteArray) (dst : Nat) (bs : ByteArray) : Nat → ByteArray
  | 0 => m
  | t + 1 =>
    if (rejFold bs t).2 < 256 ∧ rejZv bs t < Fips204.q then
      MachineState.writeBytes (rejMem m dst bs t)
        (Data.Bytes.natToBytesPadded (rejZv bs t) 32) (dst + (rejFold bs t).2 * 32)
    else rejMem m dst bs t

theorem rejMem_inv (m : ByteArray) (dst : Nat) (bs : ByteArray) : ∀ t,
    FrameExcept m (rejMem m dst bs t) [(dst, dst + POLY)] ∧
      ∀ i, i < (rejFold bs t).2 →
        (word (rejMem m dst bs t) (dst + 32 * i) : Int) = (rejFold bs t).1[i]!
  | 0 => ⟨Infra.FrameExcept.refl m _, fun i hi => by simp [rejFold_zero] at hi⟩
  | t + 1 => by
    obtain ⟨hf, hw⟩ := rejMem_inv m dst bs t
    obtain ⟨hsz, hle, -⟩ := rejFold_inv bs t
    simp only [rejMem, rejFold_succ, rejStep]
    split
    · rename_i h
      have hlt : rejZv bs t < 2 ^ 256 := Nat.lt_trans (rejZv_lt bs t) (by norm_num)
      refine ⟨?_, fun i hi => ?_⟩
      · apply Infra.FrameExcept.mono (Infra.FrameExcept.trans hf (Infra.FrameExcept.mstore _ _ _))
        intro r hr
        refine ⟨(dst, dst + POLY), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl <;> simp only [POLY] <;> omega
      · simp only at hi ⊢
        rw [getElem!_set!]
        by_cases hij : i = (rejFold bs t).2
        · subst hij
          rw [if_pos ⟨rfl, by omega⟩, show dst + 32 * (rejFold bs t).2 = dst + (rejFold bs t).2 * 32
            by omega, Infra.word_mstore _ _ _ hlt]
        · rw [if_neg (fun h => hij h.1), Infra.word_mstore_disjoint _ _ (by omega)]
          exact hw i (by omega)
    · exact ⟨hf, hw⟩

/-- Per-iteration cost. -/
def rejCost (bs : ByteArray) (t : Nat) : Nat :=
  if (rejFold bs t).2 < 256 then (if rejZv bs t < Fips204.q then 212 else 177) else 77

theorem rejCost_sum (bs : ByteArray) : ∀ n,
    ((List.range n).map (rejCost bs)).sum ≤ 177 * n + 35 * (rejFold bs n).2
  | 0 => by simp
  | n + 1 => by
    have ih := rejCost_sum bs n
    rw [List.range_succ, List.map_append, List.sum_append, rejFold_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rejCost, rejStep]
    by_cases h1 : (rejFold bs n).2 < 256
    · by_cases h2 : rejZv bs n < Fips204.q
      · simp only [h1, h2, and_self, ↓reduceIte]; omega
      · simp only [h1, h2, and_false, ↓reduceIte]; omega
    · simp only [h1, false_and, ↓reduceIte]; omega

theorem rejSample_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.rejSample ret tail) {m : ByteArray} {dst : Nat} {bs : ByteArray}
    (hbs : BytesAt m XOF bs) (hsize : bs.size = Fips204.rejNTTPolyLimit)
    (hdst : ZETA + POLY ≤ dst ∧ (dst + POLY ≤ XOF ∨ XOF + 0x420 ≤ dst))
    (hmem : dst + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', (∀ a, Fips204.rejNTTPolyOf bs = some a → PolyAt m' dst a ∧ Reduced a) ∧
      FrameExcept m m' [(dst, dst + POLY)] ∧
      Call s Entry.rejSample [wd dst] ret tail m [flag (Fips204.rejNTTPolyOf bs).isSome] m'
        68498 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.rejSample, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := by
    have := hs.small; norm_num at this; exact this
  have hsized : 2535 ≤ s.activeWords.toNat := by
    have h := hs.sized
    have h' : fixedWords = 2535 := rfl
    omega
  have hdst' : dst + 8192 + 32 ≤ 32 * s.activeWords.toNat := by simpa only [POLY] using hmem
  simp only [Fips204.rejNTTPolyLimit] at hsize
  simp only [ZETA, POLY, XOF] at hdst
  let J : Nat → Nat := fun t => (rejFold bs t).2
  let M : Nat → ByteArray := rejMem m dst bs
  have hbyte : ∀ t, t < 336 → ∀ k, k < 3 →
      byteAt (M t) (77280 + 3 * t + k) = bs[3 * t + k]!.toNat := by
    intro t ht k hk
    rw [Infra.FrameExcept.byteAt (rejMem_inv m dst bs t).1 (by
      simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, POLY]; omega)]
    have := hbs (3 * t + k) (by omega)
    simpa only [XOF, Nat.add_assoc] using this
  have hz : ∀ t, t < 336 → rejZ (M t) t = rejZv bs t := by
    intro t ht
    simp only [rejZ, rejZv]
    rw [hbyte t ht 0 (by omega), hbyte t ht 1 (by omega), hbyte t ht 2 (by omega)]
    rfl
  let I : Nat → State := fun t => rejSt s ret tail dst t (J t) (M t)
  have hbody : ∀ t, t < 336 → Infra.Reach (I t) (I (t + 1)) (rejCost bs t) := by
    intro t ht
    have hle := (rejFold_inv bs t).2.1
    simp only [I, J, M, rejCost, rejMem, rejFold_succ, rejStep]
    by_cases h1 : (rejFold bs t).2 < 256
    · by_cases h2 : rejZv bs t < Fips204.q
      · simp only [h1, h2, and_self, ↓reduceIte]
        exact rej_accept hs htail haw hsized hdst' _ t _ _ ht h1 (hz t ht) h2
      · simp only [h1, h2, and_false, ↓reduceIte]
        exact rej_reject hs htail haw hsized _ t _ _ ht h1 (hz t ht) h2 (rejZv_lt bs t)
    · simp only [h1, false_and, ↓reduceIte]
      exact rej_skip hs htail _ t _ ht (by omega) hle
  have hJ := (rejFold_inv bs 336).2.1
  have hexit := rej_exit hs htail hr.jumpdest hr.small (dst := dst) (M 336) (J 336) hJ
  have hcost := rejCost_sum bs 336
  have hloop := Infra.Reach.loopSum (I := I) 336 hbody
  have hall := ((rej_entry hs htail dst m).trans hloop).trans hexit
  obtain ⟨hf, hw⟩ := rejMem_inv m dst bs 336
  obtain ⟨hsz, -, hred⟩ := rejFold_inv bs 336
  refine ⟨M 336, fun a ha => ?_, hf, ?_⟩
  · rw [rejNTTPolyOf_eq] at ha
    split at ha
    · exact absurd ha (by simp)
    · rename_i hn
      simp only [Option.some.injEq] at ha
      subst ha
      refine ⟨⟨hsz, fun i hi => hw i (by omega)⟩, hred⟩
  · rw [Infra.call_iff, Entry.rejSample]
    have hflag : flag (Fips204.rejNTTPolyOf bs).isSome = wd (if J 336 < 256 then 0 else 1) := by
      rw [rejNTTPolyOf_eq]
      by_cases h : (rejFold bs 336).2 < 256 <;> simp [h, J, flag]
    rw [hflag]
    refine (hall.mono ?_).of_eq ?_ ?_
    · have hJ' : (rejFold bs 336).2 ≤ 256 := hJ
      omega
    · rfl
    · rfl

end MlDsa44.Proofs.Sampling
