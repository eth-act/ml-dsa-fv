import MlDsa44.Proofs.Infra
import MlDsa44.Proofs.Math.Ntt.Model
/-!
# Shared helpers for the `ntt` / `nttInv` proofs

* `Rep m0 p M g`: memory `M` holds the reduced polynomial `g` at `p` and agrees
  with `m0` outside the polynomial;
* `reach_iter`/`reach_iterU`: loops whose memory is carried by an invariant
  (the memory after `i` iterations is only known through `P i`);
* `word_mstore2`: two word stores inside a polynomial;
* `bflyMemN`/`bflyMemI`/`scMem`: the memory after one loop body of `ntt`,
  `nttInv` and the final scaling, in the shape `evm_block` produces, with the
  `Rep` transport lemmas `rep_bflyN`/`rep_bflyI`/`rep_sc`.
-/

namespace MlDsa44.Proofs.NttProof

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.NttModel
open MlDsa44.Fips204 (Poly zetas)

/-- `M` holds the reduced polynomial `g` at `p` and agrees with `m0` elsewhere. -/
def Rep (m0 : ByteArray) (p : Nat) (M : ByteArray) (g : Poly) : Prop :=
  PolyAt M p g ∧ Reduced g ∧ FrameExcept m0 M [(p, p + POLY)]

/-! ## Loops with an invariant on memory -/

theorem reach_iter {S : Nat → ByteArray → State} {P : Nat → ByteArray → Prop} {c : Nat → Nat} :
    ∀ n, (∀ i M, i < n → P i M → ∃ M', P (i + 1) M' ∧ Infra.Reach (S i M) (S (i + 1) M') (c i)) →
      ∀ M, P 0 M → ∃ M', P n M' ∧ Infra.Reach (S 0 M) (S n M') ((List.range n).map c).sum
  | 0, _, M, hM => ⟨M, hM, by simpa using Infra.Reach.refl (S 0 M)⟩
  | n + 1, h, M, hM => by
    obtain ⟨M₁, hP₁, hR₁⟩ := reach_iter n (fun i M hi => h i M (by omega)) M hM
    obtain ⟨M₂, hP₂, hR₂⟩ := h n M₁ (by omega) hP₁
    exact ⟨M₂, hP₂, by simpa [List.range_succ] using hR₁.trans hR₂⟩

theorem reach_iterU {S : Nat → ByteArray → State} {P : Nat → ByteArray → Prop} {c : Nat} (n : Nat)
    (h : ∀ i M, i < n → P i M → ∃ M', P (i + 1) M' ∧ Infra.Reach (S i M) (S (i + 1) M') c)
    (M : ByteArray) (hM : P 0 M) : ∃ M', P n M' ∧ Infra.Reach (S 0 M) (S n M') (n * c) := by
  obtain ⟨M', hP, hR⟩ := reach_iter (c := fun _ => c) n h M hM
  refine ⟨M', hP, hR.mono (le_of_eq ?_)⟩
  simp [List.map_const', List.sum_replicate]

/-! ## Words -/

theorem addMod_q (a b : UInt256) :
    UInt256.addMod a b (UInt256.ofNat 8380417) = UInt256.ofNat ((a.toNat + b.toNat) % 8380417) := rfl

theorem mulMod_q (a b : UInt256) :
    UInt256.mulMod a b (UInt256.ofNat 8380417) = UInt256.ofNat ((a.toNat * b.toNat) % 8380417) := rfl

/-! ## Arrays -/

theorem getElem!_set! (a : Array Int) (i j : Nat) (v : Int) (h : j < a.size) :
    (a.set! j v)[i]! = if i = j then v else a[i]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij, Ne.symm hij]

theorem size_set! (a : Array Int) (j : Nat) (v : Int) : (a.set! j v).size = a.size := by
  simp [Array.set!]

/-! ## Memory -/

theorem word_mstore2 (M : ByteArray) (p a b va vb i : Nat) (hab : a ≠ b) (ha : va < 2 ^ 256)
    (hb : vb < 2 ^ 256) :
    word (MachineState.writeBytes
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded vb 32) (p + b * 32))
        (Data.Bytes.natToBytesPadded va 32) (p + a * 32)) (p + 32 * i) =
      if i = a then va else if i = b then vb else word M (p + 32 * i) := by
  by_cases hia : i = a
  · subst hia
    rw [if_pos rfl, show p + 32 * i = p + i * 32 by omega, Infra.word_mstore _ _ _ ha]
  · rw [if_neg hia, Infra.word_mstore_disjoint _ _ (by omega)]
    by_cases hib : i = b
    · subst hib
      rw [if_pos rfl, show p + 32 * i = p + i * 32 by omega, Infra.word_mstore _ _ _ hb]
    · rw [if_neg hib, Infra.word_mstore_disjoint _ _ (by omega)]

theorem frame_mstore2 (M : ByteArray) (p a b va vb : Nat) (ha : a < 256) (hb : b < 256) :
    FrameExcept M (MachineState.writeBytes
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded vb 32) (p + b * 32))
        (Data.Bytes.natToBytesPadded va 32) (p + a * 32)) [(p, p + POLY)] := by
  apply Infra.FrameExcept.mono (Infra.FrameExcept.trans (Infra.FrameExcept.mstore _ _ _)
    (Infra.FrameExcept.mstore _ _ _))
  intro r hr
  refine ⟨(p, p + POLY), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [POLY] <;> omega

theorem frame_mstore1 (M : ByteArray) (p a va : Nat) (ha : a < 256) :
    FrameExcept M (MachineState.writeBytes M (Data.Bytes.natToBytesPadded va 32) (p + a * 32))
      [(p, p + POLY)] := by
  apply Infra.FrameExcept.mono (Infra.FrameExcept.mstore _ _ _)
  intro r hr
  refine ⟨(p, p + POLY), by simp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only [POLY]; omega

theorem zetaTable_of_rep {m0 M : ByteArray} {p : Nat} {g : Poly} (hR : Rep m0 p M g)
    (hz : ZetaTable m0) (hp : ZETA + POLY ≤ p) : ZetaTable M :=
  Infra.ZetaTable.frame hz hR.2.2 (by simp; omega)

theorem zetas_lt (k : Nat) : zetas k < (Fips204.q : Int) ∧ 0 ≤ zetas k := by
  unfold zetas
  constructor
  · exact_mod_cast Nat.mod_lt _ (by decide)
  · exact Int.natCast_nonneg _

/-- The value of an entry of a `Rep` polynomial, as a `Nat` word below `q`. -/
theorem rep_word {m0 M : ByteArray} {p : Nat} {g : Poly} (hR : Rep m0 p M g) {i : Nat}
    (hi : i < 256) : (word M (p + i * 32) : Int) = g[i]! ∧ word M (p + i * 32) < 8380417 := by
  have h1 := hR.1.2 i hi
  have h2 := hR.2.1 i hi
  rw [show p + i * 32 = p + 32 * i by omega]
  refine ⟨h1, ?_⟩
  have : (word M (p + 32 * i) : Int) < 8380417 := by rw [h1]; exact h2.2
  omega

/-! ## `ntt` butterfly -/

/-- Memory after one `ntt` butterfly at `j`, `j + len` with twiddle `z`. -/
def bflyMemN (M : ByteArray) (p j len z : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes M
      (Data.Bytes.natToBytesPadded
        ((word M (p + j * 32) + (8380417 - z * word M (p + j * 32 + len * 32) % 8380417)) %
          8380417) 32)
      (p + j * 32 + len * 32))
    (Data.Bytes.natToBytesPadded
      ((word M (p + j * 32) + z * word M (p + j * 32 + len * 32) % 8380417) % 8380417) 32)
    (p + j * 32)

theorem bfN_get (len : Nat) (z : Int) (g : Poly) (a i : Nat) (hg : g.size = 256)
    (ha : a + len < 256) (hlen : 0 < len) :
    (bfN len z g a)[i]! =
      if i = a then (g[a]! + z * g[a + len]! % Fips204.q) % Fips204.q
      else if i = a + len then (g[a]! - z * g[a + len]! % Fips204.q) % Fips204.q else g[i]! := by
  unfold bfN
  rw [getElem!_set! _ _ _ _ (by rw [size_set!]; omega), getElem!_set! _ _ _ _ (by omega),
    getElem!_set! _ _ _ _ (by omega)]
  have hl : len ≠ 0 := by omega
  by_cases h1 : i = a
  · subst h1; simp [hl]
  · simp [h1]

theorem rep_bflyN {m0 M : ByteArray} {p : Nat} {g : Poly} (hR : Rep m0 p M g) {j len z : Nat}
    (hj : j + len < 256) (hlen : 0 < len) :
    Rep m0 p (bflyMemN M p j len z) (bfN len (z : Int) g j) := by
  have hg : g.size = 256 := hR.1.1
  obtain ⟨hx, hxq⟩ := rep_word hR (i := j) (by omega)
  obtain ⟨hy, hyq⟩ := rep_word hR (i := j + len) hj
  rw [show p + (j + len) * 32 = p + j * 32 + len * 32 by omega] at hy hyq
  have hsize : (bfN len (z : Int) g j).size = 256 := by simp [bfN, hg]
  have hval : ∀ i, (bfN len (z : Int) g j)[i]! =
      if i = j then (((word M (p + j * 32) + z * word M (p + j * 32 + len * 32) % 8380417) %
          8380417 : Nat) : Int)
      else if i = j + len then (((word M (p + j * 32) +
          (8380417 - z * word M (p + j * 32 + len * 32) % 8380417)) % 8380417 : Nat) : Int)
      else g[i]! := by
    intro i
    rw [bfN_get len _ g j i hg hj hlen, ← hx, ← hy]
    generalize word M (p + j * 32) = x at *
    generalize word M (p + j * 32 + len * 32) = y at *
    have ht : z * y % 8380417 < 8380417 := Nat.mod_lt _ (by decide)
    simp only [Fips204.q]
    split_ifs
    · push_cast; rfl
    · have hle : z * y % 8380417 ≤ 8380417 := by omega
      push_cast [Nat.cast_sub hle]
      generalize (z : Int) * (y : Int) = k
      omega
    · rfl
  have hmem : bflyMemN M p j len z = MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
        ((word M (p + j * 32) + (8380417 - z * word M (p + j * 32 + len * 32) % 8380417)) %
          8380417) 32) (p + (j + len) * 32))
      (Data.Bytes.natToBytesPadded
        ((word M (p + j * 32) + z * word M (p + j * 32 + len * 32) % 8380417) % 8380417) 32)
      (p + j * 32) := by
    rw [bflyMemN, show p + (j + len) * 32 = p + j * 32 + len * 32 by omega]
  refine ⟨⟨hsize, fun i hi => ?_⟩, fun i hi => ?_, ?_⟩
  · rw [hmem, word_mstore2 _ _ _ _ _ _ _ (by omega) (by omega) (by omega), hval i]
    split_ifs
    · rfl
    · rfl
    · exact hR.1.2 i hi
  · rw [hval i]
    split_ifs
    · constructor
      · exact Int.natCast_nonneg _
      · simp only [Fips204.q]; exact_mod_cast Nat.mod_lt _ (by decide)
    · constructor
      · exact Int.natCast_nonneg _
      · simp only [Fips204.q]; exact_mod_cast Nat.mod_lt _ (by decide)
    · exact hR.2.1 i hi
  · rw [hmem]
    exact Infra.FrameExcept.mono (Infra.FrameExcept.trans hR.2.2
      (frame_mstore2 M p j (j + len) _ _ (by omega) hj)) (by simp)

/-! ## `nttInv` butterfly -/

/-- Memory after one `nttInv` butterfly at `j`, `j + len` with twiddle `z`. -/
def bflyMemI (M : ByteArray) (p j len z : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes M
      (Data.Bytes.natToBytesPadded
        ((word M (p + j * 32) + word M (p + j * 32 + len * 32)) % 8380417) 32)
      (p + j * 32))
    (Data.Bytes.natToBytesPadded
      (z * ((word M (p + j * 32) + (8380417 - word M (p + j * 32 + len * 32))) % 8380417) %
        8380417) 32)
    (p + j * 32 + len * 32)

theorem bfI_get (len : Nat) (z : Int) (g : Poly) (a i : Nat) (hg : g.size = 256)
    (ha : a + len < 256) (hlen : 0 < len) :
    (bfI len z g a)[i]! =
      if i = a + len then z * ((g[a]! - g[a + len]!) % Fips204.q) % Fips204.q
      else if i = a then (g[a]! + g[a + len]!) % Fips204.q else g[i]! := by
  have hl0 : len ≠ 0 := by omega
  unfold bfI
  simp (disch := (simp only [size_set!, hg]; omega)) only [getElem!_set!]
  by_cases h1 : i = a + len
  · subst h1; simp [hl0]
  · by_cases h2 : i = a
    · subst h2; simp [hl0]
    · simp [h1, h2]

theorem rep_bflyI {m0 M : ByteArray} {p : Nat} {g : Poly} (hR : Rep m0 p M g) {j len z : Nat}
    {zI : Int} (hzI : (z : Int) % 8380417 = zI % 8380417) (hj : j + len < 256) (hlen : 0 < len) :
    Rep m0 p (bflyMemI M p j len z) (bfI len zI g j) := by
  have hg : g.size = 256 := hR.1.1
  obtain ⟨hx, hxq⟩ := rep_word hR (i := j) (by omega)
  obtain ⟨hy, hyq⟩ := rep_word hR (i := j + len) hj
  rw [show p + (j + len) * 32 = p + j * 32 + len * 32 by omega] at hy hyq
  have hsize : (bfI len zI g j).size = 256 := by simp [bfI, hg]
  have hval : ∀ i, (bfI len zI g j)[i]! =
      if i = j + len then ((z * ((word M (p + j * 32) +
          (8380417 - word M (p + j * 32 + len * 32))) % 8380417) % 8380417 : Nat) : Int)
      else if i = j then (((word M (p + j * 32) + word M (p + j * 32 + len * 32)) %
          8380417 : Nat) : Int)
      else g[i]! := by
    intro i
    rw [bfI_get len _ g j i hg hj hlen, ← hx, ← hy]
    generalize word M (p + j * 32) = x at *
    generalize word M (p + j * 32 + len * 32) = y at *
    simp only [Fips204.q, Nat.cast_ofNat]
    split_ifs
    · have hle : y ≤ 8380417 := by omega
      have hX : (((x + (8380417 - y)) % 8380417 : Nat) : Int) = ((x : Int) - y) % 8380417 := by
        push_cast [Nat.cast_sub hle]; omega
      rw [Int.natCast_mod, Nat.cast_mul, hX]
      simp only [Nat.cast_ofNat]
      rw [Int.mul_emod, ← hzI, ← Int.mul_emod]
    · push_cast; rfl
    · rfl
  have hmem : bflyMemI M p j len z = MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
        ((word M (p + j * 32) + word M (p + j * 32 + len * 32)) % 8380417) 32) (p + j * 32))
      (Data.Bytes.natToBytesPadded
        (z * ((word M (p + j * 32) + (8380417 - word M (p + j * 32 + len * 32))) % 8380417) %
          8380417) 32)
      (p + (j + len) * 32) := by
    rw [bflyMemI, show p + (j + len) * 32 = p + j * 32 + len * 32 by omega]
  refine ⟨⟨hsize, fun i hi => ?_⟩, fun i hi => ?_, ?_⟩
  · rw [hmem, word_mstore2 _ _ _ _ _ _ _ (by omega) (by omega) (by omega), hval i]
    split_ifs
    · rfl
    · rfl
    · exact hR.1.2 i hi
  · rw [hval i]
    split_ifs
    · constructor
      · exact Int.natCast_nonneg _
      · simp only [Fips204.q]; exact_mod_cast Nat.mod_lt _ (by decide)
    · constructor
      · exact Int.natCast_nonneg _
      · simp only [Fips204.q]; exact_mod_cast Nat.mod_lt _ (by decide)
    · exact hR.2.1 i hi
  · rw [hmem]
    exact Infra.FrameExcept.mono (Infra.FrameExcept.trans hR.2.2
      (frame_mstore2 M p (j + len) j _ _ hj (by omega))) (by simp)

/-! ## Final scaling of `nttInv` -/

/-- Memory after scaling the word at `j`. -/
def scMem (M : ByteArray) (p j : Nat) : ByteArray :=
  MachineState.writeBytes M
    (Data.Bytes.natToBytesPadded (8347681 * word M (p + j * 32) % 8380417) 32) (p + j * 32)

theorem rep_sc {m0 M : ByteArray} {p : Nat} {g : Poly} (hR : Rep m0 p M g) {j : Nat}
    (hj : j < 256) : Rep m0 p (scMem M p j) (scStep g j) := by
  have hg : g.size = 256 := hR.1.1
  obtain ⟨hx, -⟩ := rep_word hR hj
  have hv : 8347681 * word M (p + j * 32) % 8380417 < 8380417 := Nat.mod_lt _ (by decide)
  have hval : ∀ i, (scStep g j)[i]! =
      if i = j then ((8347681 * word M (p + j * 32) % 8380417 : Nat) : Int) else g[i]! := by
    intro i
    rw [scStep, getElem!_set! _ _ _ _ (by omega), ← hx]
    simp only [Fips204.q]
    push_cast
    rfl
  refine ⟨⟨by simp [scStep, hg], fun i hi => ?_⟩, fun i hi => ?_, ?_⟩
  · rw [hval i, scMem]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, show p + 32 * i = p + i * 32 by omega, Infra.word_mstore _ _ _ (by omega)]
    · rw [if_neg hij, Infra.word_mstore_disjoint _ _ (by omega)]
      exact hR.1.2 i hi
  · rw [hval i]
    split_ifs
    · constructor
      · exact Int.natCast_nonneg _
      · simp only [Fips204.q]; exact_mod_cast hv
    · exact hR.2.1 i hi
  · exact Infra.FrameExcept.mono (Infra.FrameExcept.trans hR.2.2 (frame_mstore1 M p j _ hj))
      (by simp)

end MlDsa44.Proofs.NttProof
