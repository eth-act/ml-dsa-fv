import MlDsa44.Proofs.Math.Ntt.Model
import Mathlib.Data.ZMod.Basic
/-!
# Algorithms 41/42 as linear maps over `ZMod q`

Every layer of `Fips204.ntt`/`nttInv` performs disjoint butterflies, so its
result has a closed form per index (`CL`): block `i / (2 len)`, offset
`i % (2 len)`. Mapping coefficients to `F = ZMod q` (all writes are `% q`)
turns `ntt` into `Nf u 8` and `nttInv` into `8347681 · If u 8`, where `Nf`/`If`
iterate the closed-form layers on functions `ℕ → F`.
-/

namespace MlDsaOpt44.Proofs.NttConv

open MlDsa44 Fips204 MlDsa44.Proofs.NttModel

abbrev F := ZMod 8380417

/-- Coefficient `i` of an array, in `ZMod q`. -/
def toF (w : Poly) (i : Nat) : F := ((w[i]! : Int) : F)

theorem cast_emod (x : Int) : (((x % (q : Int) : Int)) : F) = (x : F) := by
  show (((x % ((8380417 : Nat) : Int) : Int)) : ZMod 8380417) = (x : ZMod 8380417)
  exact ZMod.intCast_mod x 8380417

theorem getElem!_set (a : Array Int) (i j : Nat) (v : Int) (h : j < a.size) :
    (a.set! j v)[i]! = if i = j then v else a[i]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij, Ne.symm hij]

/-- Closed form of one layer. -/
def CL (len : Nat) (Lo Hi : F → F → F → F) (z : Nat → F) (u : Nat → F) (i : Nat) : F :=
  if i % (2 * len) < len then Lo (z (i / (2 * len))) (u i) (u (i + len))
  else Hi (z (i / (2 * len))) (u (i - len)) (u i)

theorem dm {len b o : Nat} (ho : o < 2 * len) :
    (2 * len * b + o) / (2 * len) = b ∧ (2 * len * b + o) % (2 * len) = o :=
  (Nat.div_mod_unique (by omega)).2 ⟨Nat.add_comm _ _, ho⟩

theorem CL_lo {len : Nat} {Lo Hi : F → F → F → F} {z : Nat → F} {u : Nat → F} {b o : Nat}
    (ho : o < len) :
    CL len Lo Hi z u (2 * len * b + o) = Lo (z b) (u (2 * len * b + o)) (u (2 * len * b + o + len)) := by
  obtain ⟨h1, h2⟩ := dm (len := len) (b := b) (o := o) (by omega)
  unfold CL; rw [h1, h2, if_pos ho]

theorem CL_hi {len : Nat} {Lo Hi : F → F → F → F} {z : Nat → F} {u : Nat → F} {b o : Nat}
    (ho1 : len ≤ o) (ho2 : o < 2 * len) :
    CL len Lo Hi z u (2 * len * b + o) = Hi (z b) (u (2 * len * b + o - len)) (u (2 * len * b + o)) := by
  obtain ⟨h1, h2⟩ := dm (len := len) (b := b) (o := o) ho2
  unfold CL; rw [h1, h2, if_neg (by omega)]

/-- Index decomposition with the block below `nb`. -/
theorem decomp {len nb i : Nat} (hlen : 0 < len) (hnb : 2 * len * nb = 256) (hi : i < 256) :
    ∃ b o, i = 2 * len * b + o ∧ o < 2 * len ∧ b < nb := by
  refine ⟨i / (2 * len), i % (2 * len), (Nat.div_add_mod i (2 * len)).symm,
    Nat.mod_lt _ (by omega), ?_⟩
  by_contra h
  have h1 : 2 * len * nb ≤ 2 * len * (i / (2 * len)) := Nat.mul_le_mul_left _ (by omega)
  have h2 := Nat.div_add_mod i (2 * len)
  omega

theorem block_le {len nb b : Nat} (hnb : 2 * len * nb = 256) (hb : b < nb) :
    2 * len * b + 2 * len ≤ 256 := by
  have : 2 * len * (b + 1) ≤ 2 * len * nb := Nat.mul_le_mul_left _ hb
  rw [Nat.mul_succ] at this; omega

theorem CL_congr {len nb : Nat} (hlen : 0 < len) (hnb : 2 * len * nb = 256)
    {Lo Hi : F → F → F → F} {z : Nat → F} {u v : Nat → F} (h : ∀ j, j < 256 → u j = v j)
    {i : Nat} (hi : i < 256) : CL len Lo Hi z u i = CL len Lo Hi z v i := by
  obtain ⟨b, o, rfl, ho, hb⟩ := decomp hlen hnb hi
  have := block_le hnb hb
  by_cases h1 : o < len
  · rw [CL_lo h1, CL_lo h1, h _ hi, h _ (by omega)]
  · rw [CL_hi (by omega) ho, CL_hi (by omega) ho, h _ hi, h _ (by omega)]

/-! ## Folding one layer -/

/-- The first `b` blocks of a layer (generic butterfly `op`). -/
def layerG (op : Int → Poly → Nat → Poly) (len : Nat) (zf : Nat → Int) (w : Poly) : Nat → Poly
  | 0 => w
  | b + 1 => (List.range' (2 * len * b) len).foldl (op (zf b)) (layerG op len zf w b)

/-- Pointwise effect of one butterfly at `a`, `a + len`. -/
def BfSpec (op : Int → Poly → Nat → Poly) (len : Nat) (Lo Hi : F → F → F → F) : Prop :=
  ∀ z w a, w.size = 256 → a + len < 256 → (op z w a).size = 256 ∧
    ∀ i, toF (op z w a) i = if i = a then Lo (z : F) (toF w a) (toF w (a + len))
      else if i = a + len then Hi (z : F) (toF w a) (toF w (a + len)) else toF w i

/-- Processed indices after `b0` blocks and `k` butterflies of block `b0`. -/
@[reducible] def Done (len b0 k b o : Nat) : Prop :=
  b < b0 ∨ (b = b0 ∧ (o < k ∨ (len ≤ o ∧ o < len + k)))

def St (len b0 k : Nat) (Lo Hi : F → F → F → F) (z : Nat → F) (w R : Poly) : Prop :=
  R.size = 256 ∧ ∀ b o, o < 2 * len → 2 * len * b + o < 256 →
    toF R (2 * len * b + o) =
      if Done len b0 k b o then CL len Lo Hi z (toF w) (2 * len * b + o)
      else toF w (2 * len * b + o)

theorem st_step {op : Int → Poly → Nat → Poly} {len nb : Nat} {Lo Hi : F → F → F → F}
    (hbf : BfSpec op len Lo Hi) (hlen : 0 < len) (hnb : 2 * len * nb = 256)
    (zf : Nat → Int) (w R : Poly) {b0 k : Nat} (hb0 : b0 < nb) (hk : k < len)
    (h : St len b0 k Lo Hi (fun b => (zf b : F)) w R) :
    St len b0 (k + 1) Lo Hi (fun b => (zf b : F)) w (op (zf b0) R (2 * len * b0 + k)) := by
  obtain ⟨hs, hR⟩ := h
  have hbl := block_le hnb hb0
  obtain ⟨hs', hop⟩ := hbf (zf b0) R (2 * len * b0 + k) hs (by omega)
  refine ⟨hs', fun b o ho hi => ?_⟩
  rw [hop]
  have ea : toF R (2 * len * b0 + k) = toF w (2 * len * b0 + k) := by
    rw [hR b0 k (by omega) (by omega), if_neg (by unfold Done; omega)]
  have eb : toF R (2 * len * b0 + k + len) = toF w (2 * len * b0 + k + len) := by
    have := hR b0 (k + len) (by omega) (by omega)
    rw [if_neg (by unfold Done; omega)] at this
    rw [show 2 * len * b0 + k + len = 2 * len * b0 + (k + len) by omega, this]
  rw [ea, eb]
  by_cases h1 : 2 * len * b + o = 2 * len * b0 + k
  · obtain ⟨hb, hob⟩ := dm (len := len) (b := b) (o := o) ho
    obtain ⟨hb', hob'⟩ := dm (len := len) (b := b0) (o := k) (by omega)
    rw [h1] at hb hob
    obtain ⟨rfl, rfl⟩ : b = b0 ∧ o = k := ⟨by omega, by omega⟩
    rw [if_pos rfl, if_pos (by unfold Done; omega), CL_lo hk]
  · rw [if_neg h1]
    by_cases h2 : 2 * len * b + o = 2 * len * b0 + k + len
    · obtain ⟨hb, hob⟩ := dm (len := len) (b := b) (o := o) ho
      obtain ⟨hb', hob'⟩ := dm (len := len) (b := b0) (o := k + len) (by omega)
      rw [h2, show 2 * len * b0 + k + len = 2 * len * b0 + (k + len) by omega] at hb hob
      obtain ⟨rfl, rfl⟩ : b = b0 ∧ o = k + len := ⟨by omega, by omega⟩
      rw [if_pos (by omega), if_pos (by unfold Done; omega), CL_hi (by omega) (by omega),
        show 2 * len * b + (k + len) - len = 2 * len * b + k by omega,
        show 2 * len * b + (k + len) = 2 * len * b + k + len by omega]
    · rw [if_neg h2, hR b o ho hi]
      have hd : Done len b0 (k + 1) b o ↔ Done len b0 k b o := by
        unfold Done
        constructor
        · rintro (h3 | ⟨rfl, h3⟩)
          · exact Or.inl h3
          · right; refine ⟨rfl, ?_⟩
            rcases h3 with h3 | h3
            · by_cases h4 : o = k
              · subst h4; exact absurd rfl h1
              · left; omega
            · by_cases h4 : o = len + k
              · subst h4; exact absurd (by omega) h2
              · right; omega
        · rintro (h3 | ⟨h4, h3⟩)
          · exact Or.inl h3
          · right; exact ⟨h4, by omega⟩
      by_cases hD : Done len b0 k b o
      · rw [if_pos hD, if_pos (hd.2 hD)]
      · rw [if_neg hD, if_neg (fun h' => hD (hd.1 h'))]

theorem st_block {op : Int → Poly → Nat → Poly} {len nb : Nat} {Lo Hi : F → F → F → F}
    (hbf : BfSpec op len Lo Hi) (hlen : 0 < len) (hnb : 2 * len * nb = 256)
    (zf : Nat → Int) (w R : Poly) {b0 : Nat} (hb0 : b0 < nb)
    (h : St len b0 0 Lo Hi (fun b => (zf b : F)) w R) : ∀ k, k ≤ len →
    St len b0 k Lo Hi (fun b => (zf b : F)) w ((List.range' (2 * len * b0) k).foldl (op (zf b0)) R)
  | 0, _ => h
  | k + 1, hk => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul]
    exact st_step hbf hlen hnb zf w _ hb0 (by omega) (st_block hbf hlen hnb zf w R hb0 h k (by omega))

theorem st_layer {op : Int → Poly → Nat → Poly} {len nb : Nat} {Lo Hi : F → F → F → F}
    (hbf : BfSpec op len Lo Hi) (hlen : 0 < len) (hnb : 2 * len * nb = 256)
    (zf : Nat → Int) (w : Poly) (hw : w.size = 256) : ∀ b0, b0 ≤ nb →
    St len b0 0 Lo Hi (fun b => (zf b : F)) w (layerG op len zf w b0)
  | 0, _ => ⟨hw, fun b o _ _ => by rw [if_neg (by unfold Done; omega)]; rfl⟩
  | b0 + 1, hb0 => by
    obtain ⟨hs, hR⟩ := st_block hbf hlen hnb zf w _ (by omega)
      (st_layer hbf hlen hnb zf w hw b0 (by omega)) len le_rfl
    refine ⟨hs, fun b o ho hi => ?_⟩
    show toF ((List.range' (2 * len * b0) len).foldl (op (zf b0)) (layerG op len zf w b0)) _ = _
    rw [hR b o ho hi]
    have hd : Done len b0 len b o ↔ Done len (b0 + 1) 0 b o := by unfold Done; omega
    by_cases hD : Done len b0 len b o
    · rw [if_pos hD, if_pos (hd.1 hD)]
    · rw [if_neg hD, if_neg (fun h' => hD (hd.2 h'))]

theorem layerG_spec {op : Int → Poly → Nat → Poly} {len nb : Nat} {Lo Hi : F → F → F → F}
    (hbf : BfSpec op len Lo Hi) (hlen : 0 < len) (hnb : 2 * len * nb = 256)
    (zf : Nat → Int) (w : Poly) (hw : w.size = 256) :
    (layerG op len zf w nb).size = 256 ∧ ∀ i, i < 256 →
      toF (layerG op len zf w nb) i = CL len Lo Hi (fun b => (zf b : F)) (toF w) i := by
  obtain ⟨hs, hR⟩ := st_layer hbf hlen hnb zf w hw nb le_rfl
  refine ⟨hs, fun i hi => ?_⟩
  obtain ⟨b, o, rfl, ho, hb⟩ := decomp hlen hnb hi
  rw [hR b o ho hi, if_pos (by unfold Done; omega)]

theorem foldl_size {op : Int → Poly → Nat → Poly} (hop : ∀ z w a, (op z w a).size = w.size)
    (z : Int) : ∀ (l : List Nat) (R : Poly), (l.foldl (op z) R).size = R.size
  | [], _ => rfl
  | a :: l, R => by rw [List.foldl_cons, foldl_size hop z l, hop]

theorem layerG_size {op : Int → Poly → Nat → Poly} {len : Nat}
    (hop : ∀ z w a, (op z w a).size = w.size) (zf : Nat → Int) (w : Poly) :
    ∀ b, (layerG op len zf w b).size = w.size
  | 0 => rfl
  | b + 1 => by
    show ((List.range' (2 * len * b) len).foldl (op (zf b)) (layerG op len zf w b)).size = _
    rw [foldl_size hop, layerG_size hop zf w b]

/-! ## The two butterflies -/

theorem bfN_size (len : Nat) (z : Int) (w : Poly) (a : Nat) : (bfN len z w a).size = w.size := by
  simp [bfN]

theorem bfI_size (len : Nat) (z : Int) (w : Poly) (a : Nat) : (bfI len z w a).size = w.size := by
  simp [bfI]

theorem bfN_spec (len : Nat) (hlen : 0 < len) :
    BfSpec (bfN len) len (fun z x y => x + z * y) (fun z x y => x - z * y) := by
  intro z w a hw ha
  refine ⟨by rw [bfN_size, hw], fun i => ?_⟩
  unfold bfN toF
  rw [getElem!_set _ _ _ _ (by simp; omega), getElem!_set _ _ _ _ (by omega),
    getElem!_set _ _ _ _ (by omega), if_neg (by omega : ¬ a = a + len)]
  by_cases h1 : i = a
  · subst h1; simp only [if_true, cast_emod, Int.cast_add, Int.cast_mul]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = a + len
    · simp only [h2, if_true, cast_emod, Int.cast_sub, Int.cast_mul]
    · rw [if_neg h2, if_neg h2]

theorem bfI_spec (len : Nat) (hlen : 0 < len) :
    BfSpec (bfI len) len (fun _ x y => x + y) (fun z x y => z * (x - y)) := by
  intro z w a hw ha
  refine ⟨by rw [bfI_size, hw], fun i => ?_⟩
  unfold bfI toF
  have ha' : a < 256 := by omega
  have hne : ¬ a + len = a := by omega
  simp (disch := (simp only [Array.size_set!, hw]; omega)) only [getElem!_set, if_true, hne,
    if_false]
  by_cases h1 : i = a + len
  · subst h1; simp only [if_true, hne, if_false, cast_emod, Int.cast_sub, Int.cast_mul]
  · simp only [h1, if_false]
    by_cases h2 : i = a
    · simp only [h2, if_true, cast_emod, Int.cast_add]
    · simp only [h2, if_false]

end MlDsaOpt44.Proofs.NttConv
