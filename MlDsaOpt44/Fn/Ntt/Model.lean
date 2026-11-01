import MlDsaOpt44.Fn.Ntt.Defs
import MlDsa44.Proofs.Math.Ntt.Model
/-!
# `Fips204.ntt` / `nttInv` modulo `q` are the index-wise layer models (WP7)

The reference's closed-index models (`MlDsa44.Proofs.NttModel.nttL`, `nttIL`,
`scaleI`) apply the butterflies of a layer one at a time; here every layer is
shown to compute `fwdLayer` / `invLayer` modulo `q`, so that
`((ntt f)[t]! : F) = fwdL f 8 t` and `((nttInv f)[t]! : F) = 256⁻¹ · invL f 8 t`.
-/

namespace MlDsaOpt44.Proofs.NttW

open MlDsa44 MlDsa44.Proofs.NttModel
open Fips204 (Poly zetas)

theorem getElem!_set!' (a : Array Int) (i j : Nat) (v : Int) (h : j < a.size) :
    (a.set! j v)[i]! = if i = j then v else a[i]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij, Ne.symm hij]

theorem size_set!' (a : Array Int) (j : Nat) (v : Int) : (a.set! j v).size = a.size := by
  simp [Array.set!]

theorem castq (x : Int) : (((x % (Fips204.q : Int) : Int)) : F) = (x : F) :=
  ZMod.intCast_mod x Fips204.q

/-! ## Arithmetic of block positions -/

/-- The butterfly that touches index `t` in a layer with block length `len`. -/
def bfIdx (len t : Nat) : Nat := if t % (2 * len) < len then t else t - len

theorem bfIdx_le (len t : Nat) : bfIdx len t ≤ t := by unfold bfIdx; split <;> omega

theorem bfIdx_mod {len t : Nat} (hl : 0 < len) : bfIdx len t % (2 * len) < len := by
  unfold bfIdx
  split
  · assumption
  · rename_i h
    have h2 : 0 < 2 * len := by omega
    have e := Nat.div_add_mod t (2 * len)
    have hr := Nat.mod_lt t h2
    have hq : t - len = (t % (2 * len) - len) + 2 * len * (t / (2 * len)) := by
      generalize 2 * len * (t / (2 * len)) = X at e ⊢; omega
    rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

theorem bfIdx_eq {len t a : Nat} (_ha : a % (2 * len) < len) (h : bfIdx len t = a) :
    t = a ∨ t = a + len := by
  unfold bfIdx at h
  split at h
  · exact Or.inl h
  · rename_i h'
    have : len ≤ t := by
      have := Nat.mod_le t (2 * len); omega
    exact Or.inr (by omega)

theorem bfIdx_self {len a : Nat} (ha : a % (2 * len) < len) : bfIdx len a = a := by
  unfold bfIdx; rw [if_pos ha]

theorem divmod_hi' {ia len : Nat} (h : ia % (2 * len) < len) :
    (ia + len) % (2 * len) = ia % (2 * len) + len ∧ (ia + len) / (2 * len) = ia / (2 * len) := by
  have h2 : 0 < 2 * len := by omega
  have e := Nat.div_add_mod ia (2 * len)
  have hlt : ia % (2 * len) + len < 2 * len := by omega
  have hx : ia + len = (ia % (2 * len) + len) + 2 * len * (ia / (2 * len)) := by
    generalize 2 * len * (ia / (2 * len)) = X at e ⊢
    omega
  constructor
  · rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [hx, Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem bfIdx_hi {len a : Nat} (ha : a % (2 * len) < len) : bfIdx len (a + len) = a := by
  unfold bfIdx
  rw [if_neg (by rw [(divmod_hi' ha).1]; omega)]
  omega

/-- Position `2 len b + r` (`r < len`) of block `b`. -/
theorem blockPos {len b r : Nat} (hr : r < len) :
    (2 * len * b + r) % (2 * len) = r ∧ (2 * len * b + r) / (2 * len) = b := by
  have h2 : 0 < 2 * len := by omega
  constructor
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ h2, Nat.div_eq_of_lt (by omega),
      Nat.zero_add]

/-- No butterfly index lies in the second half of a block. -/
theorem bfIdx_gap {len b t : Nat} (hl : 0 < len) :
    bfIdx len t < 2 * len * b + len ↔ bfIdx len t < 2 * len * (b + 1) := by
  have hm := bfIdx_mod (t := t) hl
  generalize bfIdx len t = x at hm ⊢
  have h2 : 0 < 2 * len := by omega
  have e := Nat.div_add_mod x (2 * len)
  constructor
  · intro h; rw [Nat.mul_add, Nat.mul_one]; omega
  · intro h
    have hq : x / (2 * len) < b + 1 := (Nat.div_lt_iff_lt_mul h2).2 (by rw [Nat.mul_comm]; exact h)
    have : 2 * len * (x / (2 * len)) ≤ 2 * len * b := Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## Forward layers -/

def LInvN (len : Nat) (G : Nat → F) (cur : Nat) (w : Poly) : Prop :=
  w.size = 256 ∧ ∀ t, t < 256 → ((w[t]! : ℤ) : F) = if bfIdx len t < cur then fwdLayer len G t else G t

theorem bfN_get' (len : Nat) (z : Int) (g : Poly) (a i : Nat) (hg : g.size = 256)
    (ha : a + len < 256) (hlen : 0 < len) :
    (bfN len z g a)[i]! =
      if i = a then (g[a]! + z * g[a + len]! % Fips204.q) % Fips204.q
      else if i = a + len then (g[a]! - z * g[a + len]! % Fips204.q) % Fips204.q else g[i]! := by
  unfold bfN
  rw [getElem!_set!' _ _ _ _ (by rw [size_set!']; omega), getElem!_set!' _ _ _ _ (by omega),
    getElem!_set!' _ _ _ _ (by omega)]
  have hl : len ≠ 0 := by omega
  by_cases h1 : i = a
  · subst h1; simp [hl]
  · simp [h1]

theorem bfN_size (len : Nat) (z : Int) (g : Poly) (a : Nat) : (bfN len z g a).size = g.size := by
  simp [bfN]

theorem linvN_step {len : Nat} {G : Nat → F} {a : Nat} {w : Poly} (hl : 0 < len)
    (ha : a % (2 * len) < len) (hal : a + len < 256) (hw : LInvN len G a w) :
    LInvN len G (a + 1) (bfN len (zetas (128 / len + a / (2 * len))) w a) := by
  obtain ⟨hs, hv⟩ := hw
  refine ⟨by rw [bfN_size, hs], fun t ht => ?_⟩
  have hA := hv a (by omega)
  have hB := hv (a + len) hal
  rw [bfIdx_self ha, if_neg (Nat.lt_irrefl _)] at hA
  rw [bfIdx_hi ha, if_neg (Nat.lt_irrefl _)] at hB
  rw [bfN_get' len _ w a t hs hal hl]
  by_cases h1 : t = a
  · subst h1
    rw [if_pos rfl, bfIdx_self ha, if_pos (Nat.lt_succ_self _)]
    unfold fwdLayer
    rw [if_pos ha]
    push_cast [castq]
    rw [hA, hB]; rfl
  · by_cases h2 : t = a + len
    · subst h2
      rw [if_neg h1, if_pos rfl, bfIdx_hi ha, if_pos (Nat.lt_succ_self _)]
      unfold fwdLayer
      rw [if_neg (by rw [(divmod_hi' ha).1]; omega), (divmod_hi' ha).2, Nat.add_sub_cancel]
      push_cast [castq]
      rw [hA, hB]; rfl
    · rw [if_neg h1, if_neg h2, hv t ht]
      have hne : bfIdx len t ≠ a := fun h => (bfIdx_eq ha h).elim h1 h2
      by_cases hc : bfIdx len t < a
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]

theorem linvN_block {len : Nat} {G : Nat → F} {b : Nat} {w : Poly} (hl : 0 < len)
    (hb : 2 * len * (b + 1) ≤ 256) (hw : LInvN len G (2 * len * b) w) :
    ∀ r, r ≤ len → LInvN len G (2 * len * b + r)
      ((List.range' (2 * len * b) r).foldl (bfN len (zetas (128 / len + b))) w)
  | 0, _ => by simpa using hw
  | r + 1, hr => by
    rw [List.range'_concat, List.foldl_append]
    have ih := linvN_block hl hb hw r (by omega)
    obtain ⟨hm, hd⟩ := blockPos (len := len) (b := b) (r := r) (by omega)
    have := linvN_step (a := 2 * len * b + r) hl (by rw [hm]; omega)
      (by have : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
          omega) ih
    rw [hd] at this
    simpa [← Nat.add_assoc] using this

theorem layerN_model {len m0 : Nat} (hl : 0 < len) (hm0 : m0 + 1 = 128 / len) {G : Nat → F} {w : Poly}
    (hw : w.size = 256) (hG : ∀ t, t < 256 → ((w[t]! : ℤ) : F) = G t) :
    ∀ nb, 2 * len * nb ≤ 256 → LInvN len G (2 * len * nb) (layerN len m0 w nb)
  | 0, _ => ⟨hw, fun t ht => by
      simp only [Nat.mul_zero, Nat.not_lt_zero, if_false]; exact hG t ht⟩
  | nb + 1, hnb => by
    have ih := layerN_model hl hm0 hw hG nb (by
      have : 2 * len * (nb + 1) = 2 * len * nb + 2 * len := by ring
      omega)
    have hblk := linvN_block hl hnb ih len le_rfl
    have hz : m0 + nb + 1 = 128 / len + nb := by omega
    simp only [layerN, blockN, hz]
    refine ⟨hblk.1, fun t ht => ?_⟩
    rw [hblk.2 t ht]
    simp only [bfIdx_gap hl]

theorem nttL_model (f : Poly) (hf : f.size = 256) :
    ∀ L, L ≤ 8 → (nttL f L).size = 256 ∧
      ∀ t, t < 256 → (((nttL f L)[t]! : ℤ) : F) = fwdL (fun i => ((f[i]! : ℤ) : F)) L t
  | 0, _ => ⟨hf, fun _ _ => rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hv⟩ := nttL_model f hf L (by omega)
    have hL8 : L < 8 := by omega
    have hl : 0 < 128 / 2 ^ L := by interval_cases L <;> decide
    have hm0 : 2 ^ L - 1 + 1 = 128 / (128 / 2 ^ L) := by interval_cases L <;> decide
    have hnb : 2 * (128 / 2 ^ L) * 2 ^ L = 256 := by interval_cases L <;> decide
    have := layerN_model hl hm0 hs hv (2 ^ L) (by omega)
    rw [hnb] at this
    refine ⟨this.1, fun t ht => ?_⟩
    simp only [nttL]
    rw [this.2 t ht, if_pos (Nat.lt_of_le_of_lt (bfIdx_le _ _) ht)]
    rfl

theorem ntt_model (f : Poly) (hf : f.size = 256) {t : Nat} (ht : t < 256) :
    (((Fips204.ntt f)[t]! : ℤ) : F) = fwdL (fun i => ((f[i]! : ℤ) : F)) 8 t := by
  rw [ntt_eq]; exact (nttL_model f hf 8 le_rfl).2 t ht

/-! ## Inverse layers -/

def LInvI (len m0 : Nat) (G : Nat → F) (cur : Nat) (w : Poly) : Prop :=
  w.size = 256 ∧ ∀ t, t < 256 → ((w[t]! : ℤ) : F) = if bfIdx len t < cur then invLayer len m0 G t else G t

theorem bfI_get' (len : Nat) (z : Int) (g : Poly) (a i : Nat) (hg : g.size = 256)
    (ha : a + len < 256) (hlen : 0 < len) :
    (bfI len z g a)[i]! =
      if i = a + len then z * ((g[a]! - g[a + len]!) % Fips204.q) % Fips204.q
      else if i = a then (g[a]! + g[a + len]!) % Fips204.q else g[i]! := by
  have hl0 : len ≠ 0 := by omega
  unfold bfI
  simp (disch := (simp only [size_set!', hg]; omega)) only [getElem!_set!']
  by_cases h1 : i = a + len
  · subst h1; simp [hl0]
  · by_cases h2 : i = a
    · subst h2; simp [hl0]
    · simp [h1, h2]

theorem bfI_size (len : Nat) (z : Int) (g : Poly) (a : Nat) : (bfI len z g a).size = g.size := by
  simp [bfI]

theorem linvI_step {len m0 : Nat} {G : Nat → F} {a : Nat} {w : Poly} (hl : 0 < len)
    (ha : a % (2 * len) < len) (hal : a + len < 256) (hw : LInvI len m0 G a w) :
    LInvI len m0 G (a + 1) (bfI len (-zetas (m0 - a / (2 * len) - 1)) w a) := by
  obtain ⟨hs, hv⟩ := hw
  refine ⟨by rw [bfI_size, hs], fun t ht => ?_⟩
  have hA := hv a (by omega)
  have hB := hv (a + len) hal
  rw [bfIdx_self ha, if_neg (Nat.lt_irrefl _)] at hA
  rw [bfIdx_hi ha, if_neg (Nat.lt_irrefl _)] at hB
  rw [bfI_get' len _ w a t hs hal hl]
  by_cases h2 : t = a + len
  · subst h2
    rw [if_pos rfl, bfIdx_hi ha, if_pos (Nat.lt_succ_self _)]
    unfold invLayer
    rw [if_neg (by rw [(divmod_hi' ha).1]; omega), (divmod_hi' ha).2, Nat.add_sub_cancel]
    push_cast [castq]
    rw [hA, hB]
    unfold ζ; ring
  · by_cases h1 : t = a
    · subst h1
      rw [if_neg h2, if_pos rfl, bfIdx_self ha, if_pos (Nat.lt_succ_self _)]
      unfold invLayer
      rw [if_pos ha]
      push_cast [castq]
      rw [hA, hB]
    · rw [if_neg h2, if_neg h1, hv t ht]
      have hne : bfIdx len t ≠ a := fun h => (bfIdx_eq ha h).elim h1 h2
      by_cases hc : bfIdx len t < a
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]

theorem linvI_block {len m0 : Nat} {G : Nat → F} {b : Nat} {w : Poly} (hl : 0 < len)
    (hb : 2 * len * (b + 1) ≤ 256) (hw : LInvI len m0 G (2 * len * b) w) :
    ∀ r, r ≤ len → LInvI len m0 G (2 * len * b + r)
      ((List.range' (2 * len * b) r).foldl (bfI len (-zetas (m0 - b - 1))) w)
  | 0, _ => by simpa using hw
  | r + 1, hr => by
    rw [List.range'_concat, List.foldl_append]
    have ih := linvI_block hl hb hw r (by omega)
    obtain ⟨hm, hd⟩ := blockPos (len := len) (b := b) (r := r) (by omega)
    have := linvI_step (m0 := m0) (a := 2 * len * b + r) hl (by rw [hm]; omega)
      (by have : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
          omega) ih
    rw [hd] at this
    simpa [← Nat.add_assoc] using this

theorem layerI_model {len m0 : Nat} (hl : 0 < len) {G : Nat → F} {w : Poly}
    (hw : w.size = 256) (hG : ∀ t, t < 256 → ((w[t]! : ℤ) : F) = G t) :
    ∀ nb, 2 * len * nb ≤ 256 → LInvI len m0 G (2 * len * nb) (layerI len m0 w nb)
  | 0, _ => ⟨hw, fun t ht => by
      simp only [Nat.mul_zero, Nat.not_lt_zero, if_false]; exact hG t ht⟩
  | nb + 1, hnb => by
    have ih := layerI_model (m0 := m0) hl hw hG nb (by
      have : 2 * len * (nb + 1) = 2 * len * nb + 2 * len := by ring
      omega)
    have hblk := linvI_block (m0 := m0) hl hnb ih len le_rfl
    simp only [layerI, blockI]
    refine ⟨hblk.1, fun t ht => ?_⟩
    rw [hblk.2 t ht]
    simp only [bfIdx_gap hl]

theorem nttIL_model (f : Poly) (hf : f.size = 256) :
    ∀ L, L ≤ 8 → (nttIL f L).size = 256 ∧
      ∀ t, t < 256 → (((nttIL f L)[t]! : ℤ) : F) = invL (fun i => ((f[i]! : ℤ) : F)) L t
  | 0, _ => ⟨hf, fun _ _ => rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hv⟩ := nttIL_model f hf L (by omega)
    have hL8 : L < 8 := by omega
    have hl : 0 < 2 ^ L := by positivity
    have hnb : 2 * 2 ^ L * (128 / 2 ^ L) = 256 := by interval_cases L <;> decide
    have := layerI_model (m0 := 2 ^ (8 - L)) hl hs hv (128 / 2 ^ L) (by omega)
    rw [hnb] at this
    refine ⟨this.1, fun t ht => ?_⟩
    simp only [nttIL]
    rw [this.2 t ht, if_pos (Nat.lt_of_le_of_lt (bfIdx_le _ _) ht)]
    rfl

theorem scaleI_model (w : Poly) (hw : w.size = 256) :
    ∀ k, k ≤ 256 → (scaleI w k).size = 256 ∧ ∀ t, t < 256 →
      (((scaleI w k)[t]! : ℤ) : F) = if t < k then 8347681 * ((w[t]! : ℤ) : F) else ((w[t]! : ℤ) : F)
  | 0, _ => ⟨hw, fun t _ => by simp [scaleI]⟩
  | k + 1, hk => by
    obtain ⟨hs, hv⟩ := scaleI_model w hw k (by omega)
    have he : scaleI w (k + 1) = scStep (scaleI w k) k := by
      simp only [scaleI, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.zero_add, Nat.one_mul]
    rw [he]
    refine ⟨by simp [scStep, hs], fun t ht => ?_⟩
    unfold scStep
    rw [getElem!_set!' _ _ _ _ (by omega)]
    by_cases htk : t = k
    · subst htk
      rw [if_pos rfl, if_pos (Nat.lt_succ_self _)]
      push_cast [castq]
      rw [hv t ht, if_neg (Nat.lt_irrefl _)]
    · rw [if_neg htk, hv t ht]
      by_cases hc : t < k
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]

theorem nttInv_model (f : Poly) (hf : f.size = 256) {t : Nat} (ht : t < 256) :
    (((Fips204.nttInv f)[t]! : ℤ) : F) = 8347681 * invL (fun i => ((f[i]! : ℤ) : F)) 8 t := by
  rw [nttInv_eq]
  obtain ⟨hs, hv⟩ := nttIL_model f hf 8 le_rfl
  rw [(scaleI_model _ hs 256 le_rfl).2 t ht, if_pos ht, hv t ht]

/-! ## Linearity of the inverse layers -/

theorem invL_smul (c : F) (h : Nat → F) : ∀ L t, invL (fun i => c * h i) L t = c * invL h L t
  | 0, _ => rfl
  | L + 1, t => by
    simp only [invL, invLayer]
    split <;> simp only [invL_smul c h L] <;> ring

end MlDsaOpt44.Proofs.NttW
