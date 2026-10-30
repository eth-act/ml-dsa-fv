import MlDsa44.Spec.Fips204
/-!
# Facts about `verifyInternal`'s building blocks

Loop invariants and `Option`-traversal characterisations used to flatten
`Fips204.verifyInternal` into independent checks.
-/

namespace MlDsa44.Proofs.Math

open Fips204

theorem getElem!_map_range {β : Type} [Inhabited β] (n i : Nat) (F : Nat → β) (h : i < n) :
    ((Array.range n).map F)[i]! = F i := by
  simp [getElem!_pos, h]

theorem getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (xs : Array α) (F : α → β)
    (i : Nat) (h : i < xs.size) : (xs.map F)[i]! = F xs[i]! := by
  simp [getElem!_pos, h]

theorem map_range_congr {β : Type} (n : Nat) (F G : Nat → β) (h : ∀ i, i < n → F i = G i) :
    (Array.range n).map F = (Array.range n).map G := by
  apply Array.ext (by simp)
  intro i h1 _
  simp only [Array.size_map, Array.size_range] at h1
  simp [h i h1]

theorem w1_congr (F G : Nat → Poly) (h : Array Poly)
    (hFG : ∀ i, i < 4 → F i = G i) :
    (Array.range k).map (fun i => (Array.range 256).map fun j =>
        useHint h[i]![j]! ((Array.range k).map F)[i]![j]!) =
      (Array.range 4).map (fun i => (Array.range 256).map fun j =>
        useHint h[i]![j]! ((Array.range 4).map G)[i]![j]!) := by
  apply map_range_congr
  intro i hi
  rw [getElem!_map_range _ _ _ hi, getElem!_map_range 4 _ _ hi, hFG i hi]

theorem foldl_congr_mem {α β : Type} (l : List α) (F G : β → α → β) (init : β)
    (h : ∀ b j, j ∈ l → F b j = G b j) : l.foldl F init = l.foldl G init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h init x (by simp)]
    exact ih _ fun b j hj => h b j (by simp [hj])

theorem forIn_id_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P init) (hstep : ∀ a b, P b → P (f a b).run.value) :
    P (forIn l init f).run := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons x xs ih =>
    rw [List.forIn_cons]
    have := hstep x init h0
    revert this
    cases f x init with
    | done b => intro hb; exact hb
    | yield b => intro hb; exact ih b hb

theorem id_bind_eq {β γ : Type} (x : Id β) (g : β → Id γ) : (x >>= g) = g x.run := rfl

theorem sampleInBallOf_size (s : ByteArray) (c : Poly) (h : sampleInBallOf s = some c) :
    c.size = 256 := by
  unfold sampleInBallOf at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  rw [id_bind_eq] at h
  have inv := fun l init f => forIn_id_inv (α := Nat) l init f
    (fun st : Option (Option Poly) × Poly × Nat => st.2.1.size = 256 ∧ ∀ r, st.1 = some r → r = none)
  have h0 : Array.size (zeroPoly : Poly) = 256 ∧ ∀ r : Option Poly, (none : Option (Option Poly)) = some r → r = none :=
    ⟨by simp [zeroPoly], by simp⟩
  split at h
  · rename_i r heq
    have hr := (inv _ _ _ h0 (by
      intro a b hb
      split
      · exact ⟨hb.1, by simp⟩
      · exact ⟨by simp [hb.1], by simp⟩)).2 r heq
    subst hr
    cases h
  · rw [← Option.some.inj h]
    exact (inv _ _ _ h0 (by
      intro a b hb
      split
      · exact ⟨hb.1, by simp⟩
      · exact ⟨by simp [hb.1], by simp⟩)).1

theorem list_mapM_option {α β : Type} (f : α → Option β) (l : List α) (d : β) :
    l.mapM f = if l.all (fun x => (f x).isSome) then some (l.map fun x => (f x).getD d) else none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, ih]
    cases h : f x with
    | none => simp [h]
    | some b =>
      by_cases hall : xs.all (fun x => (f x).isSome) = true
      · simp [hall, h]
      · simp only [hall]; simp [h, hall]

theorem array_mapM_range_option {β : Type} (n : Nat) (f : Nat → Option β) (d : β) :
    (List.range n).toArray.mapM f =
      if (List.range n).all (fun x => (f x).isSome) then
        some ((Array.range n).map fun x => (f x).getD d) else none := by
  rw [List.mapM_toArray, list_mapM_option _ _ d]
  split <;> simp
  apply Array.ext <;> simp

/-- `ExpandA` succeeds iff every entry does, and then holds the entries. -/
theorem expandA_eq (rho : ByteArray) :
    expandA rho =
      if (List.range 4).all (fun r => (List.range 4).all fun s =>
          (rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) then
        some ((Array.range 4).map fun r => (Array.range 4).map fun s =>
          (rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).getD zeroPoly)
      else none := by
  unfold expandA
  rw [show k = 4 from rfl, show l = 4 from rfl, array_mapM_range_option 4 _ #[]]
  simp only [array_mapM_range_option 4 _ zeroPoly]
  by_cases hc : (List.range 4).all (fun r => (List.range 4).all fun s =>
          (rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) = true
  · have hc' := hc
    simp only [List.all_eq_true] at hc'
    rw [if_pos hc]
    rw [if_pos (by simp only [List.all_eq_true]; intro r hr; rw [if_pos (hc' r hr)]; rfl)]
    congr 1
    apply Array.ext (by simp)
    intro i h1 h2
    simp at h1
    have hi := hc' i (by simpa using h1)
    simp only [List.mem_range] at hi
    simp
    rw [if_pos hi]
    rfl
  · rw [if_neg hc, if_neg]
    intro h
    apply hc
    simp only [List.all_eq_true] at h ⊢
    intro r hr
    have := h r hr
    split at this
    · assumption
    · simp at this

end MlDsa44.Proofs.Math
