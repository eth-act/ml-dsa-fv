import MlDsaOptCommon.Basic
set_option warningAsError true
/-!
# `Reach`: gas-bounded traces and their composition

`Reach s t c`: a trace from `s` to `t` costing at most `c` gas. Everything
composes by `Reach.trans` (costs add) and `Reach.mono`; loops by
`Reach.loop` (uniform per-iteration bound) and `Reach.loopSum`. The
artifact-specific block lemmas (`reach_block`, generated per artifact) produce
`Reach` facts for straight-line paths.
-/

namespace MlDsaOptCommon

open EvmSemantics
open EvmSemantics.EVM

/-- A gas-parametric trace from `s` to `t` with cost at most `c`. -/
def Reach (s t : State) (c : Nat) : Prop := ∃ g : EvmProof.GasSteps s t, g.cost ≤ c

theorem Reach.refl (s : State) : Reach s s 0 := ⟨EvmProof.GasSteps.refl s, le_rfl⟩

theorem Reach.trans {s t u : State} {a b : Nat} (h₁ : Reach s t a) (h₂ : Reach t u b) :
    Reach s u (a + b) := by
  obtain ⟨g₁, h₁⟩ := h₁
  obtain ⟨g₂, h₂⟩ := h₂
  exact ⟨g₁.trans g₂, by simp only [EvmProof.GasSteps.trans_cost]; omega⟩

theorem Reach.mono {s t : State} {a b : Nat} (h : Reach s t a) (hab : a ≤ b) : Reach s t b := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, Nat.le_trans hg hab⟩

theorem Reach.of_eq {s t s' t' : State} {a : Nat} (h : Reach s t a) (hs : s = s') (ht : t = t') :
    Reach s' t' a := hs ▸ ht ▸ h

theorem Reach.of_gasSteps {s t : State} (g : EvmProof.GasSteps s t) : Reach s t g.cost :=
  ⟨g, le_rfl⟩

/-- Loop with a uniform per-iteration bound. -/
theorem Reach.loop {I : Nat → State} {c : Nat} :
    ∀ n, (∀ i, i < n → Reach (I i) (I (i + 1)) c) → Reach (I 0) (I n) (n * c)
  | 0, _ => by simpa using Reach.refl (I 0)
  | n + 1, h => by
    have := (Reach.loop n (fun i hi => h i (by omega))).trans (h n (by omega))
    simpa [Nat.succ_mul] using this

/-- Loop with an iteration-dependent bound. -/
theorem Reach.loopSum {I : Nat → State} {c : Nat → Nat} :
    ∀ n, (∀ i, i < n → Reach (I i) (I (i + 1)) (c i)) →
      Reach (I 0) (I n) ((List.range n).map c).sum
  | 0, _ => by simpa using Reach.refl (I 0)
  | n + 1, h => by
    have := (Reach.loopSum n (fun i hi => h i (by omega))).trans (h n (by omega))
    simpa [List.range_succ] using this

end MlDsaOptCommon
