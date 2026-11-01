import Lean
set_option warningAsError true
/-!
# Running a long straight-line block in pieces

The block tactics (`optNN_block`, `evm_block`) reduce
`(path.map located).foldl stepL (some s) = rhs` with one `simp`. The kernel's
check of that single proof grows much faster than the path: for the 340
instructions of `MlDsaOpt44.Proofs.Blk.bodyA` it took 78 s, against 1.7 s for
the first 85 and 7.8 s for the first 170 (most of the time in the kernel's
definitional-equality cache comparing large states structurally).

`foldl_chunks n => tac` splits the literal path into pieces of at most `n`
instructions and runs `tac` once per piece, each from the state the previous
piece reached (`foldl_map_append_of_eq`). With one `simp` proof per piece the
kernel check stays roughly linear in the path length (bodyA: 78 s → 7.9 s with
pieces of 85; 6 s with pieces of 20–40). The statement proved is unchanged.
-/

namespace MlDsaOptCommon

theorem foldl_map_append_of_eq {α β γ : Type _} {f : α → β → α} {g : γ → β} {a b c : α}
    {l₁ l₂ : List γ} (h₁ : (l₁.map g).foldl f a = b) (h₂ : (l₂.map g).foldl f b = c) :
    ((l₁ ++ l₂).map g).foldl f a = c := by
  rw [List.map_append, List.foldl_append, h₁, h₂]

open Lean Meta Elab Tactic

/-- On a goal `List.foldl f a (List.map g [x₁, …, xₘ]) = rhs`, run `tac` on the
first `n` elements (goal `… = ?b`, closed by `rfl` once `tac` has reduced the
left side), then continue from `?b` with the rest; the last piece runs `tac`
against `rhs`. Any other goal shape runs `tac` once. -/
partial def foldlChunks (n : Nat) (tac : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := tgt.eq? | evalTactic tac
    let some (f, a, xs) := (if lhs.isAppOfArity ``List.foldl 5 then
        some (lhs.getArg! 2, lhs.getArg! 3, lhs.getArg! 4) else none) | evalTactic tac
    let some (gfn, l) := (if xs.isAppOfArity ``List.map 4 then
        some (xs.getArg! 2, xs.getArg! 3) else none) | evalTactic tac
    let some elems := (← zetaReduce (← instantiateMVars l)).listLit? | evalTactic tac
    if elems.2.length ≤ n then
      evalTactic tac
      return
    let ty := elems.1
    let l₁ ← mkListLit ty (elems.2.take n)
    let l₂ ← mkListLit ty (elems.2.drop n)
    let b ← mkFreshExprMVar (← inferType a)
    let h₁ ← mkFreshExprSyntheticOpaqueMVar
      (← mkEq (← mkAppM ``List.foldl #[f, a, ← mkAppM ``List.map #[gfn, l₁]]) b)
    let h₂ ← mkFreshExprSyntheticOpaqueMVar
      (← mkEq (← mkAppM ``List.foldl #[f, b, ← mkAppM ``List.map #[gfn, l₂]]) rhs)
    let pf ← mkAppM ``foldl_map_append_of_eq #[h₁, h₂]
    unless ← isDefEq (← inferType pf) tgt do
      throwError "foldl_chunks: could not split the path of{indentExpr tgt}"
    g.assign pf
    setGoals [h₁.mvarId!]
    evalTactic tac
    for r in ← getUnsolvedGoals do r.refl
    setGoals [h₂.mvarId!]
    foldlChunks n tac

/-- `foldl_chunks n => tac`: see `foldlChunks`. -/
elab "foldl_chunks " n:num " => " tac:tacticSeq : tactic => foldlChunks n.getNat tac

end MlDsaOptCommon
