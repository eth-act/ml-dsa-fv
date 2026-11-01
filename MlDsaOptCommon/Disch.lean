import Lean
set_option warningAsError true
/-!
# Side-goal discharger of the block tactics

The `simp` of `optNN_block` / `evm_block` discharges its side goals with
`blk_disch`. Nearly all of them are linear `Nat` bounds that follow from
literal bounds in context:

* comparisons of literals, e.g. `8971 < 2 ^ 256` (`Nat.mod_eq_of_lt` on a
  literal `pc + 1`; `simp` tries it before the `Nat.reduceMod` simproc);
* stack capacity, `tail.length + 1 + … + 1 < 1024` from `htail : tail.length ≤ K`;
* word and memory bounds such as `67840 + Y * 32 + 32 ≤ 32 * s.activeWords.toNat`
  from `hY : Y < 256` and `hmem : 84224 ≤ 32 * s.activeWords.toNat`.

`omega` proves each of these in a few milliseconds and adds an auxiliary
theorem for the kernel; a block of 20 instructions has about 50 of them.
`blk_disch` proves them directly: an upper bound `a ≤ c` of the left side and a
lower bound `d ≤ b` of the right side, both literal, built through `+` and
multiplication by literals from hypotheses `x ≤ c`, `x < c`, `x + k ≤ c`,
`d ≤ x`, then `Nat.blt c d` (or `Nat.ble`) by evaluation. A goal it cannot prove this way
goes to `assumption` (reducible transparency), then `omega` if the goal is
arithmetic and `omega` has not already failed on it in the same context.
-/

namespace MlDsaOptCommon

theorem bnd_add {a b c d : Nat} (h₁ : a ≤ c) (h₂ : b ≤ d) : a + b ≤ c + d := Nat.add_le_add h₁ h₂
theorem bnd_mul_right {a c : Nat} (k : Nat) (h : a ≤ c) : a * k ≤ c * k := Nat.mul_le_mul_right k h
theorem bnd_mul_left {a c : Nat} (k : Nat) (h : a ≤ c) : k * a ≤ k * c := Nat.mul_le_mul_left k h
theorem bnd_of_lt {a c : Nat} (h : a < c) : a ≤ c - 1 := Nat.le_sub_one_of_lt h
theorem bnd_of_lt' {c a : Nat} (h : c < a) : c + 1 ≤ a := h
theorem bnd_of_add_le {x k c : Nat} (h : x + k ≤ c) : x ≤ c - k := Nat.le_sub_of_add_le h
theorem bnd_of_add_le' {x k c : Nat} (h : k + x ≤ c) : x ≤ c - k :=
  Nat.le_sub_of_add_le (Nat.add_comm k x ▸ h)

theorem disch_lt {a b c d : Nat} (ha : a ≤ c) (hb : d ≤ b) (h : Nat.blt c d = true) : a < b :=
  Nat.lt_of_le_of_lt ha (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true h) hb)

theorem disch_le {a b c d : Nat} (ha : a ≤ c) (hb : d ≤ b) (h : Nat.ble c d = true) : a ≤ b :=
  Nat.le_trans ha (Nat.le_trans (Nat.le_of_ble_eq_true h) hb)

theorem disch_not_lt {a b : Nat} (h : a ≤ b) : ¬ b < a := Nat.not_lt.mpr h

open Lean Meta Elab Tactic

/-- The value of a closed `Nat` expression (literals, `+`, `^`, …; `evalNat`,
plus `^` through Mathlib's `Monoid.npow` instance, as in `2 ^ 256` in lemma
statements). -/
private partial def natVal? (e : Expr) : MetaM (Option Nat) := do
  if let some v ← (evalNat e).run then return some v
  let_expr HPow.hPow t₁ t₂ _ _ b n := e | return none
  unless t₁.isConstOf ``Nat && t₂.isConstOf ``Nat do return none
  let some n ← natVal? n | return none
  unless n ≤ 4096 do return none
  return (← natVal? b).map (· ^ n)

/-- A bound on a `Nat` term: its literal value `v`, the bound as an
expression `c` (with value `v`) and the proof (`e ≤ c` or `c ≤ e`). -/
private structure Bnd where
  v : Nat
  c : Expr
  h : Expr

/-- `(x, y)` with `x ≤ y`, `x < y` (`strict`) for hypotheses or `none`. -/
private def leHyp? (ty : Expr) : Option (Expr × Expr × Bool) :=
  match_expr ty with
  | LE.le t _ x y => if t.isConstOf ``Nat then some (x, y, false) else none
  | LT.lt t _ x y => if t.isConstOf ``Nat then some (x, y, true) else none
  | GE.ge t _ y x => if t.isConstOf ``Nat then some (x, y, false) else none
  | GT.gt t _ y x => if t.isConstOf ``Nat then some (x, y, true) else none
  | _ => none

mutual
/-- `e ≤ c` with literal `c`, through `+`, `* k`, and hypotheses. -/
private partial def upper? (e : Expr) (depth : Nat) : MetaM (Option Bnd) := do
  if let some v ← natVal? e then
    return some ⟨v, e, mkApp (mkConst ``Nat.le_refl) e⟩
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    let some ba ← upper? a depth | return none
    let some bb ← upper? b depth | return none
    return some ⟨ba.v + bb.v, mkNatAdd ba.c bb.c,
      mkApp6 (mkConst ``bnd_add) a b ba.c bb.c ba.h bb.h⟩
  | HMul.hMul _ _ _ _ a k =>
    if let some _ ← natVal? k then
      let some ba ← upper? a depth | return none
      let some kv ← natVal? k | return none
      return some ⟨ba.v * kv, mkNatMul ba.c k, mkApp4 (mkConst ``bnd_mul_right) a ba.c k ba.h⟩
    let some _ ← natVal? a | return none
    let some bk ← upper? k depth | return none
    let some av ← natVal? a | return none
    return some ⟨av * bk.v, mkNatMul a bk.c, mkApp4 (mkConst ``bnd_mul_left) k bk.c a bk.h⟩
  | _ => atomUpper? e depth

/-- The least literal upper bound of an atom `x` from the hypotheses
`x ≤ y`, `x < y`, `x + k ≤ y`, `k + x ≤ y` (and `<`), with `y` bounded. -/
private partial def atomUpper? (x : Expr) (depth : Nat) : MetaM (Option Bnd) := do
  if depth == 0 then return none
  let mut best : Option Bnd := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (a, y, strict) := leHyp? (← instantiateMVars d.type) | continue
    -- `a` is `x`, `x + k` or `k + x`
    let shape? : Option (Option (Expr × Bool)) ← do
      if a == x then pure (some none) else
      match_expr a with
      | HAdd.hAdd _ _ _ _ u w =>
        if u == x then pure ((← natVal? w).map fun _ => some (w, true))
        else if w == x then pure ((← natVal? u).map fun _ => some (u, false))
        else pure none
      | _ => pure none
    let some shape := shape? | continue
    let some by_ ← upper? y (depth - 1) | continue
    -- a bound `a ≤ c`
    let ba : Bnd ←
      if strict then
        -- `a < y ≤ c`, so `a ≤ c - 1`
        let hc := mkApp5 (mkConst ``Nat.lt_of_lt_of_le) a y by_.c d.toExpr by_.h
        pure ⟨by_.v - 1, mkNatSub by_.c (mkNatLit 1), mkApp3 (mkConst ``bnd_of_lt) a by_.c hc⟩
      else
        pure ⟨by_.v, by_.c, mkApp5 (mkConst ``Nat.le_trans) a y by_.c d.toExpr by_.h⟩
    let b : Bnd ← match shape with
      | none => pure ba
      | some (k, right) =>
        let some kv ← natVal? k | continue
        pure ⟨ba.v - kv, mkNatSub ba.c k,
          mkApp4 (mkConst (if right then ``bnd_of_add_le else ``bnd_of_add_le')) x k ba.c ba.h⟩
    if best.all (b.v < ·.v) then best := some b
  return best
end

/-- `c ≤ e` with literal `c`, through `+`, `* k`, and hypotheses `c ≤ e`;
`0` when nothing better is known. -/
private partial def lower (e : Expr) : MetaM Bnd := do
  if let some v ← natVal? e then
    return ⟨v, e, mkApp (mkConst ``Nat.le_refl) e⟩
  let mut best : Bnd := ⟨0, mkNatLit 0, mkApp (mkConst ``Nat.zero_le) e⟩
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (c, y, strict) := leHyp? (← instantiateMVars d.type) | continue
    unless y == e do continue
    let some cv ← natVal? c | continue
    let b : Bnd := if strict then
        ⟨cv + 1, mkNatAdd c (mkNatLit 1), mkApp3 (mkConst ``bnd_of_lt') c e d.toExpr⟩
      else ⟨cv, c, d.toExpr⟩
    if best.v < b.v then best := b
  let b? : Option Bnd ← match_expr e with
    | HAdd.hAdd _ _ _ _ a b =>
      let ba ← lower a
      let bb ← lower b
      pure (some ⟨ba.v + bb.v, mkNatAdd ba.c bb.c, mkApp6 (mkConst ``bnd_add) ba.c bb.c a b ba.h bb.h⟩)
    | HMul.hMul _ _ _ _ a k =>
      if let some kv ← natVal? k then
        let ba ← lower a
        pure (some ⟨ba.v * kv, mkNatMul ba.c k, mkApp4 (mkConst ``bnd_mul_right) ba.c a k ba.h⟩)
      else if let some av ← natVal? a then
        let bk ← lower k
        pure (some ⟨av * bk.v, mkNatMul a bk.c, mkApp4 (mkConst ``bnd_mul_left) bk.c k a bk.h⟩)
      else pure none
    | _ => pure none
  if let some b := b? then
    if best.v < b.v then best := b
  return best

private def trueRefl : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- A hypothesis proving `a ≤ b` (directly, or as `a < b`). -/
private def leFromHyp? (a b : Expr) : MetaM (Option Expr) := do
  if a == b then return some (mkApp (mkConst ``Nat.le_refl) a)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (x, y, strict) := leHyp? (← instantiateMVars d.type) | continue
    if x == a && y == b then
      return some (if strict then mkApp3 (mkConst ``Nat.le_of_lt) a b d.toExpr else d.toExpr)
  return none

/-- `a ≤ b` (`strict = false`) or `a < b` from literal bounds. -/
private def boundProof? (a b : Expr) (strict : Bool) : MetaM (Option Expr) := do
  let some ua ← upper? a 3 | return none
  let lb ← lower b
  if strict then
    unless ua.v < lb.v do return none
    return some (mkApp7 (mkConst ``disch_lt) a b ua.c lb.c ua.h lb.h trueRefl)
  else
    unless ua.v ≤ lb.v do return none
    return some (mkApp7 (mkConst ``disch_le) a b ua.c lb.c ua.h lb.h trueRefl)

/-- A proof of `goal` from literal bounds, or `none`. -/
private def leafProof? (goal : Expr) : MetaM (Option Expr) := do
  if let some (a, b, strict) := leHyp? goal then
    return ← boundProof? a b strict
  let_expr Not p := goal | return none
  -- `¬ b < a` from `a ≤ b`
  let some (b, a, true) := leHyp? p | return none
  if let some h ← leFromHyp? a b then
    return some (mkApp3 (mkConst ``disch_not_lt) a b h)
  let some h ← boundProof? a b false | return none
  return some (mkApp3 (mkConst ``disch_not_lt) a b h)

/-- A proof of `goal` from literal bounds, or `none`; `p ∨ q` (e.g.
non-overlap of two memory ranges) from either side. -/
private def fastProof? (goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  if let some (p, q) := goal.app2? ``Or then
    if let some h ← leafProof? p then return some (mkApp3 (mkConst ``Or.inl) p q h)
    if let some h ← leafProof? q then return some (mkApp3 (mkConst ``Or.inr) p q h)
    return none
  leafProof? goal

/-- A `Nat`/`Int` (in)equation, or a `¬`/`∧`/`∨`/`↔` of one. -/
private partial def isArith (e : Expr) : Bool :=
  let ni (t : Expr) := t.isConstOf ``Nat || t.isConstOf ``Int
  match_expr e with
  | Eq t _ _ => ni t
  | Ne t _ _ => ni t
  | LT.lt t _ _ _ => ni t
  | LE.le t _ _ _ => ni t
  | GT.gt t _ _ _ => ni t
  | GE.ge t _ _ _ => ni t
  | Dvd.dvd t _ _ _ => ni t
  | Not p => isArith p
  | And p q => isArith p || isArith q
  | Or p q => isArith p || isArith q
  | Iff p q => isArith p || isArith q
  | _ => false

/-- Whether `omega` can use anything of `goal` itself: its conclusion (after
`∀`/`→`) or one of its premises is arithmetic. Other goals (`Nonempty …`,
`∀ t, o = Op.jump t → False`, `b = true`; about half of all fallbacks, from the
reflection `simp`) `omega` proves only from contradictory hypotheses. -/
private def omegaApplicable (goal : Expr) : MetaM Bool :=
  forallTelescope goal fun xs c => do
    if isArith c then return true
    xs.anyM fun x => return isArith (← inferType x)

/-- Goals, with their local context, on which `omega` already failed: it would
fail again. A `simp` call meets the same failing side goal (an `if` condition, a
`% 2 ^ 64` it cannot drop) at many instructions. -/
initialize omegaFailed : IO.Ref (Std.HashSet (Expr × Array FVarId)) ← IO.mkRef {}

/-- Discharger of the block tactics: linear bounds from literal bounds, else a
hypothesis matching up to reducible unfolding, else `omega` (on arithmetic goals
only, and not again on a goal it already failed on in the same context).

(`assumption` at default transparency is avoided on purpose: on goals such as
`word M rp / 2 ^ sh < 2 ^ 256` it unfolds `<`, `/` and `word` against every
hypothesis, which took half of the time of `MlDsaOpt44.Fn.Fix.Blocks`.) -/
elab "blk_disch" : tactic => do
  let g ← getMainGoal
  let done ← g.withContext do
    let tgt ← g.getType
    if let some p ← fastProof? tgt then
      if ← isDefEq (← inferType p) tgt then
        g.assign p
        return true
    withReducible g.assumptionCore
  if done then
    replaceMainGoal []
    return
  let (tgt, key) ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    return (tgt, (tgt, (← getLCtx).getFVarIds))
  unless ← g.withContext (omegaApplicable tgt) do
    throwError "blk_disch: not an arithmetic goal{indentExpr tgt}"
  if (← omegaFailed.get).contains key then
    throwError "blk_disch: omega already failed on{indentExpr tgt}"
  trace[blk_disch] "fallback: {tgt}"
  try
    evalTactic (← `(tactic| omega))
  catch ex =>
    unless tgt.hasMVar do
      omegaFailed.modify fun c => (if c.size > 100000 then {} else c).insert key
    throw ex

initialize registerTraceClass `blk_disch

end MlDsaOptCommon
