import MlDsaOptGlam44
/-! Axiom check (`lake env lean MlDsaOptGlam44/checks/Axioms.lean`).

1. `#print axioms` of the four final theorems.
2. The open items: every `MlDsaOptGlam44` declaration whose own proof term contains
   `sorryAx`, and those the final theorems transitively depend on. -/

#print axioms MlDsaOptGlam44.Proofs.opt_correctInAnyContextWithSchedule
#print axioms MlDsaOptGlam44.Proofs.opt_correctInAnyContext
#print axioms MlDsaOptGlam44.Proofs.opt_correctWithSchedule
#print axioms MlDsaOptGlam44.Proofs.opt_correct

open Lean in
/-- The proof term of a definition or theorem (`value?` omits imported theorems). -/
def constValue? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | _ => none

open Lean Elab Command in
elab "#open_items" : command => do
  let env ← getEnv
  let mine := env.constants.toList.filter fun (n, _) => (`MlDsaOptGlam44).isPrefixOf n
  let direct := mine.filterMap fun (n, ci) =>
    match constValue? ci with
    | some v => if v.getUsedConstants.contains ``sorryAx then some n else none
    | none => none
  logInfo m!"declarations with a direct sorry ({direct.length}): {direct.map (·.toString) |>.toArray.qsort (· < ·)}"
  -- transitive dependencies of the final theorem
  let mut seen : NameSet := {}
  let mut todo : List Name := [`MlDsaOptGlam44.Proofs.opt_correctInAnyContextWithSchedule]
  let mut hits : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let some v := constValue? ci | continue
    let cs := v.getUsedConstants
    if cs.contains ``sorryAx then hits := hits.push n
    for c in cs do
      if (`MlDsaOptGlam44).isPrefixOf c && !seen.contains c then todo := c :: todo
  logInfo m!"open items the final theorems depend on ({hits.size}): {hits.map (·.toString) |>.qsort (· < ·)}"

#open_items

#print axioms MlDsaOptGlam44.Proofs.Kf4.kf4_spec
#print axioms MlDsaOptGlam44.Proofs.Kf1.kf1_spec
