import MlDsaOpt65
/-! Axiom check (`lake env lean MlDsaOpt65/checks/Axioms.lean`).

1. `#print axioms` of the four final theorems: `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx`.
2. The open items: every `MlDsaOpt65` declaration whose own proof term contains
   `sorryAx` (the deliberate `sorry`s), and those the final theorems
   transitively depend on.
3. `#print axioms` of the contracts proved by porting (no `sorryAx`). -/

#print axioms MlDsaOpt65.Proofs.opt_correctInAnyContextWithSchedule
#print axioms MlDsaOpt65.Proofs.opt_correctInAnyContext
#print axioms MlDsaOpt65.Proofs.opt_correctWithSchedule
#print axioms MlDsaOpt65.Proofs.opt_correct

open Lean in
/-- The proof term of a definition or theorem (`value?` omits imported theorems). -/
def constValue? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | _ => none

open Lean Elab Command in
elab "#open_items" : command => do
  let env ← getEnv
  let mine := env.constants.toList.filter fun (n, _) => (`MlDsaOpt65).isPrefixOf n
  let direct := mine.filterMap fun (n, ci) =>
    match constValue? ci with
    | some v => if v.getUsedConstants.contains ``sorryAx then some n else none
    | none => none
  logInfo m!"declarations with a direct sorry ({direct.length}): {direct.map (·.toString) |>.toArray.qsort (· < ·)}"
  -- transitive dependencies of the final theorem
  let mut seen : NameSet := {}
  let mut todo : List Name := [`MlDsaOpt65.Proofs.opt_correctInAnyContextWithSchedule]
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
      if (`MlDsaOpt65).isPrefixOf c && !seen.contains c then todo := c :: todo
  logInfo m!"open items the final theorems depend on ({hits.size}): {hits.map (·.toString) |>.qsort (· < ·)}"

#open_items

#print axioms MlDsaOpt65.Proofs.kf4_call
#print axioms MlDsaOpt65.Proofs.kf1_call
#print axioms MlDsaOpt65.Proofs.blk_call
#print axioms MlDsaOpt65.Proofs.spr_call
#print axioms MlDsaOpt65.Proofs.trabs_call
#print axioms MlDsaOpt65.Proofs.cext_call
#print axioms MlDsaOpt65.Proofs.absorb17_call
#print axioms MlDsaOpt65.Proofs.fix_call
#print axioms MlDsaOpt65.Proofs.gfix_call
#print axioms MlDsaOpt65.Proofs.tbuild_call
#print axioms MlDsaOpt65.Proofs.ntt_call
#print axioms MlDsaOpt65.Proofs.intt_call
#print axioms MlDsaOpt65.Proofs.pass3_call
#print axioms MlDsaOpt65.Proofs.mu0_call
#print axioms MlDsaOpt65.Proofs.seg_mu
#print axioms MlDsaOpt65.Proofs.csum_call
#print axioms MlDsaOpt65.Proofs.csum_congr
#print axioms MlDsaOpt65.Proofs.csum_lt
