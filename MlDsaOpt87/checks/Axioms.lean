import MlDsaOpt87
/-! Axiom check (`lake env lean MlDsaOpt87/checks/Axioms.lean`).

1. `#print axioms` of the four final theorems: `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx`.
2. The open items: every `MlDsaOpt87` declaration whose own proof term contains
   `sorryAx` (the deliberate `sorry`s), and those the final theorems
   transitively depend on.
3. `#print axioms` of the contracts proved by porting (no `sorryAx`). -/

#print axioms MlDsaOpt87.Proofs.opt_correctInAnyContextWithSchedule
#print axioms MlDsaOpt87.Proofs.opt_correctInAnyContext
#print axioms MlDsaOpt87.Proofs.opt_correctWithSchedule
#print axioms MlDsaOpt87.Proofs.opt_correct

open Lean in
/-- The proof term of a definition or theorem (`value?` omits imported theorems). -/
def constValue? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | _ => none

open Lean Elab Command in
elab "#open_items" : command => do
  let env ← getEnv
  let mine := env.constants.toList.filter fun (n, _) => (`MlDsaOpt87).isPrefixOf n
  let direct := mine.filterMap fun (n, ci) =>
    match constValue? ci with
    | some v => if v.getUsedConstants.contains ``sorryAx then some n else none
    | none => none
  logInfo m!"declarations with a direct sorry ({direct.length}): {direct.map (·.toString) |>.toArray.qsort (· < ·)}"
  -- transitive dependencies of the final theorem
  let mut seen : NameSet := {}
  let mut todo : List Name := [`MlDsaOpt87.Proofs.opt_correctInAnyContextWithSchedule]
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
      if (`MlDsaOpt87).isPrefixOf c && !seen.contains c then todo := c :: todo
  logInfo m!"open items the final theorems depend on ({hits.size}): {hits.map (·.toString) |>.qsort (· < ·)}"

#open_items

#print axioms MlDsaOpt87.Proofs.kf4_call
#print axioms MlDsaOpt87.Proofs.kf1_call
#print axioms MlDsaOpt87.Proofs.blk_call
#print axioms MlDsaOpt87.Proofs.spr_call
#print axioms MlDsaOpt87.Proofs.trabs_call
#print axioms MlDsaOpt87.Proofs.cext_call
#print axioms MlDsaOpt87.Proofs.absorb17_call
#print axioms MlDsaOpt87.Proofs.fix_call
#print axioms MlDsaOpt87.Proofs.gfix_call
#print axioms MlDsaOpt87.Proofs.tbuild_call
#print axioms MlDsaOpt87.Proofs.ntt_call
#print axioms MlDsaOpt87.Proofs.intt_call
#print axioms MlDsaOpt87.Proofs.pass3_call
#print axioms MlDsaOpt87.Proofs.ginit_call
#print axioms MlDsaOpt87.Proofs.group_call
#print axioms MlDsaOpt87.Proofs.pass3k14_call
#print axioms MlDsaOpt87.Proofs.pass3m_call
#print axioms MlDsaOpt87.Proofs.seg_mu
#print axioms MlDsaOpt87.Proofs.csum_call
#print axioms MlDsaOpt87.Proofs.csum_congr
#print axioms MlDsaOpt87.Proofs.csum_lt
#print axioms MlDsaOpt87.Proofs.usehint_call
#print axioms MlDsaOpt87.Proofs.pack_call
#print axioms MlDsaOpt87.Proofs.useHint_emod
#print axioms MlDsaOpt87.Proofs.useHint_range
#print axioms MlDsaOpt87.Proofs.finBytes_le64_mu
#print axioms MlDsaOpt87.Proofs.finBytes_le64_w1
#print axioms MlDsaOpt87.Proofs.accepts_eq_optAccepts
#print axioms MlDsaOpt87.Proofs.sampleInBallOf_coeffs
#print axioms MlDsaOpt87.Proofs.hintBitUnpack_range
#print axioms MlDsaOpt87.Proofs.ntt_zLane
