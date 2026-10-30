import MlDsa44.Proofs.Layout
set_option warningAsError true
/-!
# Instruction-address facts for the frozen artifact

The kernel walks `referenceInstructions` (3375 entries behind nine appended
`have`-chunked literals) at roughly 0.2 ms per element, so every proof that
reduced `referenceArtifact.instructionPC n` or `referenceInstructions[n]` by
evaluation paid O(n) of that per instruction.  Instead:

* `instrTree` / `pcTree` are balanced binary lookup trees (bit-interleaved
  indexing, depth 12) holding every instruction and every byte offset,
  generated from the artifact by `mldsa_define_tables`.
* `tables_ok` validates both trees against `referenceInstructions` with ONE
  linear Boolean pass (`checkAll`, offsets checked incrementally:
  `pc(k+1) = pc(k) + isz instr(k)`), evaluated once by the kernel.
* `instrTree_get` / `pcTree_get` then give every lookup in 12 kernel steps;
  `pcOf n` is the specification of offsets and `instructionPC_eq_pcOf` ties it
  to `referenceArtifact.instructionPC`.
* `jumpdest_of n pc (by decide +kernel)` proves
  `Decode.isValidJumpDest referenceBytecode pc = true` for every JUMPDEST.
* `instrAt n` / `pcAt n` read the trees; `located_instruction_eq` and
  `instructionPC_eq_pcAt` connect them to `located` / `instructionPC`.
  Proof terms must not make the kernel unfold `located i` or
  `instructionPC n` (each walks the list: ~1 s of kernel time).
* Simprocs for `simp`: `instrAt_lit` / `pcAt_lit` replace `instrAt n` and
  `pcAt n` by literals,
  `instructionPC_lit` replaces `referenceArtifact.instructionPC n` by its
  literal offset, and `isValidJumpDest_lit` rewrites
  `Decode.isValidJumpDest referenceBytecode pc` to `true` at JUMPDESTs.
-/

namespace MlDsa44.Proofs.Infra

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open MlDsa44.Proofs.Artifact

/-- Byte size of an instruction, without encoding it. -/
def isz : Instr → Nat
  | .push w _ => 1 + w.val
  | .op _ => 1

theorem bytes_length_eq_isz (i : Instr) : i.bytes.length = isz i := by
  cases i <;> simp [isz]

theorem assembleBytes_length (l : List Instr) :
    (assembleBytes l).length = (l.map isz).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih, bytes_length_eq_isz]

/-- Byte offset of instruction `n` of the reference artifact. -/
def pcOf (n : Nat) : Nat := ((referenceInstructions.take n).map isz).sum

theorem instructionPC_eq_pcOf (n : Nat) :
    referenceArtifact.instructionPC n = pcOf n := by
  unfold EvmProof.ProgramArtifact.instructionPC pcOf
  exact assembleBytes_length _

/-! ## Lookup trees -/

/-- A binary lookup tree; `get` reads index bits from least significant. -/
inductive BTree (α : Type) where
  | leaf (a : Option α)
  | node (l r : BTree α)

def BTree.get {α : Type} : BTree α → Nat → Option α
  | .leaf a, _ => a
  | .node l r, i => if i % 2 = 0 then l.get (i / 2) else r.get (i / 2)

/-- Boolean instruction equality (`Instr` has no `DecidableEq`). -/
def instrBEq : Instr → Instr → Bool
  | .push w v, .push w' v' => decide (w = w') && decide (v = v')
  | .op o, .op o' => decide (o = o')
  | _, _ => false

theorem eq_of_instrBEq {a b : Instr} (h : instrBEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [instrBEq]

def optInstrBEq : Option Instr → Instr → Bool
  | some a, b => instrBEq a b
  | none, _ => false

theorem eq_of_optInstrBEq {a : Option Instr} {b : Instr}
    (h : optInstrBEq a b = true) : a = some b := by
  cases a with
  | none => cases h
  | some a => rw [eq_of_instrBEq h]

/-- One linear pass checking both trees from index `k`, offset `pc`. -/
def checkAll (t : BTree Instr) (p : BTree Nat) : Nat → Nat → List Instr → Bool
  | k, pc, [] => p.get k == some pc
  | k, pc, i :: is =>
      optInstrBEq (t.get k) i && p.get k == some pc && checkAll t p (k + 1) (pc + isz i) is

theorem checkAll_spec (t : BTree Instr) (p : BTree Nat) :
    ∀ (l : List Instr) (k pc : Nat), checkAll t p k pc l = true →
      (∀ j, j < l.length → t.get (k + j) = l[j]?) ∧
      (∀ j, j ≤ l.length → p.get (k + j) = some (pc + ((l.take j).map isz).sum)) := by
  intro l
  induction l with
  | nil =>
    intro k pc h
    simp only [checkAll, beq_iff_eq] at h
    refine ⟨fun j hj => by simp at hj, fun j hj => ?_⟩
    simp at hj; subst hj; simpa using h
  | cons i is ih =>
    intro k pc h
    simp only [checkAll, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hi, hp⟩, hrest⟩ := h
    obtain ⟨ih1, ih2⟩ := ih (k + 1) (pc + isz i) hrest
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero => simpa using eq_of_optInstrBEq hi
      | succ j =>
        have := ih1 j (by simpa using hj)
        rw [show k + (j + 1) = k + 1 + j by omega, this]
        simp
    · cases j with
      | zero => simpa using hp
      | succ j =>
        have := ih2 j (by simpa using hj)
        rw [show k + (j + 1) = k + 1 + j by omega, this]
        simp [Nat.add_assoc]

/-! ## Meta-level view of the instruction list -/

section Meta
open Lean Meta Elab Command

/-- The instruction `Expr`s of `referenceInstructions`, in order. -/
def instrExprs : MetaM (Array Expr) := do
  let mut out := #[]
  for k in [0:9] do
    let name := Name.mkStr `MlDsa44.Proofs.Artifact s!"instructions{k}"
    let some v := (← getEnv).find? name |>.bind (·.value?) | throwError "missing {name}"
    let mut e := v
    -- Long list literals are elaborated as `have y := tail; a :: … :: y`.
    repeat
      if let .letE _ _ val body _ := e then
        e := body.instantiate1 val
      else if e.isAppOfArity ``List.cons 3 then
        out := out.push (e.getArg! 1)
        e := e.getArg! 2
      else break
  return out

/-- Byte size of an instruction `Expr` (`Instr.push w v` or `Instr.op o`). -/
def instrExprSize (e : Expr) : MetaM Nat := do
  if e.isAppOfArity ``Instr.push 2 then
    let w := e.getArg! 0
    let some (n : Nat) := (← getFinValue? w).map (fun v => v.2.val)
      | throwError "unexpected push width {w}"
    return 1 + n
  return 1

/-- Byte offsets of all instructions plus the end offset. -/
def pcValues : MetaM (Array Nat) := do
  let mut out := #[0]
  let mut pc := 0
  for i in (← instrExprs) do
    pc := pc + (← instrExprSize i)
    out := out.push pc
  return out

/-- Build the bit-interleaved tree literal over `elems`. -/
partial def treeExpr (ty : Expr) (elems : Array Expr) : Expr :=
  if elems.size ≤ 1 then
    mkApp2 (mkConst ``BTree.leaf) ty <| match elems[0]? with
      | some e => mkApp2 (mkConst ``Option.some [0]) ty e
      | none => mkApp (mkConst ``Option.none [0]) ty
  else
    let evens := (List.range ((elems.size + 1) / 2)).toArray.map (fun i => elems[2 * i]!)
    let odds := (List.range (elems.size / 2)).toArray.map (fun i => elems[2 * i + 1]!)
    mkApp3 (mkConst ``BTree.node) ty (treeExpr ty evens) (treeExpr ty odds)

elab "mldsa_define_tables" : command => liftTermElabM do
  let instrTy := mkConst ``Instr
  let instrs ← instrExprs
  let pcs ← pcValues
  for (name, ty, elems) in [(`MlDsa44.Proofs.Infra.instrTree, instrTy, instrs),
      (`MlDsa44.Proofs.Infra.pcTree, mkConst ``Nat, pcs.map mkNatLit)] do
    addDecl <| .defnDecl {
      name, levelParams := [], type := mkApp (mkConst ``BTree) ty
      value := treeExpr ty elems, hints := .opaque, safety := .safe }

end Meta

mldsa_define_tables

/-- The single linear validation of both trees (one kernel evaluation). -/
theorem tables_ok : checkAll instrTree pcTree 0 0 referenceInstructions = true := by
  decide +kernel

theorem instrTree_get {n : Nat} (h : n < 3375) : instrTree.get n = referenceInstructions[n]? := by
  have := (checkAll_spec _ _ _ _ _ tables_ok).1 n (by simpa using h)
  simpa using this

theorem pcTree_get {n : Nat} (h : n ≤ 3375) : pcTree.get n = some (pcOf n) := by
  have := (checkAll_spec _ _ _ _ _ tables_ok).2 n (by simpa using h)
  simpa [pcOf] using this

/-- Offset from a tree lookup (kernel: 12 steps). -/
theorem instructionPC_eq_of (n pc : Nat)
    (h : (decide (n ≤ 3375) && pcTree.get n == some pc) = true) :
    referenceArtifact.instructionPC n = pc := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [instructionPC_eq_pcOf]
  rw [pcTree_get h.1] at h
  exact Option.some.inj h.2

/-! ## Tree-backed instruction and offset accessors

Proof terms must never make the kernel unfold `Artifact.located i` or
`referenceArtifact.instructionPC n`: both walk the 3375-element list (and the
latter encodes every byte), ~1 s of kernel time per occurrence.  `instrAt` /
`pcAt` read the trees instead; `located_instruction_eq` and
`instructionPC_eq_pcAt` are the propositional bridges. -/

/-- Instruction `n`, read from the lookup tree. -/
noncomputable def instrAt (n : Nat) : Instr := (instrTree.get n).getD (.op .INVALID)

/-- Byte offset of instruction `n`, read from the lookup tree. -/
noncomputable def pcAt (n : Nat) : Nat := (pcTree.get n).getD 0

theorem located_instruction_eq (i : Fin 3375) : (located i).instruction = instrAt i.val := by
  have h := instrTree_get i.isLt
  rw [List.getElem?_eq_getElem (by simp)] at h
  change referenceInstructions[i.val]'_ = (instrTree.get i.val).getD _
  rw [h]
  rfl

theorem located_index_eq (i : Fin 3375) : (located i).index = i.val := rfl

theorem instructionPC_eq_pcAt {n : Nat} (h : n ≤ 3375) :
    referenceArtifact.instructionPC n = pcAt n := by
  rw [instructionPC_eq_pcOf, pcAt, pcTree_get h]
  rfl

theorem instrAt_of (n : Nat) (instr : Instr)
    (h : optInstrBEq (instrTree.get n) instr = true) : instrAt n = instr := by
  unfold instrAt
  rw [eq_of_optInstrBEq h]
  rfl

theorem pcAt_of (n pc : Nat) (h : (pcTree.get n == some pc) = true) : pcAt n = pc := by
  unfold pcAt
  rw [eq_of_beq h]
  rfl

/-! ## Jump destinations -/

def isJumpdest : Instr → Bool
  | .op .JUMPDEST => true
  | _ => false

theorem eq_of_isJumpdest {i : Instr} (h : isJumpdest i = true) : i = .op .JUMPDEST := by
  unfold isJumpdest at h
  split at h
  · rfl
  · cases h

/-- Kernel-evaluable check that instruction `n` is a JUMPDEST at byte `pc`. -/
noncomputable def jumpdestAt (n pc : Nat) : Bool :=
  decide (n < 3375) && (instrTree.get n).map isJumpdest == some true && pcTree.get n == some pc

/-- Every JUMPDEST instruction's offset is a valid jump target, e.g.
`jumpdest_of 1931 3028 (by decide +kernel)`; the simproc
`isValidJumpDest_lit` finds the index itself. -/
theorem jumpdest_of (n pc : Nat) (h : jumpdestAt n pc = true) :
    Decode.isValidJumpDest referenceBytecode pc = true := by
  simp only [jumpdestAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hn, h⟩, hpc⟩ := h
  rw [pcTree_get (by omega)] at hpc
  rw [instrTree_get hn] at h
  cases hget : referenceInstructions[n]? with
  | none => rw [hget] at h; cases h
  | some i =>
    rw [hget] at h
    have hi : i = .op .JUMPDEST := eq_of_isJumpdest (Option.some.inj h)
    subst hi
    have := referenceArtifact.isValidJumpDest_index n hget
    rw [instructionPC_eq_pcOf, Option.some.inj hpc] at this
    exact this

/-! ## Simprocs -/

section Simprocs
open Lean Meta Simp

def instrExprIsJumpdest (e : Expr) : Bool :=
  e.isAppOfArity ``Instr.op 1 &&
    (e.getArg! 0).isAppOfArity ``Operation.StackMemFlow 1 &&
    ((e.getArg! 0).getArg! 0).isConstOf ``Operation.StackMemFlowOps.JUMPDEST

/-- Index argument of `instructionPC` as a literal. -/
def indexLit? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  let e ← instantiateMVars e
  if e.isAppOfArity ``EvmProof.Stepper.Located.index 3 then
    let l := e.getArg! 2
    if l.isAppOfArity ``MlDsa44.Proofs.Artifact.located 1 then
      if let some v ← getFinValue? (l.getArg! 0) then return some v.2.val
  if e.isAppOfArity ``Fin.val 2 then
    if let some v ← getFinValue? (e.getArg! 1) then return some v.2.val
  return none

private def trueRefl : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- `instrAt n` ↦ the literal instruction. -/
simproc_decl instrAt_lit (instrAt _) := fun e => do
  unless e.isAppOfArity ``instrAt 1 do return .continue
  let some n := (e.getArg! 0).nat? | return .continue
  let instrs ← instrExprs
  let some instr := instrs[n]? | return .continue
  let proof := mkApp3 (mkConst ``instrAt_of) (mkNatLit n) instr trueRefl
  return .done { expr := instr, proof? := some proof }

/-- `pcAt n` ↦ the literal byte offset. -/
simproc_decl pcAt_lit (pcAt _) := fun e => do
  unless e.isAppOfArity ``pcAt 1 do return .continue
  let some n := (e.getArg! 0).nat? | return .continue
  let pcs ← pcValues
  let some pc := pcs[n]? | return .continue
  let proof := mkApp3 (mkConst ``pcAt_of) (mkNatLit n) (mkNatLit pc) trueRefl
  return .done { expr := mkNatLit pc, proof? := some proof }

/-- `referenceArtifact.instructionPC n` ↦ its literal byte offset. -/
simproc_decl instructionPC_lit
    (EvmProof.ProgramArtifact.instructionPC referenceArtifact _) := fun e => do
  unless e.isAppOfArity ``EvmProof.ProgramArtifact.instructionPC 2 do return .continue
  let some n ← indexLit? (e.getArg! 1) | return .continue
  let pcs ← pcValues
  let some pc := pcs[n]? | return .continue
  let lit := mkNatLit pc
  let proof := mkApp3 (mkConst ``instructionPC_eq_of) (mkNatLit n) lit trueRefl
  -- `e` may mention the index through `Located.index`; restate the
  -- conclusion at the original argument (definitionally equal).
  return .done { expr := lit, proof? := some (← mkExpectedTypeHint proof (← mkEq e lit)) }

/-- `Decode.isValidJumpDest referenceBytecode pc` ↦ `true` at JUMPDESTs. -/
simproc_decl isValidJumpDest_lit
    (Decode.isValidJumpDest MlDsa44.referenceBytecode _) := fun e => do
  unless e.isAppOfArity ``Decode.isValidJumpDest 2 do return .continue
  let some pc := (e.getArg! 1).nat? | return .continue
  let instrs ← instrExprs
  let pcs ← pcValues
  let some k := (List.range instrs.size).find? (fun k =>
      pcs[k]! == pc && instrExprIsJumpdest instrs[k]!) | return .continue
  let proof := mkApp3 (mkConst ``jumpdest_of) (mkNatLit k) (mkNatLit pc) trueRefl
  return .done { expr := mkConst ``Bool.true, proof? := some proof }

end Simprocs

end MlDsa44.Proofs.Infra
