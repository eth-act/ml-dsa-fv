import MlDsa44.Proofs.Infra.Code
import MlDsa44.Proofs.Infra.Word
import MlDsa44.Proofs.Infra.Memory
import MlDsaOptCommon.Chunk
import MlDsaOptCommon.StateProj
import MlDsaOptCommon.Disch
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Straight-line block execution

`runLocatedBlock path s` is rewritten to a left fold `path.foldl stepL (some s)`
(`runLocatedBlock_eq_foldl`).  Under `simp`, `List.foldl_cons` then exposes
exactly one instruction at a time: the head `stepL (some st) l` is reduced to
`some st'` (via `runLocated`, `runInstr` and the simprocs of `Infra.Code`)
before the next fold step is visited, so the term never contains the
unfolded remainder of the path (the quadratic blow-up of unfolding
`runLocatedBlock` directly).

The tactic `evm_block [extra lemmas]` packages the whole recipe. It runs the
path in pieces of 32 instructions (`foldl_chunks`, `MlDsaOptCommon.Chunk`):
one `simp` over a long path makes a proof whose kernel check grows much faster
than the path. The `halt = .Running` premise is closed by
`with_reducible assumption` or `simp` (plain `assumption` unfolded the state
against every hypothesis: about 30 s of `MlDsaOpt44.Fn.Fix.Blocks`). Side
goals of the `simp` go to `blk_disch` (`MlDsaOptCommon.Disch`).
-/

namespace MlDsa44.Proofs.Infra

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact

/-- Run `l` on `s` if `s` is still running. -/
def runIfRunning {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (s : State) (l : Located artifact fork) : Option State :=
  match s.halt with
  | .Running => runLocated l s
  | _ => none

/-- One fold step: run `l` if the state is still running. -/
def stepL {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (acc : Option State) (l : Located artifact fork) : Option State :=
  acc.bind fun s => runIfRunning s l

theorem stepL_some {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (s : State) (l : Located artifact fork) :
    stepL (some s) l = runIfRunning s l := rfl

theorem stepL_none {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (l : Located artifact fork) : stepL none l = none := rfl

/-- Not a `rfl` lemma on purpose: `simp` then records an explicit proof step
instead of a definitional unfolding that the kernel would re-check by
evaluating `runLocated` (and with it `instructionPC`) from scratch. -/
theorem runIfRunning_of {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    {s : State} (l : Located artifact fork) (h : s.halt = .Running) :
    runIfRunning s l = runLocated l s := by
  unfold runIfRunning; rw [h]

theorem foldl_stepL_none {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) : path.foldl stepL none = none := by
  induction path with
  | nil => rfl
  | cons l rest ih => simpa [List.foldl_cons, stepL_none] using ih

theorem runLocatedBlock_eq_foldl {artifact : EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (s : State) (h : s.halt = .Running) :
    runLocatedBlock path s = path.foldl stepL (some s) := by
  induction path generalizing s with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl_cons, stepL_some, runIfRunning_of l h]
    cases hl : runLocated l s with
    | none => simp [runLocatedBlock, hl, foldl_stepL_none]
    | some t =>
      cases rest with
      | nil => simp [runLocatedBlock, hl]
      | cons x r =>
        have hstep : (x :: r).foldl stepL (some t) = (x :: r).foldl stepL
            (match t.halt with | .Running => some t | _ => none) := by
          cases ht : t.halt <;> simp [List.foldl_cons, stepL_some, stepL_none, runIfRunning, ht, foldl_stepL_none]
        rw [hstep]
        cases ht : t.halt with
        | Running => rw [← ih t ht]; simp [runLocatedBlock, hl, ht]
        | _ => simp [runLocatedBlock, hl, ht, stepL_none, foldl_stepL_none]

/-- Pass `o` through iff the halt flag is `Running`. -/
def guardHalt (h : HaltKind) (o : Option State) : Option State :=
  match h with
  | .Running => o
  | _ => none

theorem guardHalt_running (o : Option State) : guardHalt .Running o = o := rfl

/-- The step lemma used by `evm_block`: one fold step at instruction `i`,
with instruction and offset read from the lookup trees.  It is a theorem (not
a definitional unfolding) so the kernel never re-evaluates `runLocated`. -/
theorem stepL_located (i : Fin 3375) (st : State) :
    stepL (some st) (located i) =
      guardHalt st.halt
        (if st.pc.toNat = pcAt i.val then runInstr (instrAt i.val) st else none) := by
  rw [stepL_some, runIfRunning, EvmProof.Stepper.runLocated,
    located_instruction_eq, located_index_eq,
    instructionPC_eq_pcAt (by have := i.isLt; omega)]
  rfl

/-- `PUSH0` pushes the literal word `⟨0⟩`; normalize it to `UInt256.ofNat 0`. -/
theorem push0_eq : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := rfl

open Lean Meta Simp in
/-- `Fin.val` of a `Fin` literal ↦ the `Nat` literal (push widths, DUP/SWAP
indices). -/
dsimproc_decl finVal_lit (Fin.val _) := fun e => do
  unless e.isAppOfArity ``Fin.val 2 do return .continue
  let some v ← getFinValue? (e.getArg! 1) | return .continue
  return .done (mkNatLit v.2.val)


end MlDsa44.Proofs.Infra

/-- Symbolically execute a straight-line located path.

Goal shape: `EvmProof.Stepper.runLocatedBlock (Artifact.locatedPath [i₀, …]) st = rhs`
where `st` is concrete enough for `simp` to read its `pc`, stack shape, `halt`
and code (e.g. `callState s pc stk m` with `hs : Ctx s` in context, which the
tactic uses through `hs.code`/`hs.running`).  The stack-capacity checks are
discharged by `blk_disch`, so keep a hypothesis like `htail : tail.length ≤ 960`
in context.  Extra simp lemmas (value definitions of the target state,
memory facts, …) go in the brackets. -/
syntax "evm_block" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evm_block) => `(tactic| evm_block [])
  | `(tactic| evm_block [$extra,*]) => `(tactic| (
      rw [MlDsa44.Proofs.Infra.runLocatedBlock_eq_foldl _ _
        (by first | with_reducible assumption | simp (disch := assumption) only [MlDsa44.Proofs.callState, MlDsa44.Proofs.Ctx.running])]
      try rw [MlDsa44.Proofs.Artifact.locatedPath]
      foldl_chunks 32 => simp (config := { maxSteps := 4000000, maxDischargeDepth := 1 })
          (disch := blk_disch) only
        [MlDsa44.Proofs.Artifact.locatedPath, List.map_cons, List.map_nil, List.foldl_cons,
         List.foldl_nil, MlDsa44.Proofs.Infra.stepL_located, MlDsa44.Proofs.Infra.stepL_none,
         MlDsa44.Proofs.Infra.guardHalt_running, EvmProof.Stepper.runInstr,
         state_proj,
         MlDsa44.Proofs.callState, MlDsa44.Proofs.wd,
         MlDsa44.Proofs.Infra.instrAt_lit, MlDsa44.Proofs.Infra.pcAt_lit,
         MlDsa44.Proofs.Infra.isValidJumpDest_lit,
         MlDsa44.Proofs.Infra.finVal_lit, MlDsa44.Proofs.Infra.push0_eq,
         EvmProof.Word.word_toNat_ofNat, EvmProof.Word.succ_ofNat_mod,
         EvmProof.Word.ofNat_add_mod, EvmProof.Word.literal_eq_ofNat,
         MlDsa44.Proofs.Infra.ofNat_land, MlDsa44.Proofs.Infra.ofNat_lor,
         MlDsa44.Proofs.Infra.ofNat_xor, MlDsa44.Proofs.Infra.ofNat_mul,
         MlDsa44.Proofs.Infra.ofNat_shl, MlDsa44.Proofs.Infra.ofNat_shr,
         MlDsa44.Proofs.Infra.ofNat_sub, MlDsa44.Proofs.Infra.ofNat_lt,
         MlDsa44.Proofs.Infra.ofNat_gt, MlDsa44.Proofs.Infra.ofNat_eq,
         MlDsa44.Proofs.Infra.ofNat_isZero, MlDsa44.Proofs.Infra.isTrue_ofNat,
         MlDsa44.Proofs.Infra.ofNat_toNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
         EvmSemantics.EVM.State.activeWordsAfterUInt256,
         MlDsa44.Proofs.Infra.activeWordsAfter_of_le, Nat.mod_eq_of_lt,
         MlDsa44.Proofs.Infra.readWord_eq_word, MlDsa44.Proofs.Infra.word_mod,
         MlDsa44.Proofs.Ctx.code, MlDsa44.Proofs.Ctx.running,
         List.length_cons, List.length_nil, List.length_singleton, List.replicate_succ, List.replicate_zero, List.cons_append,
         List.nil_append, List.append_nil, List.singleton_append, List.exchange, List.getElem?_cons_succ, List.getElem?_cons_zero,
         List.set_cons_succ, List.set_cons_zero, Option.bind_eq_bind, Option.bind_some,
         Option.pure_def, Option.some.injEq, EvmSemantics.EVM.State.mk.injEq,
         EvmSemantics.SharedState.mk.injEq, EvmSemantics.MachineState.mk.injEq,
         List.cons.injEq, and_true, true_and, ne_eq, not_true_eq_false, not_false_eq_true,
         Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
         Nat.reduceDiv, Nat.reduceAnd, Nat.reduceOr, Nat.reduceXor, Nat.reduceShiftLeft,
         Nat.reduceShiftRight, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceGT,
         ↓reduceIte, eq_self_iff_true, if_true, if_false, if_pos, if_neg, $extra,*]))
