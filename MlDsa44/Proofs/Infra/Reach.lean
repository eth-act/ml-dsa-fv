import MlDsa44.Proofs.Infra.Block
set_option warningAsError true
/-!
# Composition: `Reach`, blocks, calls and loops

`Reach s t c` (a trace from `s` to `t` costing at most `c` gas) is exactly the
body of `Call`, so callee contracts plug into caller traces without casts
(`call_iff`).  Everything composes by `Reach.trans` (costs add) and
`Reach.mono`.

* `reach_block`: a straight-line block proved by `evm_block` between two
  `callState s …` states costs exactly its static opcode sum `blockCost path`
  (memory never grows: both ends share `s.activeWords`).
* `Reach.loop`: an `n`-iteration loop from a state family `I` with per-iteration
  bound `c` costs `n * c`; `Reach.loopSum` allows an iteration-dependent bound.
-/

namespace MlDsa44.Proofs.Infra

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact

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

/-- `Call` is `Reach` between the entry and return states. -/
theorem call_iff {s : State} {entry : Nat} {args : List UInt256} {ret : Nat}
    {tail : List UInt256} {pre : ByteArray} {results : List UInt256} {post : ByteArray}
    {gas : Nat} :
    Call s entry args ret tail pre results post gas ↔
      Reach (callState s entry
          (args ++ List.replicate results.length (UInt256.ofNat 0) ++ UInt256.ofNat ret :: tail)
          pre)
        (callState s ret (results ++ tail) post) gas := Iff.rfl

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

/-- Discharge a callee's `RetOK` at a call site.  The caller holds
`hr : RetOK B ret tail`; at the call the callee's tail is `extra ++ tail`, where
`extra` is everything the caller has above its own tail (its locals and the
return address it was given), at most 64 slots.  Callee budgets are 64 below
the caller's (`Stack.*`), so `hB` is closed by `simp [Stack.…]` or `decide`. -/
theorem _root_.MlDsa44.Proofs.RetOK.callee {B B' ret ret' : Nat} {tail extra : List UInt256}
    (hr : RetOK B ret tail) (hB : B' + 64 ≤ B) (hextra : extra.length ≤ 64)
    (hj : Decode.isValidJumpDest referenceBytecode ret' = true) (hsmall : ret' < 2 ^ 16) :
    RetOK B' ret' (extra ++ tail) :=
  ⟨hj, hsmall, by have := hr.depth; simp only [List.length_append]; omega⟩

/-! ## Straight-line blocks -/

/-- Static (memory-free) cost of a path, from the lookup trees. -/
noncomputable def blockCost (path : List (Fin 3375)) : Nat :=
  (path.map fun i => EvmProof.Meter.instrStaticCost .Osaka (instrAt i.val)).sum

/-- Kernel-checkable side condition of `reach_block` (`by decide +kernel`). -/
noncomputable def blockOK (path : List (Fin 3375)) (cost : Nat) : Bool :=
  path.all (fun i => EvmProof.Meter.CopyFree (instrAt i.val)) && blockCost path == cost

/-- `#eval`-able twin of `blockCost`, for finding the literal to state. -/
def blockCostEval (path : List Nat) : Nat :=
  (path.map fun i => EvmProof.Meter.instrStaticCost .Osaka
    (referenceInstructions.getD i (.op .INVALID))).sum

theorem reach_block {s : State} (hs : Ctx s) (path : List (Fin 3375)) {cost : Nat}
    {pc pc' : Nat} {stk stk' : List UInt256} {m m' : ByteArray}
    (hok : blockOK path cost = true)
    (hrun : runLocatedBlock (locatedPath path) (callState s pc stk m) =
      some (callState s pc' stk' m')) :
    Reach (callState s pc stk m) (callState s pc' stk' m') cost := by
  simp only [blockOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨hfree, hcost⟩ := hok
  have hcode : (callState s pc stk m).executionEnv.code = referenceArtifact.code := hs.code
  have hfork : (callState s pc stk m).fork = .Osaka := hs.fork
  have hrunning : (callState s pc stk m).halt = .Running := hs.running
  have hnp := hs.notPrecompile
  let g := runLocatedBlock_sound referenceArtifact .Osaka (locatedPath path) hcode hfork hrun
    hrunning hnp
  refine ⟨g, le_of_eq ?_⟩
  have hpot := EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree (locatedPath path)
    (blockCost path) hrun hfork ?free ?static
  · change runLocatedBlockCost (locatedPath path) (callState s pc stk m) = cost
    change _ + MachineState.memCost s.activeWords.toNat =
      _ + MachineState.memCost s.activeWords.toNat at hpot
    omega
  case free =>
    intro l hl
    simp only [locatedPath, List.mem_map] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    rw [located_instruction_eq]
    exact hfree i hi
  case static =>
    unfold EvmProof.Meter.runLocatedBlockStaticCost blockCost locatedPath
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, located_instruction_eq]

end MlDsa44.Proofs.Infra

/-- Prove `Reach (callState s pc stk m) (callState s pc' stk' m') cost` for a
straight-line path: checks the static cost with the kernel, then runs
`evm_block`.  Needs `hs : Ctx s` in context.
Usage: `evm_reach [1556, 1557, …]` or `evm_reach [1556, …] with [extra lemmas]`. -/
syntax "evm_reach " term:max (" with " "[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evm_reach $path:term) => `(tactic| evm_reach $path with [])
  | `(tactic| evm_reach $path:term with [$extra:simpLemma,*]) => `(tactic| (
      refine MlDsa44.Proofs.Infra.reach_block (by assumption) $path
        (by first
          | decide +kernel
          | fail "evm_reach: the stated cost is not the path's static cost (or the path contains \
              CALLDATACOPY/MCOPY); get it with `#eval MlDsa44.Proofs.Infra.blockCostEval [indices]`") ?_
      evm_block [$extra,*]))
