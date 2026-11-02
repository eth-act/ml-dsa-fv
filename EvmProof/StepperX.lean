import EvmProof.Stepper
import EvmProof.XInstr
set_option warningAsError true
/-!
# The symbolic stepper with EIP-8024 instructions

`runXInstr` is `Stepper.runInstr` on `XInstr`: it delegates `XInstr.base` to
`runInstr` and adds `DUPN`, `SWAPN` and `EXCHANGE` (pc += 2, 3 gas, the stack
positions of the patched semantics: `DupNOp.n`, `SwapNOp.n + 1`,
`ExchangeOp.n + 1` / `m + 1`, i.e. EIP-8024's `decode_single` /
`decode_pair`). `runXInstr_sound` proves each successful step against the
relational semantics, through the `GasStep` rules below.

The artifact layer mirrors `Stepper`'s (`XWellFormed`, `XLocated`,
`runXLocatedBlock`, `runXLocatedBlock_sound`). The EIP-8024 instructions are
behind the fork: `XWellFormed fork (.dupN x)` asks
`(Operation.DupN ⟨x⟩).availableInFork fork`, which holds only from
`Amsterdam` and only for a valid immediate. Nothing in `Stepper`,
`ProgramArtifact` or the proofs built on them changes.
-/

namespace EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

namespace GasStep

def dupN {s : State} (x : Fin 256) (value : UInt256)
    (hop : s.decodedOp = some (.DupN ⟨x⟩))
    (hget : s.stack[(⟨x⟩ : Operation.DupNOp).n.val]? = some value)
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := value :: s.stack, pc := s.pc + UInt256.ofNat 2 } := by
  let op : Operation := .DupN ⟨x⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.dupN (withGas s gas) x value hop hgas hget hcap

def swapN {s : State} (x : Fin 256) (stack' : List UInt256)
    (hop : s.decodedOp = some (.SwapN ⟨x⟩))
    (hswap : s.stack.exchange 0 ((⟨x⟩ : Operation.SwapNOp).n.val + 1) = some stack')
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := stack', pc := s.pc + UInt256.ofNat 2 } := by
  let op : Operation := .SwapN ⟨x⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.swapN (withGas s gas) x stack' hop hgas hswap
      (by simp only [withGas, Operation.pushArity, Operation.popArity]; omega)

def exchange {s : State} (x : Fin 256) (stack' : List UInt256)
    (hop : s.decodedOp = some (.Exchange ⟨x⟩))
    (hswap : s.stack.exchange ((⟨x⟩ : Operation.ExchangeOp).n + 1)
      ((⟨x⟩ : Operation.ExchangeOp).m + 1) = some stack')
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := stack', pc := s.pc + UInt256.ofNat 2 } := by
  let op : Operation := .Exchange ⟨x⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.exchange (withGas s gas) x stack' hop hgas hswap
      (by simp only [withGas, Operation.pushArity, Operation.popArity]; omega)

end GasStep

namespace Stepper

/-- The decoder fact for an `XInstr` at the current pc. -/
def XDecodes (s : State) : XInstr → Prop
  | .base i => Decodes s i
  | .dupN x => s.decodedOp = some (.DupN ⟨x⟩)
  | .swapN x => s.decodedOp = some (.SwapN ⟨x⟩)
  | .exchange x => s.decodedOp = some (.Exchange ⟨x⟩)

/-- `runInstr` extended with the EIP-8024 instructions. -/
def runXInstr : XInstr → State → Option State
  | .base i, s => runInstr i s
  | .dupN x, s =>
      if s.stack.length < 1024 then
        match s.stack[(⟨x⟩ : Operation.DupNOp).n.val]? with
        | some value => some { s with stack := value :: s.stack, pc := s.pc + UInt256.ofNat 2 }
        | none => none
      else none
  | .swapN x, s =>
      if s.stack.length < 1024 then
        match s.stack.exchange 0 ((⟨x⟩ : Operation.SwapNOp).n.val + 1) with
        | some stack => some { s with stack := stack, pc := s.pc + UInt256.ofNat 2 }
        | none => none
      else none
  | .exchange x, s =>
      if s.stack.length < 1024 then
        match s.stack.exchange ((⟨x⟩ : Operation.ExchangeOp).n + 1)
            ((⟨x⟩ : Operation.ExchangeOp).m + 1) with
        | some stack => some { s with stack := stack, pc := s.pc + UInt256.ofNat 2 }
        | none => none
      else none

/-- Exact gas charged by a successful `runXInstr` step. -/
def xinstrCost : XInstr → State → Nat
  | .base i, s => instrCost i s
  | .dupN x, s => Gas.baseCost s.fork (.DupN ⟨x⟩)
  | .swapN x, s => Gas.baseCost s.fork (.SwapN ⟨x⟩)
  | .exchange x, s => Gas.baseCost s.fork (.Exchange ⟨x⟩)

/-- Every EIP-8024 instruction costs 3 gas, on every fork. -/
@[simp] theorem xinstrCost_dupN (x : Fin 256) (s : State) :
    xinstrCost (.dupN x) s = 3 := rfl
@[simp] theorem xinstrCost_swapN (x : Fin 256) (s : State) :
    xinstrCost (.swapN x) s = 3 := rfl
@[simp] theorem xinstrCost_exchange (x : Fin 256) (s : State) :
    xinstrCost (.exchange x) s = 3 := rfl

/-- Every successful `runXInstr` step is a gas-parametric trace in the
relational EVM semantics. -/
def runXInstr_sound {instruction : XInstr} {s t : State}
    (hdecode : XDecodes s instruction)
    (hresult : runXInstr instruction s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨xinstrCost instruction s, ?_⟩
  intro gas hgas
  cases instruction with
  | base i => exact (runInstr_sound hdecode hresult hrun hnp).trace gas hgas
  | dupN x =>
    simp only [runXInstr] at hresult
    split at hresult
    · rename_i hcap
      split at hresult
      · rename_i value hget
        injection hresult with hresult
        subst t
        exact (GasStep.dupN x value hdecode hget hcap hrun hnp).trace gas hgas
      · simp at hresult
    · simp at hresult
  | swapN x =>
    simp only [runXInstr] at hresult
    split at hresult
    · rename_i hcap
      split at hresult
      · rename_i stack hswap
        injection hresult with hresult
        subst t
        exact (GasStep.swapN x stack hdecode hswap hcap hrun hnp).trace gas hgas
      · simp at hresult
    · simp at hresult
  | exchange x =>
    simp only [runXInstr] at hresult
    split at hresult
    · rename_i hcap
      split at hresult
      · rename_i stack hswap
        injection hresult with hresult
        subst t
        exact (GasStep.exchange x stack hdecode hswap hcap hrun hnp).trace gas hgas
      · simp at hresult
    · simp at hresult

@[simp] theorem runXInstr_sound_cost {instruction : XInstr} {s t : State}
    (hdecode : XDecodes s instruction)
    (hresult : runXInstr instruction s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (runXInstr_sound hdecode hresult hrun hnp).cost = xinstrCost instruction s :=
  rfl

theorem runXInstr_executionEnv {instruction : XInstr} {s t : State}
    (hresult : runXInstr instruction s = some t) :
    t.executionEnv = s.executionEnv := by
  cases instruction with
  | base i => exact runInstr_executionEnv hresult
  | _ =>
    simp only [runXInstr] at hresult
    repeat' first | split at hresult | simp_all
    all_goals subst t; rfl

/-! ## Artifacts -/

/-- Structural and fork-specific conditions under which an `XInstr` decodes as
its instruction-boundary view claims. For the EIP-8024 instructions that is
opcode availability: from `Amsterdam`, with a valid immediate. -/
def XWellFormed (fork : Fork) : XInstr → Prop
  | .base i => WellFormed fork i
  | .dupN x => (Operation.DupN ⟨x⟩).availableInFork fork = true
  | .swapN x => (Operation.SwapN ⟨x⟩).availableInFork fork = true
  | .exchange x => (Operation.Exchange ⟨x⟩).availableInFork fork = true

instance (fork : Fork) (instruction : XInstr) :
    Decidable (XWellFormed fork instruction) := by
  cases instruction <;> simp only [XWellFormed] <;> infer_instance

/-- Available EIP-8024 instructions have valid immediates. -/
theorem XWellFormed.immOK {fork : Fork} {i : XInstr} (h : XWellFormed fork i) : i.ImmOK := by
  cases i with
  | base _ => trivial
  | _ =>
    simp only [XWellFormed, Operation.availableInFork, Bool.and_eq_true] at h
    exact h.2

theorem xdecodes_of_artifact (artifact : XArtifact) (s : State)
    (index : Nat) (instruction : XInstr)
    (hcode : s.executionEnv.code = artifact.code)
    (hpc : s.pc.toNat = artifact.instructionPC index)
    (hget : artifact.instructions[index]? = some instruction)
    (hwf : XWellFormed s.fork instruction) : XDecodes s instruction := by
  have hdec : ∀ op imm, Decode.decodeAt artifact.code (artifact.instructionPC index) =
      some (op, imm) → op.availableInFork s.fork = true → s.decoded = some (op, imm) := by
    intro op imm h ha
    unfold State.decoded
    rw [hcode, hpc, h]
    simp [ha]
  cases instruction with
  | base i =>
    cases i with
    | push width value =>
      rcases hwf with ⟨hfit, havailable⟩
      exact hdec _ _ (artifact.decodeAt_base_push index width value hget hfit) havailable
    | op op =>
      rcases hwf with ⟨hopcode, hplain, havailable⟩
      show s.decodedOp = some op
      simp [State.decodedOp,
        hdec _ _ (artifact.decodeAt_base_op index op hget hopcode hplain) havailable]
  | dupN x =>
    show s.decodedOp = some _
    simp [State.decodedOp, hdec _ _ (artifact.decodeAt_dupN index x hget) hwf]
  | swapN x =>
    show s.decodedOp = some _
    simp [State.decodedOp, hdec _ _ (artifact.decodeAt_swapN index x hget) hwf]
  | exchange x =>
    show s.decodedOp = some _
    simp [State.decodedOp, hdec _ _ (artifact.decodeAt_exchange index x hget) hwf]

/-- A proof-carrying instruction location in an `XArtifact`. -/
structure XLocated (artifact : XArtifact) (fork : Fork) where
  index : Nat
  instruction : XInstr
  atIndex : artifact.instructions[index]? = some instruction
  wellFormed : XWellFormed fork instruction

/-- One Boolean certificate for opcode availability and encoding of every
instruction of an artifact. -/
def XAllWellFormed (artifact : XArtifact) (fork : Fork) : Prop :=
  artifact.instructions.all (fun instruction =>
    decide (XWellFormed fork instruction)) = true

theorem XAllWellFormed.valid {artifact : XArtifact} {fork : Fork}
    (hcert : XAllWellFormed artifact fork) {instruction : XInstr}
    (hmem : instruction ∈ artifact.instructions) :
    XWellFormed fork instruction :=
  of_decide_eq_true ((List.all_eq_true.mp hcert) instruction hmem)

/-- With the whole-artifact certificate, every `JUMPDEST` instruction is a
valid jump destination. -/
theorem XAllWellFormed.isValidJumpDest {artifact : XArtifact} {fork : Fork}
    (hcert : XAllWellFormed artifact fork) {index : Nat}
    (hget : artifact.instructions[index]? = some (.base (.op .JUMPDEST))) :
    Decode.isValidJumpDest artifact.code (artifact.instructionPC index) = true :=
  artifact.isValidJumpDest_index index hget fun _ hi =>
    (hcert.valid (List.mem_of_mem_take hi)).immOK

/-- A kernel-reducible Boolean form of `XWellFormed`, so a whole-artifact
certificate is one `rfl` / `decide`. -/
def xwellFormedB (fork : Fork) : XInstr → Bool
  | .base (.push width value) =>
      decide (value.toNat < 256 ^ width.val) &&
        (Operation.Push ⟨width⟩).availableInFork fork
  | .base (.op op) =>
      decide (Decode.opcodeOf (Instr.opByte op) = some op) &&
        (match op with
         | .Push _ | .DupN _ | .SwapN _ | .Exchange _ => false
         | _ => true) &&
        op.availableInFork fork
  | .dupN x => (Operation.DupN ⟨x⟩).availableInFork fork
  | .swapN x => (Operation.SwapN ⟨x⟩).availableInFork fork
  | .exchange x => (Operation.Exchange ⟨x⟩).availableInFork fork

theorem xwellFormed_of_xwellFormedB {fork : Fork} {i : XInstr}
    (h : xwellFormedB fork i = true) : XWellFormed fork i := by
  cases i with
  | base i =>
    cases i with
    | push width value =>
      simp only [xwellFormedB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h
    | op op =>
      simp only [xwellFormedB, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨h.1.1, ?_, h.2⟩
      have hp := h.1.2
      cases op <;> simp_all [plainOp]
  | _ => exact h

theorem xallWellFormed_of_all {artifact : XArtifact} {fork : Fork}
    (h : artifact.instructions.all (xwellFormedB fork) = true) :
    XAllWellFormed artifact fork := by
  unfold XAllWellFormed
  rw [List.all_eq_true] at h ⊢
  intro i hi
  exact decide_eq_true (xwellFormed_of_xwellFormedB (h i hi))

def XLocated.ofIndex {artifact : XArtifact} {fork : Fork}
    (hcert : XAllWellFormed artifact fork)
    (index : Fin artifact.instructions.length) : XLocated artifact fork where
  index := index.val
  instruction := artifact.instructions[index.val]
  atIndex := List.getElem?_eq_getElem index.isLt
  wellFormed := hcert.valid (List.getElem_mem index.isLt)

def runXLocated {artifact : XArtifact} {fork : Fork}
    (located : XLocated artifact fork) (s : State) : Option State :=
  if s.pc.toNat = artifact.instructionPC located.index then
    runXInstr located.instruction s
  else none

def runXLocated_sound {artifact : XArtifact}
    {fork : Fork} {located : XLocated artifact fork} {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runXLocated located s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨xinstrCost located.instruction s, ?_⟩
  intro gas hgas
  unfold runXLocated at hresult
  split at hresult
  · rename_i hpc
    have hwf : XWellFormed s.fork located.instruction := by
      simpa [hfork] using located.wellFormed
    exact (runXInstr_sound
      (xdecodes_of_artifact artifact s located.index located.instruction
        hcode hpc located.atIndex hwf) hresult hrun hnp).trace gas hgas
  · simp_all

@[simp] theorem runXLocated_sound_cost {artifact : XArtifact}
    {fork : Fork} {located : XLocated artifact fork} {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runXLocated located s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (runXLocated_sound hcode hfork hresult hrun hnp).cost =
      xinstrCost located.instruction s := rfl

theorem runXLocated_executionEnv {artifact : XArtifact}
    {fork : Fork} {located : XLocated artifact fork} {s t : State}
    (hresult : runXLocated located s = some t) :
    t.executionEnv = s.executionEnv := by
  unfold runXLocated at hresult
  split at hresult
  · exact runXInstr_executionEnv hresult
  · simp_all

def runXLocatedBlock {artifact : XArtifact} {fork : Fork} :
    List (XLocated artifact fork) → State → Option State
  | [], s => some s
  | located :: rest, s =>
      match runXLocated located s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runXLocatedBlock rest next
              | _ => none

theorem runXLocatedBlock_append {artifact : XArtifact} {fork : Fork}
    (left right : List (XLocated artifact fork)) (s t u : State)
    (hleft : runXLocatedBlock left s = some t)
    (hrunning : t.halt = .Running)
    (hright : runXLocatedBlock right t = some u) :
    runXLocatedBlock (left ++ right) s = some u := by
  induction left generalizing s with
  | nil =>
      simp [runXLocatedBlock] at hleft
      subst t
      exact hright
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hleft
          | some next =>
              simp [runXLocatedBlock, hnext] at hleft
              subst next
              cases right with
              | nil => simpa [runXLocatedBlock, hnext] using hright
              | cons nextLocated tail =>
                  simpa [runXLocatedBlock, hnext, hrunning] using hright
      | cons nextLocated tail =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hleft
          | some next =>
              cases hhalt : next.halt with
              | Running =>
                  have hrest : runXLocatedBlock (nextLocated :: tail) next = some t := by
                    simpa [runXLocatedBlock, hnext, hhalt] using hleft
                  have happ := ih next hrest
                  simpa [runXLocatedBlock, hnext, hhalt] using happ
              | Success => simp [runXLocatedBlock, hnext, hhalt] at hleft
              | Returned => simp [runXLocatedBlock, hnext, hhalt] at hleft
              | Reverted => simp [runXLocatedBlock, hnext, hhalt] at hleft
              | Exception error => simp [runXLocatedBlock, hnext, hhalt] at hleft

/-- Executable exact cost of a located path (as `runLocatedBlockCost`). -/
def runXLocatedBlockCost {artifact : XArtifact} {fork : Fork} :
    List (XLocated artifact fork) → State → Nat
  | [], _ => 0
  | located :: rest, s =>
      xinstrCost located.instruction s +
        match rest with
        | [] => 0
        | _ :: _ =>
            match runXLocated located s with
            | some next =>
                match next.halt with
                | .Running => runXLocatedBlockCost rest next
                | _ => 0
            | none => 0

def runXLocatedBlock_sound (artifact : XArtifact)
    (fork : Fork) (path : List (XLocated artifact fork)) {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runXLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨runXLocatedBlockCost path s, ?_⟩
  intro gas hgas
  induction path generalizing s t gas with
  | nil =>
      simp [runXLocatedBlock] at hresult
      subst t
      simpa [runXLocatedBlockCost, withGas] using
        Steps.refl (withGas s gas)
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hresult
          | some next =>
            simp [runXLocatedBlock, hnext] at hresult
            subst t
            exact (runXLocated_sound hcode hfork hnext hrun hnp).trace gas
              (by simpa [runXLocatedBlockCost] using hgas)
      | cons nextLocated tail =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hresult
          | some next =>
            cases hnextRun : next.halt with
            | Running =>
              simp [runXLocatedBlock, hnext, hnextRun] at hresult
              have henv := runXLocated_executionEnv hnext
              have hnextCode : next.executionEnv.code = artifact.code := by
                rw [henv, hcode]
              have hnextNp : Precompile.isPrecompileWithConfig
                  next.executionEnv.precompileConfig next.executionEnv.fork
                  next.executionEnv.codeAddr = false := by
                simpa [henv] using hnp
              have hnextFork : next.fork = fork := by
                change next.executionEnv.fork = fork
                rw [henv]
                exact hfork
              let head := runXLocated_sound hcode hfork hnext hrun hnp
              have hcost :
                  runXLocatedBlockCost (located :: nextLocated :: tail) s =
                    head.cost +
                      runXLocatedBlockCost (nextLocated :: tail) next := by
                simp [runXLocatedBlockCost, hnext, hnextRun, head]
              have hhead : head.cost ≤ gas := by
                rw [hcost] at hgas
                omega
              have htail : runXLocatedBlockCost (nextLocated :: tail) next ≤
                  gas - head.cost := by
                rw [hcost] at hgas
                omega
              have hsHead := head.trace gas hhead
              have hsTail := ih hnextCode hnextFork hresult hnextRun hnextNp
                (gas := gas - head.cost) htail
              have hsub :
                  gas - head.cost -
                      runXLocatedBlockCost (nextLocated :: tail) next =
                    gas - runXLocatedBlockCost
                      (located :: nextLocated :: tail) s := by
                rw [hcost]
                omega
              simpa [hsub] using hsHead.append hsTail
            | Success => simp [runXLocatedBlock, hnext, hnextRun] at hresult
            | Returned => simp [runXLocatedBlock, hnext, hnextRun] at hresult
            | Reverted => simp [runXLocatedBlock, hnext, hnextRun] at hresult
            | Exception error =>
              simp [runXLocatedBlock, hnext, hnextRun] at hresult

@[simp] theorem runXLocatedBlock_sound_cost (artifact : XArtifact)
    (fork : Fork) (path : List (XLocated artifact fork)) {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runXLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (runXLocatedBlock_sound artifact fork path hcode hfork hresult hrun hnp).cost =
      runXLocatedBlockCost path s := rfl

end Stepper
end EvmProof
