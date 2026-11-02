import EvmProof.Meter
import EvmProof.StepperX
set_option warningAsError true
/-!
# Gas metering of `XLocated` paths

`Meter`'s potential argument for `runXLocatedBlock`: memory expansion
telescopes, and on a copy-free path the cost is the static opcode sum plus
the growth of the memory potential. `XInstr.base` reuses `Meter`; the EIP-8024
instructions cost 3 and leave memory alone.
-/

namespace EvmProof.Meter

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open YulEvmCompiler

def xinstrCostWithoutMemory : XInstr → State → Nat
  | .base i, s => instrCostWithoutMemory i s
  | i, s => xinstrCost i s

theorem runXInstr_cost_potential {instruction : XInstr} {s t : State}
    (hresult : runXInstr instruction s = some t) :
    xinstrCost instruction s + MachineState.memCost s.activeWords.toNat =
      xinstrCostWithoutMemory instruction s + MachineState.memCost t.activeWords.toNat := by
  cases instruction with
  | base i => exact runInstr_cost_potential hresult
  | _ =>
    simp only [runXInstr] at hresult
    repeat' first | split at hresult | simp_all
    all_goals subst t; rfl

theorem runXLocated_cost_potential {artifact : XArtifact} {fork : Fork}
    {located : XLocated artifact fork} {s t : State}
    (hresult : runXLocated located s = some t) :
    xinstrCost located.instruction s + MachineState.memCost s.activeWords.toNat =
      xinstrCostWithoutMemory located.instruction s +
        MachineState.memCost t.activeWords.toNat := by
  unfold runXLocated at hresult
  split at hresult
  · exact runXInstr_cost_potential hresult
  · simp_all

def runXLocatedBlockCostWithoutMemory {artifact : XArtifact} {fork : Fork} :
    List (XLocated artifact fork) → State → Nat
  | [], _ => 0
  | located :: rest, s =>
      xinstrCostWithoutMemory located.instruction s +
        match rest with
        | [] => 0
        | _ :: _ =>
            match runXLocated located s with
            | some next =>
                match next.halt with
                | .Running => runXLocatedBlockCostWithoutMemory rest next
                | _ => 0
            | none => 0

def xinstrStaticCost (fork : Fork) : XInstr → Nat
  | .base i => instrStaticCost fork i
  | _ => 3

def XCopyFree : XInstr → Bool
  | .base i => CopyFree i
  | _ => true

theorem xinstrCostWithoutMemory_eq_static_of_copyFree
    (instruction : XInstr) (s : State) (fork : Fork)
    (hfork : s.fork = fork) (hfree : XCopyFree instruction) :
    xinstrCostWithoutMemory instruction s = xinstrStaticCost fork instruction := by
  cases instruction with
  | base i => exact instrCostWithoutMemory_eq_static_of_copyFree i s fork hfork hfree
  | _ => rfl

def runXLocatedBlockStaticCost {artifact : XArtifact} {fork : Fork}
    (path : List (XLocated artifact fork)) : Nat :=
  (path.map (fun located => xinstrStaticCost fork located.instruction)).sum

theorem runXLocatedBlockCostWithoutMemory_eq_static {artifact : XArtifact} {fork : Fork}
    (path : List (XLocated artifact fork)) {s t : State}
    (hresult : runXLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hstatic : ∀ located, located ∈ path → ∀ q, q.fork = fork →
      xinstrCostWithoutMemory located.instruction q =
        xinstrStaticCost fork located.instruction) :
    runXLocatedBlockCostWithoutMemory path s = runXLocatedBlockStaticCost path := by
  induction path generalizing s t with
  | nil => simp [runXLocatedBlockCostWithoutMemory, runXLocatedBlockStaticCost]
  | cons located rest ih =>
      cases rest with
      | nil =>
          simp [runXLocatedBlockCostWithoutMemory, runXLocatedBlockStaticCost,
            hstatic located (by simp) s hfork]
      | cons nextLocated tail =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hresult
          | some next =>
              cases hrun : next.halt with
              | Running =>
                  simp [runXLocatedBlock, hnext, hrun] at hresult
                  have hnextFork : next.fork = fork := by
                    have henv := runXLocated_executionEnv hnext
                    simpa [State.fork, henv] using hfork
                  have htail := ih hresult hnextFork
                    (fun member hmem q hq => hstatic member (by simp [hmem]) q hq)
                  have hwork : runXLocatedBlockCostWithoutMemory
                      (located :: nextLocated :: tail) s =
                        xinstrCostWithoutMemory located.instruction s +
                          runXLocatedBlockCostWithoutMemory (nextLocated :: tail) next := by
                    simp [runXLocatedBlockCostWithoutMemory, hnext, hrun]
                  have hsum : runXLocatedBlockStaticCost (located :: nextLocated :: tail) =
                      xinstrStaticCost fork located.instruction +
                        runXLocatedBlockStaticCost (nextLocated :: tail) := by
                    simp [runXLocatedBlockStaticCost]
                  rw [hwork, hsum, htail, hstatic located (by simp) s hfork]
              | Success => simp [runXLocatedBlock, hnext, hrun] at hresult
              | Returned => simp [runXLocatedBlock, hnext, hrun] at hresult
              | Reverted => simp [runXLocatedBlock, hnext, hrun] at hresult
              | Exception error => simp [runXLocatedBlock, hnext, hrun] at hresult

theorem runXLocatedBlock_cost_potential {artifact : XArtifact} {fork : Fork}
    (path : List (XLocated artifact fork)) {s t : State}
    (hresult : runXLocatedBlock path s = some t) :
    runXLocatedBlockCost path s + MachineState.memCost s.activeWords.toNat =
      runXLocatedBlockCostWithoutMemory path s + MachineState.memCost t.activeWords.toNat := by
  induction path generalizing s t with
  | nil =>
      simp [runXLocatedBlock] at hresult
      subst t
      simp [runXLocatedBlockCost, runXLocatedBlockCostWithoutMemory]
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hresult
          | some next =>
              simp [runXLocatedBlock, hnext] at hresult
              subst t
              simpa [runXLocatedBlockCost, runXLocatedBlockCostWithoutMemory] using
                runXLocated_cost_potential hnext
      | cons nextLocated tail =>
          cases hnext : runXLocated located s with
          | none => simp [runXLocatedBlock, hnext] at hresult
          | some next =>
              cases hrun : next.halt with
              | Running =>
                  simp [runXLocatedBlock, hnext, hrun] at hresult
                  have hhead := runXLocated_cost_potential hnext
                  have htail := ih hresult
                  have hcost : runXLocatedBlockCost (located :: nextLocated :: tail) s =
                      xinstrCost located.instruction s +
                        runXLocatedBlockCost (nextLocated :: tail) next := by
                    simp [runXLocatedBlockCost, hnext, hrun]
                  have hwork : runXLocatedBlockCostWithoutMemory
                      (located :: nextLocated :: tail) s =
                        xinstrCostWithoutMemory located.instruction s +
                          runXLocatedBlockCostWithoutMemory (nextLocated :: tail) next := by
                    simp [runXLocatedBlockCostWithoutMemory, hnext, hrun]
                  rw [hcost, hwork]
                  omega
              | Success => simp [runXLocatedBlock, hnext, hrun] at hresult
              | Returned => simp [runXLocatedBlock, hnext, hrun] at hresult
              | Reverted => simp [runXLocatedBlock, hnext, hrun] at hresult
              | Exception error => simp [runXLocatedBlock, hnext, hrun] at hresult

/-- Copy-free paths charge their static opcode sum plus the change in memory
potential. -/
theorem runXLocatedBlock_cost_potential_of_copyFree {artifact : XArtifact} {fork : Fork}
    (path : List (XLocated artifact fork)) {s t : State} (work : Nat)
    (hresult : runXLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, XCopyFree located.instruction)
    (hcost : runXLocatedBlockStaticCost path = work) :
    runXLocatedBlockCost path s + MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [← hcost, runXLocatedBlock_cost_potential path hresult,
    runXLocatedBlockCostWithoutMemory_eq_static path hresult hfork]
  intro located hmem q hq
  exact xinstrCostWithoutMemory_eq_static_of_copyFree
    located.instruction q fork hq (hfree located hmem)

end EvmProof.Meter
