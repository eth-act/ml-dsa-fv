import EvmProof
set_option warningAsError true
/-!
# Field projections of state literals, reduced with proofs

Each instruction step builds the next state as a literal
`{ gasAvailable := …, memory := …, … }` (`State.mk (SharedState.mk
(MachineState.mk …) …) …`) and reads fields of it. Simp's built-in
projection reduction rewrites `{ … }.activeWords` to `s.activeWords` without
a proof, and the kernel has to recheck that step: it first tries to unify the
literal `{ … }` with `s` field by field, which fails, and on the way it
evaluates every concrete `natToBytesPadded v 32` in the memory writes
(`MachineState.writeBytes` tests `bytes.size = 0`). In `tbl_b0` (93
instructions, 31 literal stores) that took 5.0 s of kernel time.

The `↓` simprocs below reduce a projection chain over these three structures
innermost-first with the `*_mk` lemmas, so every step carries a proof whose
type matches the goal syntactically (`tbl_b0`: 1.1 s). They run before the
built-in reduction, which still handles every other structure. The lemma
proofs are deliberately not `rfl`, so they are not used as definitional
unfoldings.
-/

namespace MlDsaOptCommon.StateProj

open EvmSemantics EvmSemantics.EVM

variable (sh : SharedState) (pc : UInt256) (st : List UInt256) (el : Nat) (h : HaltKind)
  (cs : List Frame) (m : MachineState) (am : AccountMap) (sub : Substate) (env : ExecutionEnv)
  (g : Nat) (aw : UInt256) (mem rd hr : ByteArray)

theorem toSharedState_mk : (State.mk sh pc st el h cs).toSharedState = sh := Eq.trans rfl rfl
theorem pc_mk : (State.mk sh pc st el h cs).pc = pc := Eq.trans rfl rfl
theorem stack_mk : (State.mk sh pc st el h cs).stack = st := Eq.trans rfl rfl
theorem execLength_mk : (State.mk sh pc st el h cs).execLength = el := Eq.trans rfl rfl
theorem halt_mk : (State.mk sh pc st el h cs).halt = h := Eq.trans rfl rfl
theorem callStack_mk : (State.mk sh pc st el h cs).callStack = cs := Eq.trans rfl rfl
theorem toMachineState_mk : (SharedState.mk m am sub env).toMachineState = m := Eq.trans rfl rfl
theorem accountMap_mk : (SharedState.mk m am sub env).accountMap = am := Eq.trans rfl rfl
theorem substate_mk : (SharedState.mk m am sub env).substate = sub := Eq.trans rfl rfl
theorem executionEnv_mk : (SharedState.mk m am sub env).executionEnv = env := Eq.trans rfl rfl
theorem gasAvailable_mk : (MachineState.mk g aw mem rd hr).gasAvailable = g := Eq.trans rfl rfl
theorem activeWords_mk : (MachineState.mk g aw mem rd hr).activeWords = aw := Eq.trans rfl rfl
theorem memory_mk : (MachineState.mk g aw mem rd hr).memory = mem := Eq.trans rfl rfl
theorem returnData_mk : (MachineState.mk g aw mem rd hr).returnData = rd := Eq.trans rfl rfl
theorem hReturn_mk : (MachineState.mk g aw mem rd hr).hReturn = hr := Eq.trans rfl rfl

open Lean Meta Simp

/-- Projection function ↦ (constructor, number of fields, field index, `*_mk` lemma). -/
def projTable : List (Name × Name × Nat × Nat × Name) :=
  [(``EvmSemantics.EVM.State.toSharedState, ``EvmSemantics.EVM.State.mk, 6, 0, ``toSharedState_mk),
   (``EvmSemantics.EVM.State.pc, ``EvmSemantics.EVM.State.mk, 6, 1, ``pc_mk),
   (``EvmSemantics.EVM.State.stack, ``EvmSemantics.EVM.State.mk, 6, 2, ``stack_mk),
   (``EvmSemantics.EVM.State.execLength, ``EvmSemantics.EVM.State.mk, 6, 3, ``execLength_mk),
   (``EvmSemantics.EVM.State.halt, ``EvmSemantics.EVM.State.mk, 6, 4, ``halt_mk),
   (``EvmSemantics.EVM.State.callStack, ``EvmSemantics.EVM.State.mk, 6, 5, ``callStack_mk),
   (``EvmSemantics.SharedState.toMachineState, ``EvmSemantics.SharedState.mk, 4, 0, ``toMachineState_mk),
   (``EvmSemantics.SharedState.accountMap, ``EvmSemantics.SharedState.mk, 4, 1, ``accountMap_mk),
   (``EvmSemantics.SharedState.substate, ``EvmSemantics.SharedState.mk, 4, 2, ``substate_mk),
   (``EvmSemantics.SharedState.executionEnv, ``EvmSemantics.SharedState.mk, 4, 3, ``executionEnv_mk),
   (``EvmSemantics.MachineState.gasAvailable, ``EvmSemantics.MachineState.mk, 5, 0, ``gasAvailable_mk),
   (``EvmSemantics.MachineState.activeWords, ``EvmSemantics.MachineState.mk, 5, 1, ``activeWords_mk),
   (``EvmSemantics.MachineState.memory, ``EvmSemantics.MachineState.mk, 5, 2, ``memory_mk),
   (``EvmSemantics.MachineState.returnData, ``EvmSemantics.MachineState.mk, 5, 3, ``returnData_mk),
   (``EvmSemantics.MachineState.hReturn, ``EvmSemantics.MachineState.mk, 5, 4, ``hReturn_mk)]

/-- Reduce `p x` (a projection of the table) when `x` is, or reduces through
table projections to, a constructor application: returns the field and a
proof of `p x = field`. -/
partial def reduceChain (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const p _ := e.getAppFn | return none
  unless e.getAppNumArgs == 1 do return none
  let some (_, ctor, n, i, lem) := projTable.find? (·.1 == p) | return none
  let x := e.appArg!
  if x.isAppOfArity ctor n then
    return some (x.getArg! i, mkAppN (mkConst lem) x.getAppArgs)
  let some (x', hx) ← reduceChain x | return none
  let e₁ := mkApp e.appFn! x'
  let h₁ ← mkCongrArg e.appFn! hx
  match ← reduceChain e₁ with
  | some (e₂, h₂) => return some (e₂, ← mkEqTrans h₁ h₂)
  | none => return some (e₁, h₁)

/-- Shared body of the simprocs. -/
def projStep (e : Expr) : SimpM Step := do
  match ← reduceChain e with
  | some (e', h) => return .visit { expr := e', proof? := some h }
  | none => return .continue

simproc_decl toSharedState_proj (State.toSharedState _) := projStep
simproc_decl pc_proj (State.pc _) := projStep
simproc_decl stack_proj (State.stack _) := projStep
simproc_decl execLength_proj (State.execLength _) := projStep
simproc_decl halt_proj (State.halt _) := projStep
simproc_decl callStack_proj (State.callStack _) := projStep
simproc_decl toMachineState_proj (SharedState.toMachineState _) := projStep
simproc_decl accountMap_proj (SharedState.accountMap _) := projStep
simproc_decl substate_proj (SharedState.substate _) := projStep
simproc_decl executionEnv_proj (SharedState.executionEnv _) := projStep
simproc_decl gasAvailable_proj (MachineState.gasAvailable _) := projStep
simproc_decl activeWords_proj (MachineState.activeWords _) := projStep
simproc_decl memory_proj (MachineState.memory _) := projStep
simproc_decl returnData_proj (MachineState.returnData _) := projStep
simproc_decl hReturn_proj (MachineState.hReturn _) := projStep

end MlDsaOptCommon.StateProj
