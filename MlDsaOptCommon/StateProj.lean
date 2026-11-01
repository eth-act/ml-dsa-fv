import EvmProof
import MlDsaOptCommon.StateProjAttr
set_option warningAsError true
/-!
# Field projections of state literals, reduced with proofs

Each instruction step builds the next state as a literal
`{ gasAvailable := …, memory := …, … }` (`State.mk (SharedState.mk
(MachineState.mk …) …) …`) and reads fields of it. Simp's built-in
projection reduction rewrites `{ … }.toSharedState.toMachineState.activeWords`
to `s.activeWords` without a proof, and the kernel has to recheck that step:
it first tries to unify the literal `{ … }` with `s` field by field, which
fails, and on the way it evaluates every concrete `natToBytesPadded v 32` in
the memory writes (`MachineState.writeBytes` tests `bytes.size = 0`). In
`tbl_b0` (93 instructions, 31 literal stores) that took 5.0 s of kernel time.

The `state_proj` lemmas below are `↓` (pre) rewrites for every projection
chain over these three structures whose innermost argument is a constructor
application, so they fire before the built-in reduction (which still handles
every other structure) and every step carries a proof whose type matches the
goal syntactically (`tbl_b0`: 1.1 s). Their proofs are deliberately not `rfl`,
so simp does not use them as definitional unfoldings. They are lemmas rather
than a simproc so that no interpreted code runs on each visit.
-/

namespace MlDsaOptCommon.StateProj

open EvmSemantics EvmSemantics.EVM

variable (sh : SharedState) (pc : UInt256) (st : List UInt256) (el : Nat) (h : HaltKind)
  (cs : List Frame) (m : MachineState) (am : AccountMap) (sub : Substate) (env : ExecutionEnv)
  (g : Nat) (aw : UInt256) (mem rd hr : ByteArray)

@[state_proj ↓] theorem toSharedState_mk :
    (State.mk sh pc st el h cs).toSharedState = sh := Eq.trans rfl rfl

@[state_proj ↓] theorem pc_mk :
    (State.mk sh pc st el h cs).pc = pc := Eq.trans rfl rfl

@[state_proj ↓] theorem stack_mk :
    (State.mk sh pc st el h cs).stack = st := Eq.trans rfl rfl

@[state_proj ↓] theorem execLength_mk :
    (State.mk sh pc st el h cs).execLength = el := Eq.trans rfl rfl

@[state_proj ↓] theorem halt_mk :
    (State.mk sh pc st el h cs).halt = h := Eq.trans rfl rfl

@[state_proj ↓] theorem callStack_mk :
    (State.mk sh pc st el h cs).callStack = cs := Eq.trans rfl rfl

@[state_proj ↓] theorem toMachineState_mk :
    (SharedState.mk m am sub env).toMachineState = m := Eq.trans rfl rfl

@[state_proj ↓] theorem accountMap_mk :
    (SharedState.mk m am sub env).accountMap = am := Eq.trans rfl rfl

@[state_proj ↓] theorem accountMap_mk_state :
    (State.mk sh pc st el h cs).toSharedState.accountMap = sh.accountMap := Eq.trans rfl rfl

@[state_proj ↓] theorem substate_mk :
    (SharedState.mk m am sub env).substate = sub := Eq.trans rfl rfl

@[state_proj ↓] theorem substate_mk_state :
    (State.mk sh pc st el h cs).toSharedState.substate = sh.substate := Eq.trans rfl rfl

@[state_proj ↓] theorem executionEnv_mk :
    (SharedState.mk m am sub env).executionEnv = env := Eq.trans rfl rfl

@[state_proj ↓] theorem executionEnv_mk_state :
    (State.mk sh pc st el h cs).toSharedState.executionEnv = sh.executionEnv := Eq.trans rfl rfl

@[state_proj ↓] theorem gasAvailable_mk :
    (MachineState.mk g aw mem rd hr).gasAvailable = g := Eq.trans rfl rfl

@[state_proj ↓] theorem gasAvailable_mk_shared :
    (SharedState.mk m am sub env).toMachineState.gasAvailable = m.gasAvailable := Eq.trans rfl rfl

@[state_proj ↓] theorem gasAvailable_mk_state :
    (State.mk sh pc st el h cs).toSharedState.toMachineState.gasAvailable = sh.toMachineState.gasAvailable := Eq.trans rfl rfl

@[state_proj ↓] theorem activeWords_mk :
    (MachineState.mk g aw mem rd hr).activeWords = aw := Eq.trans rfl rfl

@[state_proj ↓] theorem activeWords_mk_shared :
    (SharedState.mk m am sub env).toMachineState.activeWords = m.activeWords := Eq.trans rfl rfl

@[state_proj ↓] theorem activeWords_mk_state :
    (State.mk sh pc st el h cs).toSharedState.toMachineState.activeWords = sh.toMachineState.activeWords := Eq.trans rfl rfl

@[state_proj ↓] theorem memory_mk :
    (MachineState.mk g aw mem rd hr).memory = mem := Eq.trans rfl rfl

@[state_proj ↓] theorem memory_mk_shared :
    (SharedState.mk m am sub env).toMachineState.memory = m.memory := Eq.trans rfl rfl

@[state_proj ↓] theorem memory_mk_state :
    (State.mk sh pc st el h cs).toSharedState.toMachineState.memory = sh.toMachineState.memory := Eq.trans rfl rfl

@[state_proj ↓] theorem returnData_mk :
    (MachineState.mk g aw mem rd hr).returnData = rd := Eq.trans rfl rfl

@[state_proj ↓] theorem returnData_mk_shared :
    (SharedState.mk m am sub env).toMachineState.returnData = m.returnData := Eq.trans rfl rfl

@[state_proj ↓] theorem returnData_mk_state :
    (State.mk sh pc st el h cs).toSharedState.toMachineState.returnData = sh.toMachineState.returnData := Eq.trans rfl rfl

@[state_proj ↓] theorem hReturn_mk :
    (MachineState.mk g aw mem rd hr).hReturn = hr := Eq.trans rfl rfl

@[state_proj ↓] theorem hReturn_mk_shared :
    (SharedState.mk m am sub env).toMachineState.hReturn = m.hReturn := Eq.trans rfl rfl

@[state_proj ↓] theorem hReturn_mk_state :
    (State.mk sh pc st el h cs).toSharedState.toMachineState.hReturn = sh.toMachineState.hReturn := Eq.trans rfl rfl

@[state_proj ↓] theorem toMachineState_mk_state :
    (State.mk sh pc st el h cs).toSharedState.toMachineState = sh.toMachineState := Eq.trans rfl rfl

end MlDsaOptCommon.StateProj
