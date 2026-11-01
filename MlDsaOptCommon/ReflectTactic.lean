import MlDsaOptCommon.Reflect
import Lean

namespace MlDsaOptCommon.Reflect
open Lean Meta Elab Tactic
open EvmSemantics EvmSemantics.EVM YulEvmCompiler

initialize registerTraceClass `opt.reflect

/-- Decode an instruction expression obtained from the artifact's checked tables.
The returned syntax is untrusted; the alignment proof checks it in the kernel. -/
def reflectInstr (e : Expr) (pc next : Nat) : MetaM Expr := do
  if e.isAppOfArity ``Instr.push 2 then
    let some _ ← getFinValue? (e.getArg! 0) | throwError "nonliteral PUSH width"
    let v ← whnf (← mkAppM ``UInt256.toNat #[e.getArg! 1])
    let some n ← getNatValue? v | throwError "nonliteral PUSH value"
    return mkApp2 (mkConst ``Op.push) (e.getArg! 0) (mkNatLit n)
  unless e.isAppOfArity ``Instr.op 1 do throwError "unsupported instruction"
  let o := e.getArg! 0
  if o.isAppOfArity ``Operation.Dup 1 then
    return mkApp (mkConst ``Op.dup) (← whnf (← mkAppM ``Operation.DupOp.idx #[o.getArg! 0]))
  if o.isAppOfArity ``Operation.Swap 1 then
    return mkApp (mkConst ``Op.swap) (← whnf (← mkAppM ``Operation.SwapOp.idx #[o.getArg! 0]))
  let name := o.getAppArgs.back!.getAppFn.constName!.getString!
  if name == "JUMP" then return mkApp (mkConst ``Op.jump) (mkNatLit next)
  if name == "JUMPI" then
    return mkApp2 (mkConst ``Op.jumpi) (mkNatLit next) (toExpr (next != pc + 1))
  let bin : List (String × Name) := [("ADD", ``Bin.add), ("MUL", ``Bin.mul),
    ("SUB", ``Bin.sub), ("LT", ``Bin.lt), ("GT", ``Bin.gt), ("EQ", ``Bin.eq),
    ("AND", ``Bin.land), ("OR", ``Bin.lor), ("XOR", ``Bin.xor),
    ("SHL", ``Bin.shl), ("SHR", ``Bin.shr)]
  if let some (_, b) := bin.find? (·.1 == name) then return mkApp (mkConst ``Op.bin) (mkConst b)
  if name == "ISZERO" then return mkApp (mkConst ``Op.un) (mkConst ``Un.iszero)
  if name == "NOT" then return mkApp (mkConst ``Op.un) (mkConst ``Un.not)
  for (s, n) in [("POP", ``Op.pop), ("MLOAD", ``Op.load), ("MSTORE", ``Op.store),
      ("JUMPDEST", ``Op.dest), ("CALLDATALOAD", ``Op.calldata)] do
    if s == name then return mkConst n
  throwError "reflection: unsupported opcode {name}"

/-- Reify a concrete prefix of the input stack. The arbitrary suffix is kept
opaque; unsupported shapes safely fail back to the existing block tactic. -/
def reifyStack (xs : Expr) : MetaM (Expr × Expr × Expr) := do
  let mut xs := xs
  let mut values : Array Expr := #[]
  for _ in [:1024] do
    if xs.isAppOfArity ``List.cons 3 then
      values := values.push (xs.getArg! 1)
      xs := xs.getArg! 2
    else
      let reduced ← withTransparency .reducible (whnf xs)
      if reduced == xs then break
      xs := reduced
  let vals ← mkListLit (mkConst ``UInt256) values.toList
  let rho ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let get ← mkAppM ``List.getD #[vals, i, ← mkAppM ``UInt256.ofNat #[mkNatLit 0]]
    mkLambdaFVars #[i] get
  let terms ← mkListLit (mkConst ``Term)
    ((List.range values.size).map fun i => mkApp (mkConst ``Term.var) (mkNatLit i))
  return (rho, terms, xs)

/-- Prove the computational core and expose only bounds, alignment, and output
denotation. `sound` is the artifact wrapper emitted by proofgen_artifact.py. -/
private def reflectBlockImpl (tables : MetaM (Array Expr × Array Nat)) (sound : Name)
    (finish : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := target.eq? | throwError "reflection: expected execution equality"
    unless lhs.isAppOfArity ``EvmProof.Stepper.runLocatedBlock 4 do
      throwError "reflection: expected runLocatedBlock"
    let pathApp := lhs.getArg! 2
    let path ← zetaReduce (← instantiateMVars (pathApp.getArg! 0))
    let some (_, indices) := path.listLit? | throwError "reflection: expected literal path {path}"
    let initial := lhs.getArg! 3
    unless initial.getAppNumArgs == 4 && initial.getAppFn.constName!.getString! == "callState" do
      throwError "reflection: expected callState"
    let base := initial.getArg! 0
    let pc := initial.getArg! 1
    let mem := initial.getArg! 3
    let (instructions, pcs) ← tables
    let finalState := rhs.getArg! 1
    let finalPC := finalState.getArg! 1
    let mut ops := []
    for k in [:indices.length] do
      let i := indices[k]!
      let some n ← getFinValue? i | throwError "reflection: nonliteral index"
      let some instr := instructions[n.2.val]? | throwError "reflection: index out of range"
      if k + 1 == indices.length && (← getNatValue? finalPC).isNone &&
          (instr.isAppOfArity ``Instr.op 1 &&
            ["JUMP", "JUMPI"].contains (instr.getArg! 0).getAppArgs.back!.getAppFn.constName!.getString!) then
        throwError "reflection: symbolic final jump target"
      let next ← if k + 1 < indices.length then do
          let some j ← getFinValue? indices[k+1]! | throwError "reflection: nonliteral index"
          pure pcs[j.2.val]!
        else pure ((← getNatValue? finalPC).getD (pcs[n.2.val]! + 1))
      ops := (← reflectInstr instr pcs[n.2.val]! next) :: ops
    let (vars, terms, tail) ← reifyStack (initial.getArg! 2)
    let shared ← mkAppM ``State.toSharedState #[base]
    let calldata ← mkAppM ``ExecutionEnv.calldata #[← mkAppM ``SharedState.executionEnv #[shared]]
    let rho := mkApp2 (mkConst ``Env.mk) vars calldata
    let config := mkApp2 (mkConst ``Config.mk) terms (mkConst ``Mem.initial)
    let program ← mkListLit (mkConst ``Op) ops.reverse
    trace[opt.reflect] "decoded {indices.length} instructions"
    let result ← reduce (mkApp2 (mkConst ``run) program config)
    unless result.isAppOfArity ``Option.some 2 do throwError "reflection: symbolic execution failed"
    let r := result.getArg! 1
    let cert ← mkDecideProof (← mkEq (mkApp2 (mkConst ``run) program config) result)
    let proof := mkAppN (mkConst sound) #[program, path, config, r, rho, mem, tail, base, pc, cert]
    let mut proof := proof
    let mut goals : List MVarId := []
    for _ in [:6] do
      let ty ← whnf (← inferType proof)
      let h ← mkFreshExprSyntheticOpaqueMVar ty.bindingDomain!
      proof := mkApp proof h
      goals := goals ++ [h.mvarId!]
    let some (_, _, middle) := (← inferType proof).eq? | throwError "reflection: invalid soundness result"
    let bridge ← mkFreshExprSyntheticOpaqueMVar (← mkEq middle rhs)
    let full ← mkEqTrans proof bridge
    -- The kernel checks the input denotation conversion. Meta-level default
    -- transparency can unfold the whole located bytecode before the state.
    withTransparency .all (g.assign full)
    replaceMainGoal (goals ++ [bridge.mvarId!])
    evalTactic finish
    trace[opt.reflect] "reflected {indices.length} instructions"

def reflectBlock (tables : MetaM (Array Expr × Array Nat)) (sound : Name)
    (finish : Syntax) : TacticM Unit := do
  try withOptions (fun o => o.set `maxRecDepth (10000 : Nat)) (reflectBlockImpl tables sound finish)
  catch e =>
    trace[opt.reflect] "fallback: {e.toMessageData}"
    throw e

end MlDsaOptCommon.Reflect
