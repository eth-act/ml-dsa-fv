import MlDsa.Spec.Interface
import MlDsa44.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
import YulParser.Compile

/-!
Developer tool for the parametric spec (not part of any proof). `NN` is `44`,
`65` or `87`; vectors are `vectors/*.txt` for 44 and `vectors/mldsaNN/*.txt`
otherwise.

* `spec NN`                check `MlDsa.Fips204.verifyInternal` on the ACVP
                           rows and `MlDsa.Interface.spec` on the calldata
                           rows (for 44 also against `MlDsa44.spec`);
* `run NN HEX`             execute the bytecode in the pinned semantics on the
                           calldata vectors, compare with the spec, print gas;
* `profile NN HEX YUL ROW` per-function gas of calldata row `ROW` (1-based):
                           self gas, gas including callees and call counts,
                           from the function entries of the unoptimized
                           compile of `YUL` (which must produce `HEX`).

Compile Yul with `mldsa44tool compile`.
-/

open EvmSemantics
open MlDsa

def hexToBytes? (text : String) : Option ByteArray :=
  let text := text.trimAscii.copy
  if text == "-" then some .empty
  else if text.length % 2 != 0 then none
  else if !text.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') then none
  else some (Hex.hexToBytes text)

def readLines (path : String) : IO (List (List String)) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").filter (· ≠ "") |>.map fun line =>
    (line.splitOn " ").filter (· ≠ "")

def decodeHex (field : String) : IO ByteArray :=
  match hexToBytes? field with
  | some b => pure b
  | none => throw (IO.userError s!"bad hex field of length {field.length}")

structure Target where
  params : Params
  address : AccountAddress
  dir : String

def target : String → IO Target
  | "44" => pure ⟨.mldsa44, AccountAddress.ofNat 0x8212, "vectors"⟩
  | "65" => pure ⟨.mldsa65, AccountAddress.ofNat 0x8213, "vectors/mldsa65"⟩
  | "87" => pure ⟨.mldsa87, AccountAddress.ofNat 0x8214, "vectors/mldsa87"⟩
  | s => throw (IO.userError s!"unknown parameter set {s}")

def word (b : Bool) : ByteArray :=
  (ByteArray.mk (Array.replicate 31 0)).push (if b then 1 else 0)

def checkSpec (nn : String) : IO UInt32 := do
  let t ← target nn
  let mut failures := 0
  let mut count := 0
  for row in ← readLines s!"{t.dir}/acvp_internal.txt" do
    match row with
    | [pk, sig, m, expected] =>
      count := count + 1
      let got := Fips204.verifyInternal t.params (← decodeHex pk) (← decodeHex m) (← decodeHex sig)
      if got != (expected == "1") then
        failures := failures + 1
        IO.println s!"ACVP #{count}: expected {expected}, got {got}"
    | _ => throw (IO.userError "malformed acvp row")
  IO.println s!"ML-DSA-{nn} acvp verifyInternal: {count - failures}/{count} agree"
  let mut cdCount := 0
  let mut cdFailures := 0
  for row in ← readLines s!"{t.dir}/calldata.txt" do
    match row with
    | cd :: expected :: note =>
      cdCount := cdCount + 1
      let input ← decodeHex cd
      let out := Interface.spec t.params input
      let agree44 := nn != "44" || out == MlDsa44.spec input
      if out != word (expected == "1") || !agree44 then
        cdFailures := cdFailures + 1
        IO.println s!"calldata #{cdCount} ({" ".intercalate note}): spec disagrees"
    | _ => throw (IO.userError "malformed calldata row")
  IO.println s!"ML-DSA-{nn} calldata spec: {cdCount - cdFailures}/{cdCount} agree"
  return if failures + cdFailures == 0 then 0 else 1

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

def runVectors (nn hexPath : String) : IO UInt32 := do
  let t ← target nn
  let code ← decodeHex (← IO.FS.readFile hexPath)
  IO.println s!"bytecode: {code.size} bytes"
  let mut failures := 0
  let mut maxGas := 0
  for row in ← readLines s!"{t.dir}/calldata.txt" do
    match row with
    | cd :: expected :: note =>
      let input ← decodeHex cd
      let start := Interface.initialState t.address code input 1_000_000_000
      let final := runEvm 1_000_000_000 start
      let gas := start.gasAvailable - final.gasAvailable
      maxGas := max maxGas gas
      let ok := final.isDone && final.halt == .Returned && final.hReturn == word (expected == "1")
        && final.hReturn == Interface.spec t.params input
      if !ok then failures := failures + 1
      let status := if ok then "ok" else
        s!"FAIL halt={repr final.halt} done={final.isDone} ret={Hex.bytesToHex final.hReturn}"
      IO.println s!"{input.size}\t{gas}\t{status}\t{" ".intercalate note}"
      (← IO.getStdout).flush
    | _ => throw (IO.userError "malformed calldata row")
  IO.println s!"max gas: {maxGas}, failures: {failures}"
  return if failures == 0 then 0 else 1

/-- Source names and entry addresses of the functions of the unoptimized
compile (as `mldsa44tool layout`). -/
def layout (yulPath : String) : IO (List (String × Nat)) := do
  match YulParser.parseSource (← IO.FS.readFile yulPath) with
  | some (.block block) =>
    let raw := YulParser.pruneLinkerBlock (YulParser.decodeValueStmts block)
    let b := YulEvmCompiler.Optimizer.Normalize.normalize
      (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
        YulSemantics.EVM.ExternalCreates.none .any)
      (raw.map YulParser.desugarStmt)
    let (scope, _) := YulEvmCompiler.hoistInfos 0 b
    match YulEvmCompiler.compileAsm b with
    | none => throw (IO.userError "compiler rejected source")
    | some asm =>
      let addrs := YulEvmCompiler.labelAddrs asm
      -- `hoistInfos` lists the functions in source order.
      let srcNames := (((← IO.FS.readFile yulPath).splitOn "function ").drop 1).map
        fun t => (t.takeWhile (· != '(')).toString.trimAscii.toString
      return scope.zipIdx.map fun ((f, info), i) =>
        ((srcNames[i]?).getD (toString f), addrs.getD info.entry 0)
  | _ => throw (IO.userError "not a block")

/-- Per-function gas: a step is charged to the function whose code range
contains its pc (self) and to every function on the call stack (inclusive).
A function is entered when control reaches its entry address and left when
control leaves its code range other than by a call. -/
def profile (nn hexPath yulPath : String) (rowIdx : Nat) : IO UInt32 := do
  let t ← target nn
  let code ← decodeHex (← IO.FS.readFile hexPath)
  let fns := ((← layout yulPath).toArray.qsort (fun a b => a.2 < b.2))
  -- Index 0 is the top-level code. The classic backend jumps over each
  -- function body with `PUSH2 next JUMP` / `next: JUMPDEST`; following that
  -- chain from pc 0 reaches the top-level statements after the last body.
  let names := #["<main>"] ++ fns.map (·.1)
  let isJump (t : Nat) : Bool := t + 3 < code.size && code[t]! == 0x61 && code[t + 3]! == 0x56
  let target (t : Nat) : Nat := code[t + 1]!.toNat * 256 + code[t + 2]!.toNat
  let mut mainStart := 0
  for _ in [0:fns.size + 1] do
    if isJump mainStart then mainStart := target mainStart
    else if code[mainStart]! == 0x5b && isJump (mainStart + 1) then
      mainStart := target (mainStart + 1)
  let ranges := (#[(0, 0), (mainStart, 0)] ++ fns.mapIdx fun i (f : String × Nat) => (f.2, i + 1)).qsort
    (fun a b => a.1 < b.1)
  let owner (pc : Nat) : Nat := Id.run do
    let mut o := 0
    for r in ranges do
      if r.1 ≤ pc then o := r.2
    return o
  let ownerTbl := (Array.range (code.size + 1)).map owner
  let rows ← readLines s!"{t.dir}/calldata.txt"
  let some (cd :: _) := rows[rowIdx - 1]? | throw (IO.userError "no such row")
  let input ← decodeHex cd
  let mut s := Interface.initialState t.address code input 1_000_000_000
  let mut selfGas := Array.replicate names.size 0
  let mut inclGas := Array.replicate names.size 0
  let mut calls := Array.replicate names.size 0
  let mut stack : List Nat := [0]
  let isEntry := fun pc => fns.findIdx? (·.2 == pc)
  calls := calls.set! 0 1
  let mut steps := 0
  while !s.isDone && steps < 1_000_000_000 do
    let pc := s.pc.toNat
    let s' := EVM.stepF s
    let g := s.gasAvailable - s'.gasAvailable
    let o := ownerTbl[min pc code.size]!
    selfGas := selfGas.modify o (· + g)
    for f in stack.eraseDups do
      inclGas := inclGas.modify f (· + g)
    let pc' := s'.pc.toNat
    match isEntry pc' with
    | some i =>
      if pc' != pc + 1 then
        stack := (i + 1) :: stack
        calls := calls.modify (i + 1) (· + 1)
    | none =>
      let o' := ownerTbl[min pc' code.size]!
      while stack.length > 1 && stack.head! != o' do
        stack := stack.tail
    s := s'
    steps := steps + 1
  let total := 1_000_000_000 - s.gasAvailable
  IO.println s!"row {rowIdx}: calldata {input.size} bytes, total gas {total}, steps {steps}"
  IO.println "function\tcalls\tself\tinclusive"
  let order := (Array.range names.size).qsort fun a b => inclGas[a]! > inclGas[b]!
  for i in order do
    if calls[i]! > 0 then
      IO.println s!"{names[i]!}\t{calls[i]!}\t{selfGas[i]!}\t{inclGas[i]!}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["spec", nn] => checkSpec nn
  | ["run", nn, hex] => runVectors nn hex
  | ["profile", nn, hex, yul, row] => profile nn hex yul row.toNat!
  | _ =>
    IO.eprintln "usage: mldsatool (spec NN | run NN HEX | profile NN HEX YUL ROW)"
    return 64
