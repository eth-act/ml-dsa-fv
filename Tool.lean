import MlDsa44.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
import YulParser.Compile
import EvmProof.Bytecode

/-!
Developer tool (not part of any proof):

* `spec`               check the spec against `vectors/*.txt`;
* `compile YUL HEX`    compile Yul with the pinned verified compiler (classic
                       backend) and write lowercase hex;
* `run HEX`            execute the bytecode in the pinned semantics on
                       `vectors/calldata.txt`, compare with the spec, print gas;
* `bytes HEX NS`       print a reducible Lean byte literal for the artifact;
* `instrs HEX NS`      print the disassembled instruction list.
-/

open EvmSemantics
open MlDsa44

def hexToBytes? (text : String) : Option ByteArray :=
  let text := text.trimAscii.copy
  if text == "-" then some .empty
  else if text.length % 2 != 0 then none
  else if !text.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') then none
  else some (Hex.hexToBytes text)

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

def readLines (path : String) : IO (List (List String)) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").filter (· ≠ "") |>.map fun line =>
    (line.splitOn " ").filter (· ≠ "")

def decodeHex (field : String) : IO ByteArray :=
  match hexToBytes? field with
  | some b => pure b
  | none => throw (IO.userError s!"bad hex field of length {field.length}")

def checkSpec : IO UInt32 := do
  let mut failures := 0
  let mut count := 0
  for row in ← readLines "vectors/acvp_internal.txt" do
    match row with
    | [pk, sig, m, expected] =>
      count := count + 1
      let got := Fips204.verifyInternal (← decodeHex pk) (← decodeHex m) (← decodeHex sig)
      if got != (expected == "1") then
        failures := failures + 1
        IO.println s!"ACVP #{count}: expected {expected}, got {got}"
    | _ => throw (IO.userError "malformed acvp row")
  IO.println s!"acvp verifyInternal: {count - failures}/{count} agree"
  let mut cdCount := 0
  let mut cdFailures := 0
  for row in ← readLines "vectors/calldata.txt" do
    match row with
    | cd :: expected :: note =>
      cdCount := cdCount + 1
      let out := spec (← decodeHex cd)
      let want := (ByteArray.mk (Array.replicate 31 0)).push (if expected == "1" then 1 else 0)
      if out != want then
        cdFailures := cdFailures + 1
        IO.println s!"calldata #{cdCount} ({" ".intercalate note}): spec disagrees"
    | _ => throw (IO.userError "malformed calldata row")
  IO.println s!"calldata spec: {cdCount - cdFailures}/{cdCount} agree"
  return if failures + cdFailures == 0 then 0 else 1

def runVectors (hexPath : String) : IO UInt32 := do
  let code ← decodeHex (← IO.FS.readFile hexPath)
  IO.println s!"bytecode: {code.size} bytes"
  let mut failures := 0
  let mut maxGas := 0
  for row in ← readLines "vectors/calldata.txt" do
    match row with
    | cd :: expected :: note =>
      let input ← decodeHex cd
      let start := initialState code input 1_000_000_000
      let final := runEvm 400_000_000 start
      let gas := start.gasAvailable - final.gasAvailable
      maxGas := max maxGas gas
      let want := (ByteArray.mk (Array.replicate 31 0)).push (if expected == "1" then 1 else 0)
      let ok := final.isDone && final.halt == .Returned && final.hReturn == want
      if !ok then failures := failures + 1
      let status := if ok then "ok" else
        s!"FAIL halt={repr final.halt} done={final.isDone} ret={Hex.bytesToHex final.hReturn}"
      IO.println s!"{input.size}\t{gas}\t{status}\t{" ".intercalate note}"
    | _ => throw (IO.userError "malformed calldata row")
  IO.println s!"max gas: {maxGas}, failures: {failures}"
  return if failures == 0 then 0 else 1

/-- Compile without the optimizer pipeline: parse, normalize (hoist and
disambiguate functions) and compile with the verified classic code generator.
Every source function stays a separately callable bytecode subroutine. -/
def compileRaw (source : String) : Option ByteArray := do
  match YulParser.parseSource source with
  | some (.block block) =>
    let raw := YulParser.pruneLinkerBlock (YulParser.decodeValueStmts block)
    let b := YulEvmCompiler.Optimizer.Normalize.normalize
      (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
        YulSemantics.EVM.ExternalCreates.none .any)
      (raw.map YulParser.desugarStmt)
    return YulEvmCompiler.assemble (← YulEvmCompiler.compile b)
  | _ => none

def compileYul (optimize : Bool) (yulPath hexPath : String) : IO UInt32 := do
  let source ← IO.FS.readFile yulPath
  let code? := if optimize then YulParser.compileSourceWithBackend source [] .classic
    else compileRaw source
  match code? with
  | none => IO.eprintln s!"{yulPath}: compiler rejected source"; return 2
  | some code =>
    IO.FS.writeFile hexPath (Hex.bytesToHex code ++ "\n")
    IO.println s!"{code.size} bytes"
    return 0

def emitBytes (hexPath ns : String) : IO UInt32 := do
  let code ← decodeHex (← IO.FS.readFile hexPath)
  let chunk := 1024
  let chunks := (List.range ((code.size + chunk - 1) / chunk)).map fun c =>
    code.extract (c * chunk) (min code.size ((c + 1) * chunk))
  IO.println "import EvmSemantics.Data.Hex\nset_option warningAsError true\nset_option maxRecDepth 100000\n"
  IO.println "/-! Generated by `lake exe mldsa44tool bytes`; do not edit. -/\n"
  IO.println s!"namespace {ns}\n"
  for (c, i) in chunks.zipIdx do
    let body := ", ".intercalate (c.toList.map fun b => s!"0x{Hex.bytesToHex (ByteArray.mk #[b])}")
    IO.println s!"private abbrev referenceChunk{i} : ByteArray := ByteArray.mk #[{body}]\n"
  let sum := " ++ ".intercalate ((List.range chunks.length).map fun i => s!"referenceChunk{i}")
  IO.println s!"abbrev referenceBytes : ByteArray := {sum}\n"
  IO.println s!"theorem referenceBytes_size : referenceBytes.size = {code.size} := by decide\n"
  IO.println s!"end {ns}"
  return 0

def emitInstrs (hexPath : String) : IO UInt32 := do
  let code ← decodeHex (← IO.FS.readFile hexPath)
  let instrs := EvmProof.Bytecode.disassemble code
  IO.println s!"-- {instrs.length} instructions"
  let mut pc := 0
  for ins in instrs do
    let imm := if ins.immediate.isEmpty then "" else
      " 0x" ++ Hex.bytesToHex (ByteArray.mk ins.immediate.toArray)
    IO.println s!"{pc}: {repr ins.opcodeOperation?}{imm}"
    pc := pc + ins.bytes.length
  return 0

/-- Entry addresses of every source function in the unoptimized compile. -/
def emitLayout (yulPath : String) : IO UInt32 := do
  match YulParser.parseSource (← IO.FS.readFile yulPath) with
  | some (.block block) =>
    let raw := YulParser.pruneLinkerBlock (YulParser.decodeValueStmts block)
    let b := YulEvmCompiler.Optimizer.Normalize.normalize
      (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
        YulSemantics.EVM.ExternalCreates.none .any)
      (raw.map YulParser.desugarStmt)
    let (scope, _) := YulEvmCompiler.hoistInfos 0 b
    match YulEvmCompiler.compileAsm b with
    | none => IO.eprintln "compiler rejected source"; return 2
    | some asm =>
      let addrs := YulEvmCompiler.labelAddrs asm
      for (f, info) in scope do
        IO.println s!"{f} entry={addrs.getD info.entry 0} arity={info.arity} rets={info.rets}"
      return 0
  | _ => IO.eprintln "not a block"; return 2

/-- Print the proof-facing artifact module: the compiler's instruction list,
the assembly equation and certified instruction lookup. -/
def emitArtifact (yulPath : String) : IO UInt32 := do
  let source ← IO.FS.readFile yulPath
  let some (.block block) := YulParser.parseSource source
    | IO.eprintln "not a block"; return 2
  let raw := YulParser.pruneLinkerBlock (YulParser.decodeValueStmts block)
  let b := YulEvmCompiler.Optimizer.Normalize.normalize
    (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
      YulSemantics.EVM.ExternalCreates.none .any)
    (raw.map YulParser.desugarStmt)
  let some instrs := YulEvmCompiler.compile b
    | IO.eprintln "compiler rejected source"; return 2
  let n := instrs.length
  let chunk := 400
  let chunks := (List.range ((n + chunk - 1) / chunk)).map fun c =>
    (instrs.drop (c * chunk)).take chunk
  IO.println "import EvmProof.Program\nimport MlDsa44.Proofs.WellFormed\nimport MlDsa44.Reference.Bytecode\n"
  IO.println "set_option warningAsError true\nset_option maxRecDepth 100000\n"
  IO.println "/-! Generated by `lake exe mldsa44tool artifact`; do not edit.\n\nStructural certificate for the frozen reference bytecode: the verified\ncompiler's instruction list, its assembly equation, and proof-carrying\ninstruction lookup for `EvmProof.Stepper.runLocatedBlock` paths. -/\n"
  IO.println "namespace MlDsa44.Proofs.Artifact\n\nopen EvmSemantics\nopen EvmSemantics.EVM\nopen YulEvmCompiler\n"
  for (c, i) in chunks.zipIdx do
    let body := ",\n ".intercalate (c.map fun ins => s!"{repr ins}")
    IO.println s!"def instructions{i} : List Instr :=\n[{body}]\n"
  let sum := " ++ ".intercalate ((List.range chunks.length).map fun i => s!"instructions{i}")
  IO.println s!"def referenceInstructions : List Instr :=\n  {sum}\n"
  IO.println s!"@[simp] theorem referenceInstructions_length : referenceInstructions.length = {n} := by\n  rfl\n"
  IO.println "theorem assemble_referenceInstructions :\n    assemble referenceInstructions = MlDsa44.referenceBytecode := by\n  rfl\n"
  IO.println "def referenceArtifact : EvmProof.ProgramArtifact where\n  code := MlDsa44.referenceBytecode\n  instructions := referenceInstructions\n  assembly_eq := assemble_referenceInstructions\n"
  IO.println "theorem allWellFormedB :\n    referenceInstructions.all (MlDsa44.Proofs.wellFormedB .Osaka) = true := by\n  rfl\n"
  IO.println "theorem allWellFormed : EvmProof.Stepper.AllWellFormed referenceArtifact .Osaka :=\n  MlDsa44.Proofs.allWellFormed_of_all allWellFormedB\n"
  IO.println s!"/-- Proof-carrying instruction lookup. -/\ndef located (index : Fin {n}) : EvmProof.Stepper.Located referenceArtifact .Osaka :=\n  EvmProof.Stepper.Located.ofIndex allWellFormed\n    ⟨index.val, by rw [referenceArtifact, referenceInstructions_length]; exact index.isLt⟩\n"
  IO.println s!"/-- A certified path from a list of instruction indices. -/\ndef locatedPath (indices : List (Fin {n})) :\n    List (EvmProof.Stepper.Located referenceArtifact .Osaka) :=\n  indices.map located\n"
  IO.println "end MlDsa44.Proofs.Artifact"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["spec"] => checkSpec
  | ["compile", yul, hex] => compileYul false yul hex
  | ["compile-opt", yul, hex] => compileYul true yul hex
  | ["run", hex] => runVectors hex
  | ["bytes", hex, ns] => emitBytes hex ns
  | ["instrs", hex] => emitInstrs hex
  | ["layout", yul] => emitLayout yul
  | ["artifact", yul] => emitArtifact yul
  | _ =>
    IO.eprintln "usage: mldsa44tool (spec | compile[-opt] YUL HEX | run HEX | bytes HEX NS | instrs HEX | layout YUL | artifact YUL)"
    return 64
