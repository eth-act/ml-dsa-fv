import Lean.Replay
/-!
# Kernel replay with bounded parallelism

`leanchecker` (shipped with the toolchain) replays every module matching a
prefix at once, which runs out of memory on this project. This is its
`replayFromImports`, unchanged, over an explicit module list with `-j` worker
threads: each module's own declarations are re-added to the environment of its
imports by the kernel (`Environment.replay`), so a declaration that was added
without kernel checking (`debug.skipKernelTC`, environment hacks) fails here.

Usage: `lake env gate_replay -j N OLEANS_FILE` (one `.olean` path per line).
-/

open Lean

/-- `replayFromImports` of `LeanChecker.lean` (Lean v4.33.0), given the module's `.olean`
path (the one the extractor resolved) instead of its name. -/
unsafe def replayFromImports (mFile : System.FilePath) : IO Unit := do
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  let (jobs, file) ← match args with
    | ["-j", j, f] => pure (j.toNat!, f)
    | _ => throw <| IO.userError "usage: gate_replay -j N OLEANS_FILE"
  initSearchPath (← findSysroot)
  let mods := ((← IO.FS.readFile file).splitOn "\n").filter (· ≠ "") |>.map System.FilePath.mk
  let queue ← IO.mkRef mods
  let failures ← IO.mkRef (#[] : Array String)
  let worker : IO Unit := do
    repeat
      let next ← queue.modifyGet fun q => match q with
        | [] => (none, [])
        | m :: tl => (some m, tl)
      let some m := next | break
      try
        replayFromImports m
        IO.println s!"replayed {m}"
      catch e =>
        IO.eprintln s!"REPLAY FAILED {m}: {e}"
        failures.modify (·.push s!"{m}")
  let tasks ← (List.range (max jobs 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for t in tasks do
    if let .error e := t.get then IO.eprintln s!"worker error: {e}"; failures.modify (·.push "worker")
  let fs ← failures.get
  IO.println s!"gate_replay: {mods.length} modules, {fs.size} failed"
  return if fs.isEmpty then 0 else 1
