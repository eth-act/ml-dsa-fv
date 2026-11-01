# Build times

Per-module wall time, CPU and peak RSS, each module re-checked alone against
built imports by `scripts/time_modules.py` (run `lake build` first):

```sh
python3 scripts/time_modules.py -o docs/build/module-times-<commit>.tsv
```

| File | Commit | Machine | Modules | Σ wall | Σ CPU | Max RSS |
|---|---|---|---|---|---|---|
| `module-times-959ed80.tsv` | 959ed80 (before any speed work) | a1.3xlarge orb, 16 vCPU, 43 GB, Lean 4.33.0, `--jobs 1` | 579 | 6,197 s | 7,471 s | 4.8 GB |

`lake build` of all default targets on the same machine at 959ed80 (560
modules compiled, dependencies already built): 834 s wall, 9,322 s CPU.

## What made it faster

Before → after are wall seconds of one module run alone, on the same orb in
the same session.

### Block tactics run long paths in pieces (`foldl_chunks`, b52662d)

One `simp` over a whole straight-line path builds a proof whose kernel check
grows much faster than the path. For `MlDsaOpt44.Proofs.Blk.bodyA`, 340
instructions, the first 85 took 1.7 s in the kernel, the first 170 took 7.8 s
and all 340 took 78 s; perf put 86% of that time in the kernel's
`equiv_manager` comparing large states structurally. `foldl_chunks 32` runs
the same `simp` on 32 instructions at a time.

| Module | Before | After |
|---|---|---|
| `MlDsaOpt44.Fn.Blk.BodyA` | 93.4 | 22.3 |
| `MlDsaOpt44.Fn.Sponge.Trabs` | 125.4 | 55.1 |
| `MlDsa44.Proofs.Fn.Keccak.Blocks2` | 61.9 | 52.5 |

Modules made of many short blocks did not change.

### State-literal projections reduced with proofs (`MlDsaOptCommon.StateProj`)

simp's built-in projection reduction turns `{ … }.activeWords` into
`s.activeWords` without a proof. The kernel rechecks the step by first
unifying the literal `{ … }` with `s` field by field. That fails, and on the
way it evaluates every literal `natToBytesPadded v 32` in the memory
(`writeBytes` tests `bytes.size = 0`). Kernel diagnostics on `tbl_b0` showed
`List.concat`, `Array.push` and `ByteArray.set!` unfolded tens of thousands
of times. Pre-simprocs now reduce these chains with non-`rfl` lemmas:
`tbl_b0` kernel time 5.0 s → 1.1 s.

| Module (4f25d96 vs. its parent 7016fef) | Before | After |
|---|---|---|
| `MlDsaOpt44.Main.Tbl.Blocks` | 80.3 | 54.4 |
| `MlDsaOpt65.Main.S1.Tbl` | 72.9 | 51.4 |
| `MlDsaOpt87.Main.S1.Tbl` | 72.9 | 52.1 |
| `MlDsaOpt44.Main.Mu.Blocks` | 33.7 | 27.5 |
| `MlDsaOpt44.Main.Fin.Blocks` | 27.0 | 21.5 |
| `MlDsaOpt44.Main.Init.Blocks` | 17.6 | 14.2 |

### Whole tree

Clean `lake build` of all default targets, one after another on the same
a1.3xlarge orb with nothing else running:

| Commit | Wall | CPU |
|---|---|---|
| 959ed80 | 734 s | 8,247 s |
| e3d6f39 (chunks, halt premise, StateProj, first reflection) | 543 s | 6,534 s |
| 93a7b8a (plus Kf1/Kf4 reflection, `blk_disch`) | 499 s | 5,843 s |

Per-module profile (`time_modules.py --lean-arg=-Dprofiler=true
--save-output DIR`, both trees at once with `--jobs 3` each), 959ed80 →
e3d6f39, CPU seconds summed over modules: kernel 2,480 → 1,573, tactic
execution 2,267 → 1,250, simp 1,063 → 1,028, import 858 → 869,
interpretation 325 → 480, typeclass inference 389 → 386. Modules using the
block tactics are two thirds of the CPU (4,282 of 6,506 s at e3d6f39).

## Things that did not help

* Hash-consing the proof before the kernel sees it
  (`ShareCommon.shareCommon'`): `tbl_b0` 6.15 s → 6.38 s of kernel time.
* Chunk size below 32: `bodyA` kernel time is flat from 20 to 40 instructions
  per piece (5.9–6.1 s); 85 gives 7.9 s and 120 gives 9.6 s.
* Unfolding `runInstr` with a dsimproc that keeps the other opcodes' cases
  out of the proof: the proof term shrinks 8× (348k → 44k distinct subterms)
  but kernel time is unchanged.
* Trying `decide` before `omega` in the discharger: no change on `tbl_b0`.
