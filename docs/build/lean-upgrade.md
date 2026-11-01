# Lean toolchain upgrade (4.33.0 → 4.34.1 / 4.35.0): negative result

Hypothesis tested: a newer toolchain alone speeds up the build. Lean 4.30–4.33
carry the `instantiateMVars` regression lean4#12233 (lean4#14329, fixed by
lean4#14520 in 4.34), and later releases also include simp and kernel work.

**Verdict: do not adopt.** On 4.34.1, master does not build: the three
`Fn.Blk.BodyA` modules fail with `(kernel) deep recursion detected`. On the
other 577 modules CPU falls only 2.3%, and `MlDsa.Bridge44` regresses from 3 s
to 139 s. On 4.35.0, the pinned evm-semantics (part of the trust boundary)
fails to elaborate.

All numbers come from one a1.3xlarge orb (16 cores, 43 GB) in one session on
2026-11-01. CPU is user+sys. Per-module figures were sampled from `/proc`
every 0.2 s during `lake build`; "alone" means `lean` run serially on one
module with all its imports built.

## 1. The instantiateMVars regression does not affect this repo

`-Dprofiler=true` on the heaviest modules (623dd95 on 4.33.0, each module
alone; cumulative seconds):

| module | type checking (kernel) | tactic execution | simp | instantiate metavars | share common exprs |
|---|---:|---:|---:|---:|---:|
| MlDsaOpt44.Fn.Sponge.Trabs | 41.8 | 17.8 | 8.4 | 0.36 | 0.80 |
| MlDsaOpt44.Fn.Blk.BodyA (unchunked) | 40.1 | 2.6 | 4.5 | 0.22 | 0.58 |
| MlDsaOpt44.Main.Tbl.Blocks | 54.5 | 4.3 | 3.2 | 0.12 | 0.51 |
| MlDsaOpt87.Main.S1.Tbl | 52.2 | 4.2 | 3.4 | 0.13 | 0.54 |
| MlDsaOpt87.Fn.Decode.HintBlocks | 24.3 | 15.7 | 17.7 | 0.27 | 1.81 |
| MlDsaOpt44.Fn.Fix.Blocks | 8.4 | 29.5 | 6.9 | 0.00 | 0.42 |
| MlDsa44.Proofs.Fn.Keccak.Blocks2 | 20.3 | 5.1 | 8.3 | 0.00 | 0.93 |
| MlDsaOpt44.Fn.Hint.PackCode | 3.9 | 19.8 | 35.7 | 0.54 | 1.94 |
| MlDsaOpt44.Main.Mu.Blocks | 15.1 | 6.4 | 3.8 | 0.19 | 0.38 |
| MlDsaOpt44.Main.SegG234.G4 | 2.0 | 6.4 | 2.7 | 0.05 | 0.09 |

Neither "instantiate metavars" nor "share common exprs" exceeds 2 s in any
module. The time goes to the kernel and to simp, so lean4#14520 has nothing
to recover here.

## 2. Measurements

### Full `lake build` (all default targets; dependencies prebuilt)

| tree | toolchain | wall | CPU | result |
|---|---|---:|---:|---|
| 623dd95 | 4.33.0 | 9:06 | 6235 s | ok; peak 4.9 GB per process, 11.9 GB total anonymous |
| master d4c34ee (chunked blocks) | 4.33.0 | 8:45 | 6266 s | ok; peak 4.9 GB per process, 12.0 GB total |
| master d4c34ee + 4.34.1 | 4.34.1 | 6:20 | 5142 s | **fails**: 3 × `Fn.Blk.BodyA`; 458 modules built, the rest blocked |
| same, rest of the build | 4.34.1 | 3:07 | 1044 s | measurement only: BodyA's kernel check skipped (`debug.skipKernelTC`, not committed) so its dependents could build |

Per-module CPU, master on 4.33.0 against 4.34.1, built in parallel:

* All 577 modules except the 3 BodyA: 6061 s → 5922 s (−2.3%).
  Without Bridge44: 6058 s → 5783 s (−4.5%).
* Gains: Main.Tbl.Blocks 76.3 → 60.6, Opt87 Main.S1.Tbl 71.7 → 55.8,
  Main.Fin.Blocks 30.0 → 24.3, Main.Mu.Blocks 35.2 → 31.1,
  Main.SegG234.G4 18.3 → 16.1, Opt87 Ginit.Lanes 49.8 → 42.8,
  Keccak.Blocks2 48.2 → 42.9, Sponge.Trabs 51.9 → 46.8,
  Hint.PackCode 85.3 → 79.9.
* Flat: Fix.Blocks 55.4 → 55.7, Opt87 Decode.HintBlocks 76.9 → 74.8.
* **Regression: `MlDsa.Bridge44` 3.0 s → 138.7 s CPU, 1.7 GB → 11.6 GB
  RSS.** This raises the build's peak total memory from 12.0 GB to 18.8 GB.
  Not investigated further.

On 623dd95 (blocks not chunked yet), 4.34.1 cut CPU 7.4% on the 416 modules
that built under both toolchains. Most of that was Sponge.Trabs: 81 → 48 s ×3.
Chunking (b52662d) has since taken most of that gain on 4.33.0 as well.

Heavy modules alone on 4.33.0 at 623dd95 (wall / CPU / max RSS):
Sponge.Trabs 73.5 / 77.6 / 3173 MB, Blk.BodyA 49.2 / 50.1 / 2907,
Main.Tbl.Blocks 63.8 / 71.1 / 3551, Opt87 Decode.HintBlocks 62.0 / 80.9 / 3901,
Opt87 Main.S1.Tbl 61.9 / 68.6 / 3573, Fix.Blocks 51.4 / 58.9 / 3568,
Keccak.Blocks2 42.2 / 47.3 / 2949, Hint.PackCode 33.8 / 81.4 / 4084,
Main.Mu.Blocks 29.9 / 37.4 / 3076, Main.SegG234.G4 15.5 / 16.9 / 3119,
MlDsa44 Main.Prelude 11.2 / 14.0 / 2804, Main.Hashes 12.2 / 14.0 / 2360.
On master d4c34ee: Trabs 41.2 / 45.1, BodyA 16.4 / 17.3. The serial run was
stopped there, and the matching 4.34.1 serial and profiler runs were not
made.

## 3. Why BodyA fails: the kernel no longer has its equiv_manager

On 4.34.1, `MlDsaOpt{44,65,87}.Fn.Blk.BodyA` fail with
`(kernel) deep recursion detected` after about 25 s. They pass in 19 s on
4.33.0. The failure persists in every variant tried:

* `maxRecDepth` 20000: fails after 47 s. 100000: still running after 12 min,
  killed. The unchunked 623dd95 version was still running after 7 min.
* `-DElab.async=false`, `-s 4000000` (thread stack) or `ulimit -s unlimited`
  give the same failure. Since lean4#13956 (4.33.0) the kernel's depth limit
  is `maxRecDepth`, not the native stack.
* Chunk size 8 instead of 32: same failure.
* With the old lemma names and `linter.deprecated false` instead of the
  renames: same failure.
* `reach_block … (by decide +kernel) ?_; sorry` passes in 2.3 s. The
  failing check is therefore in the proof `opt44_block` builds, not in the
  cost side condition.

A gdb dump of the running process (maxRecDepth 100000, 45 s in) shows the
kernel thread 1.21 M frames deep. The frames are almost all one cycle:

```
338980 lean::type_checker::is_def_eq_core
193705 lean::type_checker::lazy_delta_reduction / lazy_delta_reduction_step
193704 lean::type_checker::is_def_eq_args
145270 lean::type_checker::quick_is_def_eq
145270 lean::type_checker::is_def_eq_binding
  4210 lean::expr_eq_fn<false>::apply   (top of stack)
```

So the kernel is deciding definitional equality of two large terms that
differ deep inside, descending one binder or application at a time. In
`src/kernel/type_checker.cpp`, `quick_is_def_eq` starts with
`m_st->m_eqv_manager.is_equiv(t, s, use_hash)` in v4.33.0. In v4.33.1,
v4.34.1 and v4.35.0 it starts with `t == s || succeeded_before(t, s)` and
has no `equiv_manager` at all. That change is lean4#14806, a soundness fix:
the union-find made `is_def_eq` results depend on query order, because
`is_def_eq` is not transitive. The equiv_manager compared such terms
structurally modulo already-proved equivalences, without counting depth. On
4.33.0 that is where the time went: b52662d's perf profile of BodyA shows 86%
in `equiv_manager` hash lookups. Now each level costs one kernel recursion
and the queries are not merged.

Since the fix is in 4.33.1 and every later release, upgrading to any newer
toolchain needs the BodyA proof (and perhaps Bridge44) restructured to avoid
that comparison. I did not check whether 4.33.1 alone already fails; there is
no Mathlib v4.33.1 tag.

### Minimal reproducer: not made

A report against lean4#14806 would need a Mathlib-free file that passes the
kernel quickly on v4.33.0 and fails (or is far slower) on v4.33.1. That means
extracting the defeq query that recurses. Two ways to do it:

* Export BodyA's proof with lean4export and replay it in a kernel built with
  logging around `is_def_eq_binding`.
* Bisect the `opt44_block` simp proof by instruction count, taking the
  smallest prefix that still needs a high `maxRecDepth`. The state terms then
  become the reproducer.

Neither was done.

## 4. Lean 4.35.0

Using Mathlib v4.35.0 with the same dependency commits, evm-semantics
2f8714d fails in `EvmSemantics/Data/UInt256.lean` (the `LawfulBEq UInt256`
instance):

```
42:30: Application type mismatch: The argument h has type
  ({ val := val✝¹ } == { val := val✝ }) = true
but is expected to have type decide ?m.72 = true   (in of_decide_eq_true h)
44:36: typeclass instance problem is stuck
```

Adding `backward.isDefEq.throwOnStuckAfterApp = true` and
`backward.isDefEq.respectTransparency.instanceSearchTypes = false` to its
`leanOptions` (the release notes' migration options) does not fix it.
Getting further would need a source edit inside the trust boundary, so I
stopped there. The 4.35.0 kernel has the same `quick_is_def_eq` as 4.34.1,
so BodyA would fail there too.

## 5. What 4.34.1 needed besides BodyA

* `lean-toolchain` `v4.34.1`, Mathlib `rev = "v4.34.1"`, and `lake update
  mathlib`, which moves batteries, aesop, Qq, plausible, proofwidgets,
  importGraph, LeanSearchClient and Cli to Mathlib's pins. evm-semantics,
  yul-semantics and yul-compiler stay at the same commits.
* Lean 4.34 deprecates (since 2026-07-21) `if_pos`, `if_neg`, `dif_pos`,
  `dif_neg`, `if_true` and `if_false`. Under `set_option warningAsError true`
  (most proof files, and all of yul-semantics) each use becomes an error.
  The renames are mechanical:
  `if_pos → ite_eq_left`, `if_neg → ite_eq_right`, `dif_pos → dite_eq_left`,
  `dif_neg → dite_eq_right`, `if_true → ite_true`, `if_false → ite_false`:

  ```sh
  sed -i -E 's/\bif_pos\b/ite_eq_left/g; s/\bif_neg\b/ite_eq_right/g; s/\bdif_pos\b/dite_eq_left/g; s/\bdif_neg\b/dite_eq_right/g; s/\bif_true\b/ite_true/g; s/\bif_false\b/ite_false/g' FILES
  ```

  * This repo: 212 files (`.lean`, plus the generators
    `scripts/proofgen_artifact.py`, `MlDsaOpt44/Fn/Ntt/gen_ntt.py`,
    `MlDsaOpt44/Main/Wp11Gen/gen_init.py`, `…/gen_muproof.py`,
    `MlDsaOpt65/Fn/Ginit/gen_lanes.py`, `MlDsaOpt65/Main/S1/gen_s1.py`,
    `…/gen_s1_fin.py`).
  * yul-compiler c2e44cd2 (local patch): `YulEvmCompiler/{Instr,Decode,StateRel,Value}.lean`.
  * yul-semantics c9914c13 (local patch): `YulSemantics/Dialect/EVM.lean`.
  * evm-semantics: no change needed on 4.34.1.

  Apart from BodyA, nothing else in the repo broke on 4.34.1.
