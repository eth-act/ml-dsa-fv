# Proof-preservation gate

One command decides whether a change (a faster build, a faster proof, a
refactor) left everything proved exactly as it was:

```sh
python3 scripts/gate/gate.py check origin/master            # working tree vs master
python3 scripts/gate/gate.py check origin/master my-branch  # two revisions
python3 scripts/gate/gate.py snapshot origin/master -o base.tsv
python3 scripts/gate/gate.py check base.tsv my-branch       # revision vs a baseline (BASE only)
```

Exit status 0 means `GATE PASSED`; 1 means at least one `FAIL` line in the
report. Run it from a checkout of the **base** revision: the running gate must
be BASE's `scripts/gate/` (rule 6 below). Until the gate is on master, BASE
has none: pass `--bootstrap`, and the report says this checkout's gate
decided. `--allow-gate-change` is only for reviewing a change to the gate. `--allow-moves` tolerates
constants that only moved to another module; `--allow-lakefile-change` a
`lakefile.toml` that differs from BASE's (review it).

Each revision is checked out into `.lake/gate/wt` (sharing `.lake/packages`
with this checkout, which must be at the same pins), built incrementally and
summarised in a snapshot cached under `.lake/gate/snapshots/`, keyed by the
git tree and the gate's own hash. On a 16-core, 43 GB orb a revision costs
about 12 min to build from scratch, 2.5 min to extract, 12 min to replay
(6 workers, about 5 GB each; `--jobs` to change) and 3 min for the
generators; a second revision rebuilds and replays only what changed. To skip
the first build, copy a checkout's `.lake/build` into `.lake/gate/wt/.lake/`.

Regression tests: `python3 scripts/gate/test_gate.py` (38 tests, about a
minute; they build small Lean fixtures under /tmp).

## What fails the gate

Per revision (HEAD must pass all of these):

* **Build**: `lake build` (the default targets), every library root as an
  explicit module target (`lake build +MlDsa44 ...`, so lakefile facets cannot
  skip one), `lake build mldsa44tool mldsatool`, then `lake build --no-build`
  of the same targets (nothing stale may be extracted). Lake judges a module
  up to date by input hashes alone, so the extractor also checks that every
  recorded `.olean` is the one its Lake trace records; a mismatch (left by an
  interrupted build: an orphaned `lean` writing after `lake` died) fails. A
  gate run interrupted during its build leaves a marker, and the next run
  builds from scratch. Every command runs in a process group of its own that
  is killed with the gate (so no `lean` outlives it); one gate run at a time
  holds `.lake/gate/lock`; and a run refuses to start while any process still
  works inside the worktree.
* **Kernel replay** (`gate_replay`, the `replayFromImports` of the
  toolchain's `leanchecker` with bounded parallelism): every declaration of
  every project module (every module whose `.olean` was built in the
  worktree: Lean resolves each import and the gate keeps those whose `.olean`
  path is under `.lake/build`, whatever the module's name) is re-added by the kernel to the environment of
  its imports. Catches `debug.skipKernelTC` and anything
  else that put an unchecked declaration into an `.olean`. Verdicts are
  cached per module by a Merkle hash of its `.olean` bytes and those of its
  project imports.
* **Axiom policy**, decided by Lean (`gate_extract` runs Lean's own
  `CollectAxioms.collect`, copied verbatim because it is private, without the
  extension lookup, since extensions load only by running the imported
  modules' initializers; a test checks it against `#print axioms`): every
  constant of every project module, theorems and definitions, depends only on
  `propext`, `Classical.choice`, `Quot.sound`; no project module declares an
  `axiom`; no name contains a control character. `sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceBool`
  and `Lean.ofReduceNat` (`native_decide`, `bv_decide`) are rejected even if
  the list were widened.
* **Headline theorems**: the four per bytecode (`MlDsa44.Proofs.reference_*`,
  `MlDsaOpt{44,65,87}.Proofs.opt_*`) exist and are theorems.
* **Bytecode literals**: `MlDsa44.referenceBytecode` and
  `MlDsaOpt{44,65,87}.optBytecode`, evaluated (compiled code, in a process of
  its own), equal the bytes of `reference.hex` / `opt.hex`. Their logical value
  is also part of the signature diff.

Relative to BASE:

* **Signature diff** over every constant of every project module (auxiliary
  `match_`/`proof_`/`eq_`/`_private` internals excluded by name, see below):
  removed, changed kind, changed statement, changed meaning of a definition
  that some theorem statement depends on, changed axiom set (even within the
  allowed three: this is what caught the silent `Classical.choice` in clifv),
  and moved to another module (unless `--allow-moves`). Added constants are
  listed, not failed.
* **Frozen artifacts**, byte-identical: `*.hex`, `MlDsa{44,65,87}/Reference/*`,
  `MlDsaOpt/**`, `MlDsaOpt{44,65,87}/{Bytecode.lean,listing.tsv}`,
  `docs/reference.{listing,layout}`; and the four bytecode literals.
* **Toolchain and pins**: `lean-toolchain`, the `lean --githash` that actually
  runs in the worktree (`ELAN_*`, `LEAN*`, `LAKE*` variables are cleared), and
  `lake-manifest.json` identical; only git dependencies, with the shared
  `.lake/packages` checkouts at exactly those revisions; `lakefile.toml`
  identical unless `--allow-lakefile-change`; `lakefile.lean` and any
  `lakefile.toml` key outside a short whitelist (`buildDir`, `srcDir`, `globs`,
  `moreLeanArgs`, ...) are refused.
* Every check below that passes on BASE must pass on HEAD:
  * each Lean file outside the libraries compiles (`*/checks/*.lean`,
    `scripts/*.lean`);
  * each deterministic generator reproduces the checked-in files of that
    revision exactly (table below).
* The running gate is BASE's `scripts/gate/` (`--bootstrap` if BASE has none),
  and HEAD's equals it, unless `--allow-gate-change`.
* Either snapshot made with `--skip-generators` (a dev loop) fails.

### How "meaning" is hashed

`gate_extract` imports the built project (no initializers, no extension
import hooks) and digests with SHA-256 (128 bits printed), for each constant,
its type and (for definitions) its body twice: `local` (structure and constant
names) and `closure` (structure plus, for each constant mentioned, the
closure digest of that constant: a theorem's statement, a definition's type and
body, an inductive's constructors, recursively through the project). Binder
names, binder info and metadata are ignored; private names are digested by
their user name, so moving a private declaration is a move. Constants outside the project are
hashed by name: they are fixed by the toolchain and the manifest, which must
be identical. So a theorem's closure hash changes iff its statement, or a
definition its statement (transitively) mentions, changes; the report says
which constants were edited directly (local hash changed) and which changed
through a dependency. A definition body that no theorem statement reaches
(tactics, simprocs, executable code) cannot change what is proved; its changes
are listed as notes.

Elaborator- and compiler-generated names (`Name.isInternalDetail` or a
reserved name such as `eq_def`, or a name under one such as `match_1.splitter`, unless it is a theorem with a source range,
i.e. one a person wrote) come and go with the way proofs are written; they are
not compared by name, but their meaning enters every closure hash
that mentions them and their axioms are audited like everything else.

### Generators (checked-in output reproduced exactly on master `3b6af1b`)

| generator | output |
|---|---|
| `gen_reference.py`, `gen_reference_param.py 44/65/87` | `MlDsa{44,65,87}/Reference/reference.yul` |
| `gen_opt.py`, `gen_opt.py --version v2` | `MlDsaOpt/NN/{opt.hex,opt.asm,layout.txt}`, `MlDsaOpt/NN/v2/*` |
| `proofgen_artifact.py MlDsaOpt/NN/opt.hex MlDsaOptNN MlDsaOptNN optNN M` (M = 2097, 2865, 2897) | `MlDsaOptNN/{Bytecode,Artifact,Infra,Infra/*}.lean`, `listing.tsv` |
| `mldsa44tool compile` (44, 65, 87) | `MlDsa{44,65,87}/Reference/reference.hex` |
| `mldsa44tool bytes`, `artifact`, `layout` | `MlDsa44/Reference/Bytes.lean`, `MlDsa44/Proofs/Artifact.lean`, `docs/reference.layout` |
| `gen_keccak.py` | `MlDsa44/Proofs/Fn/Keccak/{Rows,Blocks1,Blocks2,RoundSpec}.lean` |
| `MlDsaOpt44/Fn/Kf1/gen_kf1.py` | `MlDsaOpt44/Fn/Kf1/{Tables,Blocks*,BlocksLoop,Rounds}.lean` |
| `MlDsaOpt65/Fn/Csum/gen_blocks.py 87` | `MlDsaOpt87/Fn/Csum/Blocks.lean` |
| `MlDsaOpt65/Fn/Ginit/gen_lanes.py 87` (stdout) | `MlDsaOpt87/Fn/Ginit/Lanes.lean` |
| `proofgen_artifact_glam.py MlDsaOpt/NN/glam/opt.hex MlDsaOptGlamNN MlDsaOptGlamNN glamNN M` (M = 2616, 3384, 2897) | `MlDsaOptGlamNN/{Bytecode,Artifact,Infra,Infra/*}.lean`, `listing.tsv` |
| `MlDsaOptGlam44/Fn/Kf4/gen_kf4.py NN`, `MlDsaOptGlam44/Fn/Kf1/gen_kf1.py NN` (44, 65, 87) | `MlDsaOptGlamNN/Fn/{Kf4,Kf1}/*.lean` (`Model`, `Algebra` for 44 only) |
| `MlDsaOptGlam44/port.py` (`proofgen_port.py --glam 44` and its recorded adjustments) | the ported files of `MlDsaOptGlam44/` |
| `MlDsaOptGlam44/Fn/Blk/gen.py` | `MlDsaOptGlam44/Fn/Blk/{Iters,Proof}.lean` |
| `MlDsaOptGlam44/Fn/Ntt/gen_nttg.py` | `MlDsaOptGlam44/Fn/Ntt/{FwdA,FwdB,Inv1,Inv2,Zeta}.lean` |
| `MlDsaOptGlam44/Fn/Ball/gen_blocks.py` | `MlDsaOptGlam44/Fn/Ball/Blocks.lean` |
| `proofgen_port.py` with the `--sub`/`--path` arguments in each file's `Ported from` header | 76 of the 105 ported files of `MlDsaOpt65/87` |

Not reproducible: the other 29 ported files (28 carry hand adjustments
marked `-- port:`; `MlDsaOpt87/Fn/TBuild/Blocks.lean` says it was
"generalised as the 65 file"); `docs/reference.listing` (no generator in the tree); the v2-era proof
generators, which crash on the v3 listing or emit v2 constants (their files were
since relocated by `proofgen_port.py --reloc` or edited): `MlDsaOpt44/Fn/Kf4/gen_kf4.py`,
`MlDsaOpt44/Fn/Ntt/gen_ntt.py`, `MlDsaOpt44/Fn/Group/gen_p3.py` (also emits only
part of its file), `MlDsaOpt44/Main/Wp11Gen/gen_{init,tbl,rho,mu,muproof,fin}.py`,
`MlDsaOpt65/Main/S1/gen_s1.py`, `MlDsaOpt65/Fn/Csum/gen_blocks.py 65`,
`MlDsaOpt65/Fn/Ginit/gen_lanes.py 65`;
`vectors/` and `foundry/fixtures/` (random keys, the ACVP file and external
oracles are not in the tree).

## Trust rules (maintaining-lean-projects, verification-tooling.md)

1. *Key a cached verdict by everything that decides it.* Snapshot cache key:
   git tree (sources, options, toolchain and manifest files) + gate hash
   (code and policy, taken once at start); the snapshot also records the
   dependency checkouts and the Lean githash, and a check compares them.
   Replay cache key: the replayer's code, toolchain, Lean githash, dependency
   pins, the module's `.olean` bytes and, recursively, those of its project
   imports. `--clean` and `--no-cache` bypass both caches.
2. *One entry point.* `check` and `snapshot` both go through `snapshot()`;
   `--skip-generators` snapshots are never cached and always fail a check.
3. *Decided by Lean.* Axioms come from Lean's `CollectAxioms.collect`;
   admission is decided in `gate_extract` (`X`/`D`/`N` lines), Python only
   reports them. Kernel
   checking is the kernel's (`Environment.replay`). No source text is grepped.
4. *Everything downstream.* Every module built in the worktree is recorded
   and replayed, including both `lean_exe` roots (extracted separately, keys
   prefixed `Tool:` / `MlDsaTool:`); Lean files outside the libraries must compile; `.lean` files in
   library directories that no root imports are listed.
5. *Policy travels explicitly.* The allowlist is passed to `gate_extract` on
   its command line; `LEAN_PATH`, `LEAN_OPTS` and similar are cleared before
   any Lean process starts.
6. *Untrusted input never widens the policy.* The policy is in `gate.py`, the
   extractor is built from the gate's own copy (fresh, per run), HEAD's
   `scripts/gate/` is never executed or elaborated, and the running gate must
   be BASE's (for a snapshot BASE: the gate of the tree it records); a HEAD
   that edits the gate fails. Run the base revision's gate:
   `git worktree add /tmp/base origin/master && python3
   /tmp/base/scripts/gate/gate.py check origin/master <head>`.

Residual trust: building HEAD runs HEAD's code (tactics, `#eval`), and so do
its generators and the bytecode evaluation. Code that deliberately attacks the
gate (rewriting `.lake/gate` caches, the shared `.lake/packages`, or the gate's
temporary extractor binaries while they run) is out of scope; for an
adversarial change, run with `--clean` in a fresh orb.

Digest collisions: SHA-256, 128 bits compared; accidental or crafted
collisions are out of reach.
