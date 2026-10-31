# Production-EVM cross-check and differential fuzzing

The Lean development proves that the frozen bytecode
`MlDsa44/Reference/reference.hex` (5289 bytes), executed in the pinned Lean EVM
semantics from `MlDsa44.initialState`, returns the word `1` iff FIPS 204
`ML-DSA.Verify(pk, M, σ, ctx = "")` accepts the EIP-8355 calldata
`pk (1312) ‖ σ (2420) ‖ M`, and `0` otherwise (including calldata shorter than
3732 bytes), within `MlDsa44.Proofs.Gas.schedule (calldata size)` gas.

Nothing here is part of the proof. This directory falsification-tests the
things the proof cannot see from the inside:

1. **Same bytes.** The runtime code executed by revm is the proved artifact.
2. **Same behaviour on a production EVM.** revm (inside Foundry) returns the
   same word as the Lean specification on every case.
3. **Same gas.** revm's frame gas equals the Lean semantics' frame gas exactly,
   case by case — a check on the pinned semantics' gas model, on which the
   schedule theorem rests.
4. **Within the proved schedule.** revm gas never exceeds `Gas.schedule`.
5. **Specification vs. independent implementations.** The Lean specification
   `MlDsa44.accepts` agrees with RustCrypto `ml-dsa`, Go's FIPS 140-3 `mldsa`
   and dilithium-py on every generated case.

## Running

Prerequisites, from the repository root:

```sh
export TMPDIR=$PWD/.lake/tmp
lake build mldsa44tool            # Lean spec oracle (spec-file) and Lean EVM (run-file)
foundry/oracles/build.sh          # RustCrypto and Go oracles -> foundry/oracles/bin
```

Python 3 with dilithium-py on `.ref/pylib` (the scripts add it to `sys.path`).
Fixtures are checked in; regenerate them with

```sh
python3 scripts/xcheck_fixtures.py                       # fixtures/{vectors,control,schedule}.txt  (~1 min)
python3 scripts/fuzz_corpus.py --scale 2 --seed 8355     # fixtures/fuzz/*.txt  (~37 min, 8 Lean jobs)
```

Then

```sh
cd foundry
forge test -vv                                  # everything, ~1 min + ~1–4 min for 256 ffi fuzz runs
forge test --no-match-contract DifferentialFuzz # no ffi: ~1 min
forge test --match-contract DifferentialFuzz --fuzz-runs 3000 --fuzz-seed 0x5000
XCHECK_LEAN_GAS=1 forge test --match-contract DifferentialFuzz --fuzz-runs 75   # + exact Lean gas per run (~3 s/run)
XCHECK_FUZZ_LOG=cache/stats.txt forge test --match-contract DifferentialFuzz    # per-run log
```

The fuzz seed is fixed in `foundry.toml` (`0x8212`) so plain `forge test` is
reproducible; pass `--fuzz-seed` to explore.

## Measurement

`Tool.lean run`/`run-file` report `start.gasAvailable - final.gasAvailable` for
a fresh top-level Osaka frame at `pc = 0` with the calldata: the frame's own
consumption including memory expansion, with no intrinsic transaction cost, no
calldata byte cost and no charge for entering the frame.

[`src/GasProbe.sol`](src/GasProbe.sol) (taken unchanged from the
eip8200-challenges/powdr cross-checks) measures exactly that in revm: the same
`STATICCALL` instruction runs twice in a two-iteration loop, first against a
one-byte `STOP` contract (a frame that consumes zero gas) and then against the
verifier; both targets are warmed with `EXTCODESIZE` beforehand and the
argument buffer is pre-expanded, so the difference of the two `gas()` deltas is
the callee frame's consumption and nothing else. Controls
([`test/GasProbe.t.sol`](test/GasProbe.t.sol)): the probe reproduces the
`0x02`/`0x03` precompile schedules `60 + 12⌈n/32⌉` and `600 + 120⌈n/32⌉`
exactly for sizes 0 … 7464, reports 0 for a `STOP` frame, and is independent
of caller state. The verifier is run at `0x8212` (`MlDsa44.deployAddress`)
under `evm_version = "osaka"` (the fork `initialState` fixes).

The verifier only uses pure opcodes (no storage, balance, environment or
calls), so `STATICCALL` vs `CALL`, account state, and call depth cannot
matter; `Artifact.t.sol` checks the first two anyway.

## Artifact provenance

[`src/LeanArtifact.sol`](src/LeanArtifact.sol) loads `reference.hex` and
requires it to equal, byte for byte, the concatenation of the
`referenceChunk<N>` literals of `MlDsa44/Reference/Bytes.lean` in the order the
`referenceBytes` body concatenates them, that `Bytecode.lean` still defines
`referenceBytecode := referenceBytes` (the constant the theorems are about),
and that `referenceBytes_size` proves the loaded length. Every test etches
those bytes. [`test/Artifact.t.sol`](test/Artifact.t.sol) additionally asserts

* `keccak256(runtime code) = EXTCODEHASH = keccak256(reference.hex) =
  0x44c18b2d…476d44` (pinned), size 5289;
* a real `CREATE` of `initcode ‖ runtime` (no cheatcode) deploys identical
  runtime code (so EIP-170/EIP-3541 do not interfere) that returns the same
  word for the same gas;
* gas and output are unchanged with dirty storage/balance, and `CALL` (with
  value) and `STATICCALL` agree.

## Oracles

| oracle | implementation | how |
|---|---|---|
| Lean spec | `MlDsa44.accepts` (`MlDsa44/Spec.lean` over `MlDsa44/Spec/Fips204.lean`) — what the bytecode is proved to implement | `mldsa44tool spec-file FILE` (new subcommand) |
| RustCrypto | `ml-dsa` 0.1.1, `VerifyingKey::verify_with_context(M, "", σ)` | [`oracles/rust`](oracles/rust) |
| Go | Go standard library FIPS 140-3 module `crypto/internal/fips140/mldsa` `Verify(pk, M, σ, "")` (go1.26-devel) | [`oracles/go`](oracles/go), compiled as std command via `go build -overlay` |
| dilithium-py | 1.4.0, `ML_DSA_44.verify(pk, M, σ)` | in-process |
| Lean EVM | the frozen bytecode in the pinned Lean semantics | `mldsa44tool run-file HEX FILE` (new subcommand): gas, halt, returndata |

The expected verdict of every fixture case is the Lean spec's; the fixture
scripts fail unless Rust and Go agree with it, dilithium-py agrees with it
except on a well-formed hint with a repeated index inside a row (its known
divergence: FIPS 204 Algorithm 21 requires strictly increasing indices,
dilithium-py only rejects decreasing ones), the generator's own expectation
(valid signatures, truncations, …) agrees with it, the Lean-semantics
execution returns that word, and the Lean gas is ≤ `Gas.schedule`. revm is
then compared in Foundry.

`Gas.schedule` values come from evaluating the Lean definition itself
([`scripts/xcheck_schedule.lean`](../scripts/xcheck_schedule.lean), `lake env
lean --run`). The closed form in [`src/Schedule.sol`](src/Schedule.sol) and
`scripts/xcheck_common.py` (README.md's formula) agrees with Lean on every size
0 … 8231 and every 997th size up to 3732 + 200 000 (8429 sizes); 232 of them
are pinned in `fixtures/schedule.txt` and re-checked in Solidity.

## Fixtures and tests

| test | content |
|---|---|
| `VectorsTest.test_vectors_and_acvp` | all 47 rows of `vectors/calldata.txt` + the 1 ACVP sigVer row usable as EIP-8355 calldata (M′ = `00 00 ‖ M`); the other 29 ACVP rows carry a non-empty context or are internal-interface messages not starting with `00 00` |
| `VectorsTest.test_harness_detects_mismatches` | negative control: a line with Lean gas + 1 and one with a flipped verdict are flagged |
| `FuzzCorpusTest.test_corpus_*` | `fixtures/fuzz/<category>.txt`, one test per category |
| `DifferentialFuzzTest.testFuzz_*` | forge-native mutation fuzzing with live oracles through `vm.ffi` → [`scripts/xcheck_oracle.py`](../scripts/xcheck_oracle.py) |

Each replayed line asserts: revm call succeeds and returns exactly
`abi.encode(expected)`; revm frame gas `==` Lean-semantics gas; revm gas `≤`
`Gas.schedule(size)`; fixture schedule `==` `Schedule.gas(size)`. A failing line
is appended with full calldata to `vectors/fuzz/revm_failures.txt` (fuzz runs:
`vectors/fuzz/forge_fuzz_failures.txt`) before the assertion fails.

### Corpus categories (`scripts/fuzz_corpus.py --scale 2 --seed 8355`)

| category | cases | accept | content |
|---|---:|---:|---|
| valid | 548 | 548 | fresh key per case; message lengths 0, 1, 2, 31–33, 63–65, 69–71, 135–137, 205–207, 341–343, 477–479, 1000, 1023–1025, 2048, 3000, 4095, 4096 (four times each), 300 uniform in 0…4096, 120 in 0…299; random / all-zero / all-0xff messages; hedged and deterministic signing |
| z-forced | 64 | 32 | signatures searched (custom signing loop with chosen mask y) so one z coefficient is exactly ±(γ1−β−1) = ±130993 (must accept) or ±(γ1−β) = ±130994 (must reject, although the signature verifies with the norm check disabled — asserted in the generator) at coefficients 0–3, 255 and random |
| flip-pk | 300 | 0 | one bit flipped in ρ or t1 |
| flip-ctilde | 200 | 0 | one bit flipped in c̃ |
| flip-z | 300 | 0 | one bit flipped in z |
| flip-hint | 400 | 0 | one bit flipped in the 84 hint bytes (indices, padding, counts) |
| flip-msg | 200 | 0 | one bit flipped in M |
| hint-struct | 600 | 0 | 40 each: adjacent indices swapped (same set, unsorted); index duplicated by insertion (same set, repeated index); index duplicated by replacement; non-zero padding; last count = ω+1; a count in ω+1…255; decreasing counts; row boundary moved ±1; index changed (still sorted); hint removed; hint added; all-zero hint; last count = ω (padding becomes indices); index 255 appended; counts = 255 |
| z-raw | 300 | 0 | one z coefficient (index 0–3, 255, 256, 511, 1023 or random) has its 18-bit encoding γ1−z set to 0, 1, 77, 78, 79, 80, γ1−1, γ1, γ1+1, 2γ1−80 … 2γ1−77, 2γ1−1 or random |
| length | 451 | 0 | truncated to 0, 1, 31–33, 1311–1313, 3700, 3730, 3731 and 240 random sizes < 3732; message truncated by 1 … len(M) bytes; message extended by 1…299 random or zero bytes |
| other | 228 | 0 | signature under another key; signature of another message; random signature; random key; random calldata; all-zero / all-0xff calldata, signature, key |
| **total** | **3591** | **580** | |

## Results

Toolchain: forge 1.5.1-stable (b0a9dd9, revm inside), solc 0.8.35, Lean
toolchain of the repository, ml-dsa 0.1.1, go1.26-devel_7251c9e0f0,
dilithium-py 1.4.0.

**Exact gas agreement: 3639 / 3639 fixture cases** (48 KAT/ACVP + 3591 corpus),
revm frame gas equal to the Lean-semantics gas on every case, plus every
ffi fuzz run executed with `XCHECK_LEAN_GAS=1` (below). Suite totals:

| fixture | cases | Lean gas total | revm gas total | delta |
|---|---:|---:|---:|---:|
| vectors (KAT + ACVP) | 48 | 600,122,596 | 600,122,596 | 0 |
| fuzz/valid | 548 | 7,413,068,878 | 7,413,068,878 | 0 |
| fuzz/z-forced | 64 | 831,798,133 | 831,798,133 | 0 |
| fuzz/flip-pk | 300 | 4,052,092,651 | 4,052,092,651 | 0 |
| fuzz/flip-ctilde | 200 | 2,702,088,039 | 2,702,088,039 | 0 |
| fuzz/flip-z | 300 | 4,056,991,910 | 4,056,991,910 | 0 |
| fuzz/flip-hint | 400 | 5,383,323,476 | 5,383,323,476 | 0 |
| fuzz/flip-msg | 200 | 2,706,748,663 | 2,706,748,663 | 0 |
| fuzz/hint-struct | 600 | 8,098,801,424 | 8,098,801,424 | 0 |
| fuzz/z-raw | 300 | 4,041,809,876 | 4,041,809,876 | 0 |
| fuzz/length | 451 | 2,686,145,732 | 2,686,145,732 | 0 |
| fuzz/other | 228 | 3,049,547,512 | 3,049,547,512 | 0 |

**Outputs:** revm returned exactly the Lean spec's word on every case. No
disagreement between the Lean spec, RustCrypto and Go on any of the 3639
fixture cases or any ffi fuzz run. dilithium-py disagreed only on the 40
`dup-insert` hint cases (it accepts; FIPS, Lean, Rust, Go, the EVM code reject),
saved as reproducers in `vectors/fuzz/dpy_known_divergence.txt`. There is no
`vectors/fuzz/oracle_disagreements.txt`, `revm_failures.txt` or
`forge_fuzz_failures.txt`: nothing to reproduce.

**Gas vs schedule:** never exceeded.

* Calldata < 3732 bytes (253 fixture cases): gas is exactly 267 = `Gas.short`,
  zero slack — the schedule is tight there.
* Calldata ≥ 3732 bytes (3386 cases): slack between 205,200 (a forced-z
  signature with z = γ1−β, size 3733: 12,955,879 of 13,161,079, gas/schedule = 98.44 %)
  and 216,486 (all-zero hint); the largest gas/schedule ratio is 98.64 %.
  Max observed gas 15,032,336 (the ACVP row, |M| = 4767) against a schedule of
  15,239,816. At |M| = 0 the 79 cases span 12,945,498 … 12,954,592 against
  13,161,063. The slack is essentially independent of the message length
  (~205–216 k): it is the worst-case charge for the data-dependent branches
  (rejection sampling, SampleInBall, hint decoding, UseHint), as README.md
  states.

**Forge-native ffi fuzzing** (`DifferentialFuzzTest`, all passing, no
`forge_fuzz_failures.txt` written). Runs per mutation kind:

| campaign | runs | none | flip any | flip hint | hint byte := | z boundary | truncate | extend | swap hint bytes | flip pk/M | count := | short | accepted |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `--fuzz-runs 3000 --fuzz-seed 0x5000` | 3000 | 72 | 441 | 368 | 387 | 376 | 277 | 330 | 273 | 256 | 220 | 260 | 90 |
| `XCHECK_LEAN_GAS=1`, 4 × 75 runs, seeds `0x1ea1`–`0x1ea4` | 300 | 9 | 38 | 32 | 36 | 45 | 31 | 24 | 32 | 26 | 27 | 28 | 12 |

In all 3300 runs revm = Lean spec = RustCrypto = Go = dilithium-py (no
repeated-index case was hit), gas ≤ schedule (max 14,855,957, min slack
205,580 over full-length inputs; 267 exactly for every short input), and in
the 300 `XCHECK_LEAN_GAS` runs revm gas equalled the Lean-semantics gas on
every run. "Accepted" counts unmodified bases plus mutations that can leave
the bytes unchanged (a byte set to its own value, two equal bytes swapped);
all oracles agreed on each of them. An earlier 5000-run campaign
(`--fuzz-seed 0x5000`, before the corpus bases were added and before the
mutation-kind rebalancing) also passed with 0 disagreements.

**Runtimes** (shared, heavily loaded 32-core machine): `xcheck_fixtures.py`
≈ 45 s; `fuzz_corpus.py --scale 2` 2201 s (31 s generation, ~2150 s Lean-EVM
execution of 3576 distinct calldata at 8 jobs ≈ 4.8 s each, oracles a few
seconds); `forge test` without ffi ≈ 50 s for 45.6 G gas of revm execution
(parallel across categories); 256 ffi fuzz runs 1–4 min depending on load;
the 3000-run campaign 1996 s; each 75-run `XCHECK_LEAN_GAS` campaign ≈ 800 s
(four in parallel).

### Observations

* The verifier runs the whole verification path even for structurally invalid
  signatures (hint count > ω, z out of range): gas for those is ≈ 12.95 M,
  like a valid one. This is consistent with a data-independent control flow
  and with the schedule, not a defect.
* The bound at short calldata is exact (267) and the ACVP/KAT/fuzz maximum
  stays ≥ 205 k below the schedule; nothing approaches the bound.
* `Gas.schedule` evaluation needs the proof oleans; `xcheck_common.lean_schedule`
  caches results and retries when a concurrent `lake build` has removed an
  olean.

## Layout

| path | contents |
|---|---|
| `src/GasProbe.sol` | exact frame-gas measurement (from the eip8200-challenges cross-check) |
| `src/LeanArtifact.sol` | artifact loading and provenance (`reference.hex` = `Bytes.lean` literal) |
| `src/Schedule.sol` | closed-form `Gas.schedule` |
| `test/XCheckBase.sol` | etching, fixture replay in fresh call frames, reporting |
| `test/*.t.sol` | the tests above |
| `fixtures/` | generated: `vectors.txt`, `control.txt`, `schedule.txt`, `fuzz/*.txt` |
| `oracles/` | RustCrypto and Go verdict oracles, `build.sh` |
| `../scripts/xcheck_common.py` | oracles, Lean EVM runner (cached by content hash in `cache/xcheck/`), fixture writer |
| `../scripts/xcheck_fixtures.py`, `../scripts/fuzz_corpus.py`, `../scripts/xcheck_oracle.py`, `../scripts/xcheck_schedule.lean` | fixture builders, ffi oracle, Lean schedule evaluator |
