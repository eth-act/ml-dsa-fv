# Glamsterdam variant (MlDsaOpt/NN/glam/)

`MlDsaOpt/{44,65,87}/glam/opt.hex` is the **v4** verifier (`docs/opt.md`,
"Round 4 (v4)", including R4-5's fix-up, μ and SampleInBall changes) with
three Glamsterdam-only changes:

1. **Stack-resident, fully unrolled Keccak kernels** (`kf4`, `kf1`;
   `scripts/opt_keccak_glam.py`).
2. **`blk` fully unrolled.** Lanes are read at immediate addresses and
   un-complemented on load.
3. **NTT and inverse NTT merged 4 + 4.** Each pass keeps 16 words on the
   stack (`scripts/opt_ntt_glam.py`).

They need two EIPs scheduled for Glamsterdam (EIP-7773):

* **EIP-8024** (Last Call): `DUPN` 0xe6, `SWAPN` 0xe7, `EXCHANGE` 0xe8, 3 gas
  each, with one immediate byte. `DUPN n` / `SWAPN n` take n in [17, 235]
  through `encode_single(n) = (n + 111) % 256`, and immediates 91..127 halt
  (no 0x5b, no PUSH bytes, so JUMPDEST analysis is unchanged). `EXCHANGE n m`
  is pair-encoded and reaches only n < m ≤ 30 − n. It is not used here.
* **EIP-7954** (Last Call): the code size limit goes from 24,576 to 65,536 B
  (initcode 131,072 B).

No other SFI EIP changes the frame gas of the opcodes used (EIP-7904 is
informational). The numbers below are Osaka costs plus 3 gas per new op, and
the execution specs' Amsterdam fork gives exactly the same gas (section
"Second client").

`gen_opt.py` is not edited. `scripts/gen_glam.py` subclasses its generator,
and the v2, v3 (SHA-256 pinned) and v4 artifacts stay byte-identical.
`gen_glam.py --base v3 --out DIR` rebuilds the first, v3-based prototype
(branch `gas/glamsterdam`, kernels only) byte for byte.

## Result

Frame gas, valid empty-message vector (line 1 of each `calldata.txt`):

| set | v3 | v4 | **glam (v4 base)** | vs v4 | vs v3 |
|---|---:|---:|---:|---:|---:|
| 44 | 2,105,097 | 2,035,355 | **1,843,709** | −191,646 (−9.4%) | −261,388 (−12.4%) |
| 65 | 3,701,979 | 3,552,170 | **3,230,805** | −321,365 (−9.0%) | −471,174 (−12.7%) |
| 87 | 5,424,737 | 5,249,518 | **4,744,646** | −504,872 (−9.6%) | −680,091 (−12.5%) |

Worst case (`opt_worstcase.py --version glam`, \|M\| = 0):

| set | v3 | v4 | **glam** | vs v4 | vs v3 |
|---|---:|---:|---:|---:|---:|
| 44 | 2,864,301 | 2,642,702 | **2,423,040** | −219,662 | −441,261 |
| 65 | 5,073,355 | 4,652,942 | **4,281,360** | −371,582 | −791,995 |
| 87 | 7,954,105 | 7,283,210 | **6,684,558** | −598,652 | −1,269,547 |

Code size (limit 65,536 B under EIP-7954):

| set | v3 | v4 | glam |
|---|---:|---:|---:|
| 44 | 23,091 | 22,470 | **53,895** |
| 65 | 23,422 | 23,140 | **54,565** |
| 87 | 23,982 | 23,934 | **55,359** (10.2 KB left) |

Saving by step, typical 44 / 65 / 87:

| step | 44 | 65 | 87 | code |
|---|---:|---:|---:|---:|
| stack-resident kf4 + kf1, no iota tables | −157,141 | −255,101 | −421,505 | +22.7 KB |
| unrolled `blk` / `blkh` / `blkt` | −14,429 | −26,184 | −43,287 | +5.3 KB |
| NTT / inverse NTT 4 + 4 | −20,076 | −40,080 | −40,080 | +3.3 KB |

Per call:

| routine | before | glam | saving |
|---|---:|---:|---:|
| kf4 | 40,238 | 35,340 | −4,898 (−12.2%) |
| kf1 | 32,571 | 27,705 | −4,866 (−14.9%) |
| `blk` region, 44 (25 calls, 5 of them `blkh`) | 190,336 | 175,907 | −14,429 (−7.6%) |
| `ntt` (v4) | 92,404 | 82,378 | −10,026 (−10.9%) |
| `intt` | 119,593 | 109,615 | −9,978 (−8.3%) |

The kernel savings are identical to those on v3, because v4 does not touch
kf4 or kf1.

**Deployment.** The code is about 2.4× v4's. Under EIP-8037 (CPSB = 1,530
gas per byte of code deposit) that is ≈ 48M more state gas, one time, per
deployment (≈ 83M instead of ≈ 35M). At 44's saving of 192k per
verification, it pays back after ≈ 250 verifications.

## Kernel design (`scripts/opt_keccak_glam.py`)

Representations, lane complementing, chi's operand consumption, theta's
scheduling and kf1's decaying windows (offset −1, re-replication of bits
[192, 256) in rounds 2, 5, …, 23) are exactly those of v3; the generator
reuses `opt_keccak.rot_top`, `CHI` and `rc_table`. The interface is the same:
25 words at KS in, Keccak-f out. No other memory is touched (KB and KZ are
unused).

* **Entry/exit.** 25 MLOADs. The last round MSTOREs its outputs directly,
  then 31 POPs clear the dead slots, D and REP.
* **Theta.** C[x] = 5 DUP/DUPN + 4 XOR. v3 needs 5 × (PUSH + MLOAD).
* **Rho/pi input.** DUPN of the lane: 3 gas instead of 6. The source slot
  becomes dead.
* **Chi output.** SWAPN into one of the plane's dead slots + POP: 5 gas
  instead of PUSH + MSTORE (6). The plane's last output instead swaps with
  the next plane's first input, which then arrives on top (3 gas for a store
  and a load; 4 per round).
* **Layout.** The lanes end up in a different stack permutation after every
  round. `opt_asm.Stack(deep=True)` tracks the layout by name and emits DUPN /
  SWAPN past depth 16, so no code restores a fixed layout. Full unrolling
  makes that free and turns iota into a PUSH immediate.
* **Stack use.** At most ~40 items above the caller's: 25 lanes, D, B,
  temporaries and REP.

kf4 costs ≈ 1,457 gas per round instead of 1,677: (35,340 − 371 entry/exit)
/ 24. By line item, v3 → glam:

* theta lane reads: 150 → 75;
* rho/pi lane reads: 150 → 63;
* stores: 150 → 117;
* iota: ~15 → 6;
* no loop overhead.

Rotations (609), D and chi are unchanged.

## `blk` unrolled (`gen_glam.GlamGen.gen_blk`)

The same entries and outputs as v4: `blk` / `blkh` [ret, abp, flp] for
lanes 0..20 / 0..11, and `blkt` [ret] for lanes 12..20 of the last block.
The changes:

* **No KS flips.** v4 flips the six complemented rate lanes in KS before
  and after (12 MLOAD + 12 MSTORE). Here a NOT on the loaded word does it.
* **Immediate lane addresses.** Lanes are read with PUSH addr, MLOAD.
* **No loop.** There are no pointer increments or loop tests. `blkh` exits
  through one JUMPI after iteration 3, and `blkt` enters at iteration 4.

This replaces "keep the Keccak state on the stack across `kf4` → `blk` /
`trabs`". The 15 KB kf4 is one shared subroutine, so a stack hand-off would
need a fixed lane layout at its entry and exit. The unrolled kernel's
layout changes every round, so the fix-up would cost swaps. `blkt` (lazy
tail) and the sixth squeeze also need the state in KS. Taking the lanes from
memory at immediate addresses keeps all of that and recovers most of the
saving: about 580 gas per call (estimate for a true hand-off ≈ 650).

## NTT 4 + 4 (`scripts/opt_ntt_glam.py`)

v4 merges the 8 layers 3 + 3 + 2 with 8 words on the stack. Here each pass
holds 16 words, reached with DUPN/SWAPN, so the array is read and written
twice instead of three times:

* **Forward pass A.** Layers 1–4 on words j + 16 i, with Shoup
  multiplication by immediate zetas. Layer 4 is now Shoup too; it was a
  Montgomery table load in v4.
* **Forward pass B.** Layers 5–8 on blocks of 16 consecutive words, with the
  block's 15 Montgomery zetas loaded once onto the stack. v4 loads a zeta per
  butterfly.
* **Inverse.** The mirror image: pass 1 (len 1..8, accumulator reduction at
  load) walks the table backwards; pass 2 (len 16..128) uses immediate zetas
  and keeps the scaling folded into the last layer.
* **Table.** 16 blocks × 15 words, replacing v4's 56 + 192 words, in the same
  TBL region.

Bounds: v4's forward bias argument holds with Shoup on layers 1–4, because
Shoup's u < q (1 + b / 2^32) + 1 is below the Montgomery bound;
`opt_selftest_glam.py` checks it per layer. The inverse runs the same
per-layer operations and constant (C = cgs(8)); only the pass boundaries
move. A single pass is impossible: 256 words exceed DUPN's reach of 235.

### Remaining headroom (not done)

* Chaining every chi output into the next input slot, not only the plane's
  last one, breaks chi's in-place consumption: B2 and B3 must sit right below
  the partial result. A scheduler search might save ≤ 2 gas per lane
  (≤ 1.1k per kf4 call).
* `trabs`, `cext` and `ginit` could take lanes at immediate addresses like
  `blk`, but they run 11 / 16 / 20 times (44 / 65 / 87) against 25 / 50 / 75
  for `blk`, and v4's `trabs` is already a straight 7-stage network.
* Pre-expanded zeta or c tables in code (CODECOPY) are now affordable in
  size, but CODECOPY is still outside the stepper's set.

## What the proof side would need (not done)

1. **evm-semantics.** The dependency (`EvmSemantics/EVM/Operation.lean`)
   already has `DupN` / `SwapN` / `Exchange` operations, step functions and
   `argBytes = 1`, but:
   * `isAvailable` is `false` on every fork, so 0xe6–0xe8 halt with
     `InvalidInstruction`. A Glamsterdam/Amsterdam fork needs to enable them.
   * The modelled immediate is the old draft: raw n (`stack[n+1]`) and
     EXCHANGE as two nibbles. EIP-8024's final encoding has to be
     implemented and its step lemmas re-proved: `decode_single(x) = (x + 145)
     % 256`, `decode_pair`, and an exceptional halt on immediates 91–127
     (81–127 for EXCHANGE).
   * The 64 KiB code limit only matters for deployment, not for frame
     proofs.
2. **EvmProof/Stepper.lean.**
   * `runInstr` cases for DUPN and SWAPN, mirroring Dup / Swap with an
     arbitrary index.
   * Matching `GasStep` rules (3 gas) and decoder facts for 2-byte
     instructions in `Decodes` and the instruction-boundary certificates
     (`listing.tsv` generators), so that the pc advances by 2.
   * About 100 lines, following the Dup/Swap cases.
3. **Kernel proofs.**
   * v3 proves one 2-round loop body (`Fn/Kf4/Blocks1–2`, ~77 s elaboration
     for 44) plus `RoundMem` / `Slot` / `Lane` lemmas, and kf1 likewise with
     3 rounds and the `Win` window lemmas.
   * The glam kernels are 24 distinct straight-line rounds: the stack
     permutation and the DUPN/SWAPN immediates differ per round. That is 12×
     the symbolic-execution blocks, about 15 min of elaboration per kernel
     per set, or ~1.5 h for 3 sets × 2 kernels. Each block also carries a
     30–40-element symbolic stack instead of memory.
   * The round algebra (theta / rho / pi / chi on 4 interleaved slots,
     lane complementing, decay windows) is unchanged and reusable. A new
     "RoundStack" lemma would map the per-round layout permutation, emitted
     by the generator, to the lane indices of the existing round model.
   * Iota becomes an immediate, so the RC-table lemmas (`Kf1/Tables`) drop
     out.
   * `memWords` is unchanged. Callers' contracts are unchanged (same KS in
     and out); KB / KZ are no longer clobbered, a weaker postcondition that
     callers do not depend on.
   * Estimated effort: the Stepper and dependency changes are small. The
     kernel re-proof is about the size of the original kf4 + kf1 proofs, but
     mostly generated (extend `gen_kf4.py` / `gen_kf1.py` to emit 24 round
     blocks with layout maps).
4. **`blk` and NTT.**
   * `blk`: the v4 proof's loop invariant becomes 7 straight-line iteration
     blocks, plus the h-flag exit and the `blkt` entry. The bit-permutation
     lemmas (unzip, candidate extraction, flag word) are unchanged; the KS
     flips disappear from the pre/postcondition, since KS is now read-only.
   * NTT: new block structure (2 passes of 32 butterflies on 16 stack words
     instead of 3 passes of 12 / 12 / 4) and a new table-layout lemma. The
     per-layer bound argument and the butterfly lemmas (Montgomery, Shoup,
     GS) carry over unchanged.

## Second client: execution specs (EELS), Amsterdam

`scripts/opt_eels.py` runs a bytecode frame on the execution specs'
`forks/amsterdam` opcode implementations, gas and memory accounting
(ethereum/execution-specs master at `fd92984`, 2026-11-01). That fork
implements EIP-8024 with the final encoding and EIP-7954. The script uses
the interpreter loop of `process_call` without the transaction wrapper, so
the result is frame gas, the same quantity as `opt_evm.py`.

| bytecode | rows | EELS vs `opt_evm.py` (gas and output) |
|---|---:|---|
| glam 44 | all 47 vectors | identical |
| glam 65 | all 57 vectors | identical |
| glam 87 | all 57 vectors | identical |
| v3-based glam 44 (`gas/glamsterdam`), v4 44 and 87 (controls) | line 1 | identical (1,947,956; 2,042,346; 5,271,542) |
| after R4-5 (`gas/final`): glam 44 / 65 / 87 | all 47 / 57 / 57 vectors | identical |
| after R4-5: v4 44 and 87 (controls) | line 1 | identical (2,035,355; 5,249,518) |

revm/Foundry is not installed in this environment, and no local Rust
toolchain was available to build a revm with EIP-8024.

## Validation

On the v4-based artifacts (re-run after R4-5, `gas/final`):

| check | result |
|---|---|
| EIP-8024 test cases (assembly + execution) on `opt_evm.py` | all pass; 0xe6 still undefined under `fork="osaka"` |
| stack-resident kernels vs reference Keccak-f (random + all-ones states, complemented lanes), no memory written outside KS | pass |
| v2, v3 (SHA-256 pins) and v4 artifacts | byte-identical |
| NTT 4 + 4 forward bias bounds (Shoup on layers 1–4) | hold for 44 / 65 / 87 |
| all vectors on glam bytecode (44: 47, 65: 57, 87: 57), `opt_evm` and EELS | 0 mismatches |
| forced sixth squeeze (debug build; exercises `blkt` and the sixth `blk`) | 19 / 21 / 36 vectors with sixth-block checks, all correct |
| μ block boundaries (`opt_selftest.test_mu_lengths`: \|M\| = 69 … 1,500, valid and one-bit-flipped message) | 13 lengths per set, all correct |
| differential fuzz before R4-5 (`OPT_VERSION=glam opt_fuzz.py`, seeds 447 / 657 / 877, messages up to 1,200 B) | 300 cases per set, 0 failures; accepted 54 / 47 / 58. Mean / max gas of accepted cases: 1,903,756 / 2,136,405 (44), 3,292,488 / 3,566,153 (65), 4,810,952 / 4,962,707 (87) |
| differential fuzz after R4-5 (`opt_fuzz.py --version v3,v4,glam`, seeds 341 / 141 / 241, same cases on all three) | 400 cases per set, 0 failures; accepted 65 / 77 / 73. Mean / max gas of accepted cases: 1,859,153 / 1,925,370 (44), 3,237,540 / 3,297,312 (65), 4,812,150 / 5,017,182 (87) |

## Reproducing

```sh
export TMPDIR=$PWD/.lake/tmp
python3 scripts/gen_glam.py                       # MlDsaOpt/{44,65,87}/glam/ (v4 base)
python3 scripts/gen_glam.py --base v3 --out DIR   # the v3-based prototype (gas/glamsterdam)
python3 scripts/opt_selftest_glam.py              # EIP-8024 cases, kernels, NTT bounds, v2/v3/v4 unchanged, vectors, forced 6th squeeze
python3 scripts/opt_worstcase.py --version glam   # typical and worst case per set
OPT_VERSION=glam python3 scripts/opt_fuzz.py 44 300 447
/tmp/eelsenv/bin/python scripts/opt_eels.py MlDsaOpt/44/glam/opt.hex vectors/calldata.txt   # second client
```
