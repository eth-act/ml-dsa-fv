# Glamsterdam variant (MlDsaOpt/NN/glam/)

`MlDsaOpt/{44,65,87}/glam/opt.hex` is the **v4** verifier (`docs/opt.md`,
"Round 4 (v4)", including R4-5's fix-up, μ and SampleInBall changes and
R4-6's arithmetic) with three Glamsterdam-only changes:

1. **Stack-resident, fully unrolled Keccak kernels** (`kf4`, `kf1`;
   `scripts/opt_keccak_glam.py`).
2. **`blk` fully unrolled.** Lanes are read at immediate addresses and
   un-complemented on load.
3. **NTT and inverse NTT merged 4 + 4.** Each pass keeps 16 words on the
   stack (`scripts/opt_ntt_glam.py`).
4. **Arithmetic round** (branch `gas/arith`, section "Arithmetic"): UseHint
   fused into the inverse NTT for all three sets, all τ `csum` bases on the
   stack, `dz`'s gather loop unrolled, plus v4's R4-6.

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
`gen_glam.py --base v3 --out DIR` builds the first, v3-based prototype
(branch `gas/glamsterdam`, kernels only), now with the current kernels; it
matched that branch byte for byte until the plane schedule of
`gas/keccak-glam`.

## Result

Frame gas, valid empty-message vector (line 1 of each `calldata.txt`):

| set | v3 | v4 | **glam (v4 base)** | vs v4 | vs v3 |
|---|---:|---:|---:|---:|---:|
| 44 | 2,105,097 | 1,929,359 | **1,686,116** | −243,243 (−12.6%) | −418,981 (−19.9%) |
| 65 | 3,701,979 | 3,509,486 | **2,943,671** | −565,815 (−16.1%) | −758,308 (−20.5%) |
| 87 | 5,424,737 | 5,227,912 | **4,523,186** | −704,726 (−13.5%) | −901,551 (−16.6%) |

Worst case (`opt_worstcase.py --version glam`, \|M\| = 0):

| set | v3 | v4 | **glam** | vs v4 | vs v3 |
|---|---:|---:|---:|---:|---:|
| 44 | 2,864,301 | 2,580,502 | **2,293,653** | −286,849 | −570,648 |
| 65 | 5,073,355 | 4,610,258 | **3,981,579** | −628,679 | −1,091,776 |
| 87 | 7,954,105 | 7,261,604 | **6,432,872** | −828,732 | −1,521,233 |

Code size (limit 65,536 B under EIP-7954):

| set | v3 | v4 | glam |
|---|---:|---:|---:|
| 44 | 23,091 | 24,050 | **57,610** |
| 65 | 23,422 | 24,049 | **56,565** |
| 87 | 23,982 | 23,798 | **56,493** (8.8 KB left) |

44 and 65 include R4-7 (`docs/opt.md`): 44 makes 23 kf4 calls instead of
25 for |M| < 342 and switches to the 25-call schedule from there on; 65
makes 42 instead of 45 (glam only, v4 has no code room). With the searched
kernels and R4-6's schedules glam was 1,754,841 / 3,073,845 (44 / 65);
`gas/candidate` d49038a had 44 at 23 calls without the switch (1,687,047,
worst 2,294,608).

Gas by message length, glam (dilithium-py, fixed key; Δ against
`d49038a`, and for 44 against R4-6's schedule with the same kernels,
`OPT_V4_PACK=0`):

| \|M\| | 44 | Δ d49038a | Δ 25 calls | 65 | Δ d49038a |
|---:|---:|---:|---:|---:|---:|
| 0 | 1,681,866 | −931 | −68,900 | 2,911,466 | −126,820 |
| 70 | 1,715,567 | −874 | −39,407 | 2,943,595 | −97,383 |
| 206 | 1,741,262 | −871 | −15,003 | 2,971,406 | −73,154 |
| 342 | 1,760,083 | −10,229 | +43 | 2,999,177 | −48,750 |
| 478 | 1,763,222 | −34,636 | +43 | 3,025,968 | −24,171 |
| 614 | 1,792,711 | −30,827 | +100 | 3,052,567 | −28,095 |
| 1000 | 1,847,765 | −30,830 | +100 | 3,107,441 | −28,095 |
| 1500 | 1,956,949 | −30,830 | +100 | 3,216,837 | −28,095 |

Saving by step, typical 44 / 65 / 87:

| step | 44 | 65 | 87 | code |
|---|---:|---:|---:|---:|
| stack-resident kf4 + kf1, no iota tables | −157,141 | −255,101 | −421,505 | +22.7 KB |
| unrolled `blk` / `blkh` / `blkt` | −14,429 | −26,184 | −43,287 | +5.3 KB |
| NTT / inverse NTT 4 + 4 | −20,076 | −40,080 | −40,080 | +3.3 KB |
| arithmetic round (`gas/arith`) | −30,412 | −64,504 | −68,552 | +1.8 KB |
| Keccak plane schedule (`gas/keccak-glam`; 32 / 52 / 86 kernel calls × −1,778) | −56,896 | −92,456 | −152,908 | −0.5 KB |

Per call:

| routine | before | glam | saving |
|---|---:|---:|---:|
| kf4 | 40,238 | 33,562 (35,340 before `gas/keccak-glam`) | −6,676 (−16.6%) |
| kf1 | 32,571 | 25,927 (27,705) | −6,644 (−20.4%) |
| `blk` region, 44 (25 calls, 5 of them `blkh`) | 190,336 | 175,907 | −14,429 (−7.6%) |
| `ntt` (v4) | 92,404 | 82,378 | −10,026 (−10.9%) |
| `intt` | 119,593 | 109,615 | −9,978 (−8.3%) |

The kernel savings are identical to those on v3, because v4 does not touch
kf4 or kf1.

**Deployment.** The code is about 2.4× v4's. Under EIP-8037 (CPSB = 1,530
gas per byte of code deposit) that is ≈ 48M more state gas, one time, per
deployment (≈ 84M instead of ≈ 36M). At 44's saving of 258k per
verification, it pays back after ≈ 190 verifications.

## Kernel design (`scripts/opt_keccak_glam.py`)

Representations, lane complementing, chi's operand consumption, theta's
scheduling and kf1's decaying windows (offset −1, re-replication of bits
[192, 256) in rounds 2, 5, …, 23) are exactly those of v3; the generator
reuses `opt_keccak.rot_top`, `CHI` and `rc_table`. The interface is the same:
25 words at KS in, Keccak-f out. No other memory is touched (KB and KZ are
unused).

* **Entry/exit.** 25 MLOADs. The last round MSTOREs its outputs directly,
  then POPs clear the dead values (one parked D per round, the last round's
  dead lane copies, and REP for kf1): 48 POPs for kf4.
* **Theta.** C[x] = 5 DUP/DUPN + 4 XOR. v3 needs 5 × (PUSH + MLOAD). One
  EXCHANGE at the end orders the D's for the last plane (below).
* **Plane schedule** (branch `gas/keccak-glam`). Every SWAPN parks one value
  and fetches another, so no lane is copied for rho and no slot needs a POP:
  1. the top value (the previous plane's output 4, or a D at the start of
     the round) is parked in the slot of the lane for B1;
  2. B1, B2, B3 are parked in the slots of the lanes for B2, B3, B4 as those
     come up (each lane is XORed with a D copy and rotated in place);
  3. output 2 is parked in the slot of the lane for B0;
  4. outputs 3, 0 and 1 are parked in the slots of B3, B2 and B1, which come
     up for their last, consuming use (B2 ∧ B3 in output 1, B0 ∧ B1 and B4
     in output 4);
  5. output 4 stays on top.

  That is 8 SWAPs and 10 DUPs per plane (v3's chi needs the same 10 DUPs),
  against 4 lane DUPs, 4 SWAPN + POP into dead slots and one chained SWAPN
  before: −11 gas per plane. A shortest-path search over abstract stack
  schedules (cost = DUPs + SWAPs + POPs, one plane, no EXCHANGE) found it and
  shows 54 is the minimum of that model; a two-plane search ran out of memory.
* **Last plane.** Its first four lanes use D2, D3, D4, D0 (the plane is
  processed from B0), and theta leaves exactly those four D's, in that order,
  right below the plane's work area. Each is then consumed by the lane's XOR
  instead of copied: 4 × (DUP + POP) saved per round for one EXCHANGE.
* **Last round.** Outputs are stored, so nothing is parked: one SWAPN, four
  lane DUPs, and the two outputs whose operands meet on top consume them
  (the same search with stored outputs; the plane rotation is chosen per
  row so that no consumed operand needs a NOT below the top).
* **Layout.** The lanes end up in a different stack permutation after every
  round. `opt_asm.Stack(deep=True)` tracks the layout by name and emits DUPN /
  SWAPN past depth 16, so no code restores a fixed layout. Full unrolling
  makes that free and turns iota into a PUSH immediate.
* **Stack use.** About 40 items above the caller's in a round (25 lanes, D,
  B, temporaries, REP) plus one dead D per round: at most ~65.

kf4 costs ≈ 1,388 gas per round, (33,562 − 255 entry/exit) / 24 (1,457 before the plane schedule, 1,677 in
v3). By line item, v3 → glam:

* theta lane reads: 150 → 75;
* rho/pi lane reads and chi stores: 300 → 120 (8 SWAPs per plane);
* D copies: 75 → 63, and 5 POPs → 1;
* iota: ~15 → 6;
* no loop overhead.

Rotations (609) and chi's operations and DUPs are unchanged.

### Lower bound per round (kf4)

Counting only operations no stack schedule can avoid, at 3 gas each:

| part | operations | count |
|---|---|---:|
| theta C | 25 lane DUPs + 20 XOR | 45 |
| theta D | 5 C DUPs + 5 rotations × 7 + 5 XOR | 45 |
| rho | 25 XOR with D + 20 D DUPs (5 uses each, one consumes) + 24 rotations × 7 | 213 |
| chi | 50 AND/OR/XOR + 8 NOT (this complementing; ≥ 5 with any) + 50 B DUPs (3 uses each) | 108 |
| iota | PUSH + XOR | 2 |
| **total** | | **413 = 1,239 gas** |

Before: 1,457 (+17.6%). Now: 1,388 (+12.0%). The rest is stack movement
that a zero-move bound ignores: lanes must reach the top to be consumed and
outputs must leave it, and the one-plane search says 8 SWAPs (120 gas per
round) is the minimum for a plane. With those and theta's 6 SWAPs + 1 EXCHANGE, the
floor of this design is ≈ 1,380: the kernels are within ~0.6% of it. The
7-op rotation (DUP1 PUSH SHL SWAP1 PUSH SHR OR) is minimal without SAR or a
sound MULMOD.

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

## Arithmetic (branch `gas/arith`)

v4's R4-6 (`docs/opt.md`) plus three changes that need DUPN or code space:

* **UseHint fused into the inverse NTT for 87 too.** Pass 2's 16 output
  words go through `uh_word` before they are stored; its wide masks sit on
  the stack for the whole pass (`post_consts`, DUPN instead of PUSH32), so
  the 16 copies add ~1 KB.
* **All τ window bases on the stack in `csum`** (`CSUM_DEEP`): a term is
  DUPN base, DUP pointer, ADD, MLOAD, ADD (15 gas instead of 18).
* **`dz` gather loop unrolled per chunk** (`DZ_UNROLL`): immediate shifts
  and store offsets, no loop test (+0.9 KB).

Per kernel (valid |M| = 0 vector), before → after:

| kernel | 44 | 65 | 87 |
|---|---|---|---|
| `intt` + `usehint` | 162,120 → 145,475 | 308,368 → 275,078 | 308,368 → 275,078 |
| `dz` | 46,156 → 39,578 | 92,312 → 79,156 | 92,312 → 79,156 |
| `csum` | 66,675 → 59,504 | 156,390 → 138,368 | 181,734 → 159,664 |

The forward NTT is unchanged (82,378 per call). Its butterfly is 19
operations (Shoup) or 20 (Montgomery, pass B); `docs/opt.md` R4-6 lists
the alternatives that were ruled out. The rest of its cost is the two
passes' loads and stores (~12k) and pass B's zeta loads (~3k), which only
a fully unrolled kernel (~25 KB) would remove.

### Remaining headroom (not done)

* **Dead outputs in the last round.** A permutation whose output is only
  partly read could skip those chi outputs and the B's only they use:
  * the final kf1 (c̃ check) reads 4 / 6 / 8 lanes: planes 1–4 of round 24
    (most of plane 1 for 87) are dead, ≈ 0.8k once per verification;
  * an ExpandA group's fifth squeeze does not need lanes 21–24 unless the
    sixth squeeze happens (B3, B4 and outputs 21–24 of the last plane,
    ≈ 150 per call: 0.75k / 1.2k / 2.2k for 44 / 65 / 87).

  kf1 and kf4 are shared subroutines, so this needs a second copy of round
  24 (~0.6 KB each) behind a JUMPI on the return address (~22 gas on every
  other call), and the sixth squeeze would have to recompute the fifth
  permutation (+34k worst case per group). Not done.
* **Shared first round across ExpandA groups.** A group's first block
  differs from the other groups' only in lane 4 (column and row bytes), so
  C0..C3, D1, D2, D4 and the B's of the 14 lanes in columns 1, 2, 4 (minus
  lane 4) are common; most lanes are zero or constant, which a dedicated
  first round could exploit even without sharing (≈ 250 per group: no
  MLOAD, no C XOR, B = rot(D)). Sharing adds ≈ 300 per group after the
  first. Together ≈ 2.5k / 4k / 7.5k for 44 / 65 / 87, but only for groups
  whose four slots are all fresh ExpandA seeds (not slots kept for tr, μ or
  c̃), and it needs a separate round-1 entry ending in the shared kernel's
  round-2 layout plus caller changes in the group driver. Not done.
* **D frames** (`gas/keccak-lab`). Reading lanes at memory offsets rotates
  them for free, so column parities can be taken in per-column frames and
  four of theta's five rotations disappear. On the stack, a lane read
  (DUPN) is in its stored frame, all outputs of a plane share the plane's
  B frame (chi mixes the plane's columns), and a column takes one lane from
  every plane, so aligned parities force one global frame: the five
  rotations stay.
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
| after R4-6 (`gas/arith`): glam 44 / 65 / 87 | all 47 / 57 / 57 vectors | identical |

revm/Foundry is not installed in this environment, and no local Rust
toolchain was available to build a revm with EIP-8024.

## Validation

On the v4-based artifacts (re-run after R4-5, `gas/final`, and after R4-6, `gas/arith`):

| check | result |
|---|---|
| EIP-8024 test cases (assembly + execution) on `opt_evm.py` | all pass; 0xe6 still undefined under `fork="osaka"` |
| stack-resident kernels vs reference Keccak-f (random + all-ones states, complemented lanes), no memory written outside KS | pass |
| `gas/keccak-glam` kernels: 88 KATs per kernel vs `opt_ref.keccak_f` (zero, all-ones, 40 random single bits, one bit in each lane at a different bit per slot, 20 random, mixed slots), no memory written outside KS | pass |
| EELS (`opt_eels.py`, execution-specs `fd92984`) vs `opt_evm.py` after `gas/keccak-glam` | all 47 / 57 / 57 vectors: identical gas and output |
| differential fuzz after `gas/keccak-glam` (`OPT_VERSION=glam opt_fuzz.py`, seeds 447 / 657 / 877) | 300 cases per set, 0 failures; accepted 54 / 47 / 58. Mean / max gas of accepted cases: 1,771,461 / 1,901,912 (44), 3,084,265 / 3,208,507 (65), 4,567,328 / 4,643,242 (87) |
| v2, v3 (SHA-256 pins) and v4 artifacts | byte-identical |
| NTT 4 + 4 forward bias bounds (Shoup on layers 1–4) | hold for 44 / 65 / 87 |
| all vectors on glam bytecode (44: 47, 65: 57, 87: 57), `opt_evm` and EELS | 0 mismatches |
| forced sixth squeeze (debug build; exercises `blkt` and the sixth `blk`) | 19 / 21 / 36 vectors with sixth-block checks, all correct |
| μ block boundaries (`opt_selftest.test_mu_lengths`: \|M\| = 69 … 1,500, valid and one-bit-flipped message) | 13 lengths per set, all correct |
| differential fuzz before R4-5 (`OPT_VERSION=glam opt_fuzz.py`, seeds 447 / 657 / 877, messages up to 1,200 B) | 300 cases per set, 0 failures; accepted 54 / 47 / 58. Mean / max gas of accepted cases: 1,903,756 / 2,136,405 (44), 3,292,488 / 3,566,153 (65), 4,810,952 / 4,962,707 (87) |
| differential fuzz after R4-6 (`OPT_VERSION=glam opt_fuzz.py`, seeds 844 / 865 / 887) | 300 cases per set, 0 failures |
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
