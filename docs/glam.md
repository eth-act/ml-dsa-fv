# Glamsterdam variant (MlDsaOpt/NN/glam/)

`MlDsaOpt/{44,65,87}/glam/opt.hex` is the v3 verifier (`docs/opt.md`) with
both Keccak-f kernels replaced by **stack-resident, fully unrolled kernels**.
They need two EIPs scheduled for Glamsterdam (EIP-7773):

* **EIP-8024** (Last Call): `DUPN` 0xe6, `SWAPN` 0xe7, `EXCHANGE` 0xe8, 3 gas
  each, with one immediate byte. `DUPN n` / `SWAPN n` take n in [17, 235]
  through `encode_single(n) = (n + 111) % 256`, and immediates 91..127 halt
  (no 0x5b, no PUSH bytes, so JUMPDEST analysis is unchanged). `EXCHANGE n m`
  is pair-encoded and reaches only n < m ≤ 30 − n. It is not used here.
* **EIP-7954** (Last Call): the code size limit goes from 24,576 to 65,536 B
  (initcode 131,072 B).

No other SFI EIP changes the frame gas of these opcodes (EIP-7904 is
informational), so the numbers below are Osaka costs plus 3 gas per new op.
EIP-7976 (calldata floor) and EIP-8037 (state creation) change transaction
and deployment costs, not frame gas.

v3 (`MlDsaOpt/NN/opt.hex`) is unchanged and byte-identical. `gen_opt.py` is
not edited; `scripts/gen_glam.py` subclasses its generator.

## Result

Frame gas, valid empty-message vector (line 1 of each `calldata.txt`):

| set | v3 | **glam** | saving | worst v3 | **worst glam** | saving | code v3 | **code glam** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 44 | 2,105,097 | **1,947,956** | −157,141 (−7.5%) | 2,864,301 | **2,682,670** | −181,631 (−6.3%) | 23,091 | **45,832** |
| 65 | 3,701,979 | **3,446,878** | −255,101 (−6.9%) | 5,073,355 | **4,774,172** | −299,183 (−5.9%) | 23,422 | **46,163** |
| 87 | 5,424,737 | **5,003,232** | −421,505 (−7.8%) | 7,954,105 | **7,449,398** | −504,707 (−6.3%) | 23,982 | **46,723** |

Per-call kernel gas (same harness and convention as the `docs/opt.md`
profile; the in-situ profile of the 44 run gives the same numbers):

| kernel | v3 | glam | saving | code v3 | code glam |
|---|---:|---:|---:|---:|---:|
| kf4 (4 interleaved states) | 40,238 | **35,340** | −4,898 (−12.2%) | 1,521 B | 15,001 B |
| kf1 (1 replicated state) | 32,571 | **27,705** | −4,866 (−14.9%) | 1,994 B | 12,232 B |

The 44 saving splits into kf4 25 × 4,898 = 122,450, kf1 7 × 4,866 = 34,062,
and 629 in `main`: the RC4 and RC1 iota tables are no longer initialised.
Their memory stays allocated, so every address and the memory size match v3.

Of kf4's 4,898, about 253 comes from unrolling alone (40,238 → 39,985,
measured on the Keccak-representation thread) and 216 from immediate iota
(24 × 9). The remaining ~4.4k comes from keeping the state on the stack.

**Deployment.** The code roughly doubles. Under EIP-8037 (CPSB = 1,530 gas
per byte of code deposit) that is ≈ 35M state gas more, one time, per
deployment (≈ 70M instead of ≈ 35M). At 44's saving of 157k per
verification, it pays back after ≈ 220 verifications.

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

### Remaining kernel headroom (not done)

* Chaining every chi output into the next input slot, not only the plane's
  last one, breaks chi's in-place consumption: B2 and B3 must sit right below
  the partial result. A scheduler search might save ≤ 2 gas per lane
  (≤ 1.1k per kf4 call).
* Keeping the Keccak state on the stack across `kf4` → `blk` / `trabs` would
  save the 300 gas of entry/exit per call (7.5k for 44, 0.4%). That needs
  `blk`, `trabs`, `cext` and `ginit` to take lanes from the stack, which is a
  large change.

## Where else deep stack or larger code pays (estimates, not built)

| idea | saving | notes |
|---|---|---|
| Unrolled Keccak rounds with immediate iota (memory-resident state) | ~470 per call: 253 unroll (measured) + 216 iota. 44: ~15k (0.7%) | Included in the glam kernels. On its own it costs +16.6 KB for 0.3% |
| NTT / INTT layer merging 4 + 4 (16 words on the stack) instead of 3 + 3 + 2 (8 words) | One fewer pass: 256 data loads + 256 stores at ~12 gas each ≈ 5–6k per call. 44 (1 ntt + 1 intt): ~11k (0.5%); 65 / 87 (2 + 2): ~22k (0.6% / 0.4%) | Measured traffic: 768 data MLOAD + 768 MSTORE per call (ntt 99,705, intt 119,593). Zeta loads stay the same. A single pass is impossible (256 words > DUPN's reach of 235). The lane-bound argument in `opt_ntt.py` must be redone for 4 lazy layers |
| Pre-expanded zeta or c tables in code (CODECOPY) | ~1.7 KB of NTT records were rejected for proof scope, not size | Now affordable in size; CODECOPY is still outside the stepper's set |
| A·ẑ fusion of 4 columns (`docs/opt.md`: ~27k for 44, net ~14k) | unchanged | Needs memory, not stack or code |

Keccak is the only component where deep stack access changes the cost
structure. Every other kernel already keeps its working set (≤ 16 words) on
the stack, and its memory traffic is a small share.

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
4. **Toolchain.** revm/Foundry (`scripts/opt_forge.sh`) was not available in
   this environment, and Glamsterdam support in the pinned revm is
   unverified. The glam numbers come only from `opt_evm.py` with
   `fork="glamsterdam"`, which passes all EIP-8024 test cases. Cross-check
   with a second client (revm / evmone with EIP-8024) before relying on them.

## Validation

| check | result |
|---|---|
| EIP-8024 test cases (assembly + execution) on `opt_evm.py` | all pass; 0xe6 still undefined under `fork="osaka"` |
| kernels vs reference Keccak-f (random + all-ones states, complemented lanes), no memory written outside KS | pass |
| v3 artifacts after the `opt_asm` / `opt_evm` changes | byte-identical |
| all vectors on glam bytecode (44: 47, 65: 57, 87: 57) | 0 mismatches |
| forced sixth squeeze (debug build) | 19 / 21 / 36 vectors with sixth-block checks, all correct |
| differential fuzz (`opt_fuzz.py --glam`, seeds 441 / 641 / 841, messages up to 1,200 B) | 44: 300 cases (64 accepted), 65: 200 (44), 87: 200 (50); 0 failures. Mean / max gas of accepted cases: 2,007,031 / 2,191,269 (44), 3,493,993 / 3,683,870 (65), 5,086,410 / 5,291,271 (87) |

## Reproducing

```sh
export TMPDIR=$PWD/.lake/tmp
python3 scripts/gen_glam.py                 # MlDsaOpt/{44,65,87}/glam/{opt.hex,opt.asm,layout.txt}
python3 scripts/opt_selftest_glam.py        # EIP-8024 cases, kernels, v3 unchanged, vectors, forced 6th squeeze
python3 scripts/opt_worstcase.py --glam     # typical and worst case per set
python3 scripts/opt_fuzz.py --glam 44 300 441
```
