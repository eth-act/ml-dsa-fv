# Keccak-f[1600] kernel lab

Prototypes for cheaper Keccak-f in EVM bytecode under EIP-8355's rules
(compressed key, real SHAKE, no helper contracts or precompiles). Nothing here
is used by `gen_opt.py` / `gen_glam.py`. The v2, v3, v4 and glam artifacts
are unchanged.

```sh
python3 scripts/keccak_lab/baseline.py   # kf4 v3/v4 and glam kf4 through the same harness
python3 scripts/keccak_lab/kf8m.py       # 8-way memory-rotation kernel (loop 2/4/6, unrolled, no D frames)
python3 scripts/keccak_lab/kf8i.py       # kf8m with 1 round per iteration, in place (~16 s, row search)
python3 scripts/keccak_lab/kf4m.py       # 4-way kf4 with memory rotations for the even-ROT lanes
python3 scripts/keccak_lab/xswap.py      # blk prologue for the 8-way layout
python3 scripts/keccak_lab/model.py      # whole-verifier model (profiles v4 and glam on first run)
```

`lab.check` runs every kernel on `opt_evm.py` against `opt_ref.keccak_f`.
Each call mixes different states over the slots: all-zero, all-ones,
zero/ones alternating by slot, 16 single-bit states at asymmetric
(lane, bit) positions, and random states. Gas per call uses
`opt_selftest_glam.py`'s convention (harness minus 15). Code size is the
subroutine's size.

## Kernels

| variant | gas / call | gas / state | code (B) | KAT |
|---|---:|---:|---:|---|
| kf4 v3/v4 (baseline) | 40,238 | 10,060 | 1,521 | 10 calls (40 states) ok |
| kf4 glam, stack-resident (baseline, Glamsterdam) | 35,340 | 8,835 | 15,001 | 10 calls ok |
| **kf4m**: kf4 + memory rotation of the 12 even-ROT lanes | 39,806 | 9,952 | 1,607 | 10 calls ok |
| **kf8m**, 2 rounds per iteration | **68,522** | **8,565** | 2,982 | 8 calls (64 states) ok |
| kf8m, 4 rounds per iteration | 68,384 | 8,548 | 5,949 | ok |
| kf8m, 6 rounds per iteration | 68,338 | 8,542 | 8,919 | ok |
| kf8m, 24 rounds unrolled, immediate iota | 67,796 | 8,474 | 35,942 | ok |
| kf8m without D frames (5 rotations per round) | 70,454 | 8,807 | 3,051 | ok |
| **kf8i**: kf8m, 1 round per iteration, in place | 71,558 | 8,945 | 1,532 | ok |

All use only opcodes from docs/opt.md "Opcodes" (no DUPN/SWAPN needed).

### kf8m (`kf8m.py`)

* **Layout.** 8 states. Word (lane i, half h) holds bit 2b + h of lane i of
  state s at bit 8b + s, so each byte is one bit position of all 8 states.
  50 words.
* **Rotation by memory.** Every word is stored twice (a and a + 32), so
  MLOAD(a + k) is the word rotated by k bytes, which rotates every state's
  half-lane by k. Rotating a lane by 2m rotates both halves by m. Rotating
  by 2m + 1 moves the odd half, rotated by m + 1, into the even half, and the
  even half, rotated by m, into the odd half. rho is one MLOAD at an offset.
  The extra cost is the second store: DUP1 PUSH MSTORE PUSH MSTORE (15 gas)
  instead of PUSH MSTORE (6).
* **Theta.** rho rotates A ⊕ D, so D (10 words) is also stored twice and
  read at the lane's offset: B = MLOAD(A + k) ⊕ MLOAD(D + k + f). This beats
  applying D in an extra pass before a duplicated store (33 vs 24 gas per
  word).
* **D frames** (rotation-frame tracking). Each D word is stored rotated by
  a frame f, and each column parity is computed in a frame by reading its 5
  lanes at an offset, which is free. The frame equations around the 5-cycle
  of C/D dependencies close up to one byte, so one physical rotation per
  round remains instead of five: −1,932 gas per call (−2.8%).
* **Round cost** (8 states): 2,825 gas. Parities 420, D 246 (including the
  rotation and 10 duplicated stores), rho 750, chi + iota ~660, duplicated
  stores 750. Per word that is 56.5 gas, against kf4's 67 and glam kf4's 58.
* **Interface.** The state lives in KS in the duplicated layout (3,200 B).
  Writers (absorption, ginit) must write both copies; readers read the
  first. Total memory: KS + KB 6,400 B, D 640 B, iota table 1,536 B.

### kf8i (`kf8i.py`)

kf8m with a single in-place buffer and one round per loop body, so the code
is the size of kf4. Chi outputs whose home word is still unread by rho are
parked on the stack (22 per round). After the last row they are stored, top
first, with no extra cost. Parking costs a SWAP and breaks some in-place
operand consumption in chi. The B load order and output order of each row
are chosen by exhaustive search. Net cost: +3,036 gas per call (+4.4%) over
kf8m, for half the code.

### kf4m (`kf4m.py`)

On the existing 4-way layout, a 64-bit rotation by n is a 4n-bit word
rotation. That is a byte rotation only for even n: 12 of 24 lanes. Those
lanes save 21 − 15 + 3 gas, but D must be stored twice and also kept on the
stack. Net −18 gas per round (−432 per call, −1.1%). KS moves to stride 64.
Not worth integrating.

### Not built (estimates)

* **16-way / 32-way** (4 or 8 parts per lane, bit 16b + s / 32b + s): every
  rotation is still a byte rotation and the per-word costs are identical
  (store 15, parity 9, rho 15, chi 13). The only saving is the single theta
  rotation per round, amortised over 100 or 200 words, about 0.2%. Packing
  is worse (16 or 32 slots per group), and code and memory double or
  quadruple. Not worth building.
* **More frame tracking in kf8m.** Choose row frames so that some words need
  only offset-0 reads and skip their second store. Parity alignment allows at
  most one such word per row-half, so at most 10 per round (≤ 90 gas, ≤ 3%).
  Frame tracking in the 4-way layout does not pay: parity needs column
  alignment, so every frame difference between rows costs a rotation.
* **Glamsterdam kf8m with parities from the stack.** DUPN on parked outputs
  instead of MLOAD saves 150 per round. But parities would then be in frame
  0, which brings back the 5 theta rotations (+84). Net about −2%.

## Whole verifier (`model.py`)

The model starts from the measured profiles of v4 and glam (valid
empty-message vector) and replaces:

* kf4 calls with the measured kf8m / kf8i calls;
* `blk` with 2 × v4 `blk` per call plus 21 × 45 gas of cross-word swap
  (`xswap.py`). After the swap, each half is an ordinary kf4 word, so the
  unzip and candidate extraction are unchanged;
* `trabs`: +1,275 per call. v4's 7-stage zip network already yields
  bit 8b + 4h + i, so the network stays; each calldata word needs 8
  extractions instead of 4, each stored twice;
* `cext` ×2, `ginit` ×2.5 per group;
* memory: +7.2 KB, +2.6k gas.

Schedules:

* **pure.** 8-slot groups only:
  * 44: 3 groups, 15 calls;
  * 65: 5 groups, 25 calls, μ in group 4;
  * 87: 8 groups, 40 calls; tr in groups 0–3, so H(c̃) and μ ride in spare
    slots and save 2 kf1 calls.
* **mixed.** Full 8-slot groups plus one 4-slot kf4 group: 10+5 / 20+5 /
  35+5 calls. It needs both kernels and both `blk` paths.

| base, kernel | schedule | set | today | modeled | delta | keccak | blk | trabs | cext | ginit | mem | code (B) |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| v4, kf8m | pure | 44 | 2,042,346 | 2,145,304 | +102,958 (+5.0%) | +21,880 | +52,242 | +14,025 | +10,326 | +1,885 | +2,600 | 24,247 (was 22,546) |
| v4, kf8m | pure | 65 | 3,564,626 | 3,564,990 | +364 (+0.0%) | -97,660 | +61,926 | +20,400 | +10,326 | +2,772 | +2,600 | 24,920 (was 23,219) **over limit** |
| v4, kf8m | pure | 87 | 5,271,542 | 5,038,441 | -233,101 (-4.4%) | -342,112 | +75,867 | +25,500 | +1,659 | +3,385 | +2,600 | 25,642 (was 23,941) **over limit** |
| v4, kf8m | mixed | 44 | 2,042,346 | 1,959,961 | -82,385 (-4.0%) | -119,540 | +9,450 | +14,025 | +10,326 | +754 | +2,600 | 25,768 (was 22,546) **over limit** |
| v4, kf8m | mixed | 65 | 3,564,626 | 3,379,356 | -185,270 (-5.2%) | -239,080 | +18,900 | +20,400 | +10,326 | +1,584 | +2,600 | 26,441 (was 23,219) **over limit** |
| v4, kf8m | mixed | 87 | 5,271,542 | 4,918,356 | -353,186 (-6.7%) | -418,390 | +33,075 | +25,500 | +1,659 | +2,370 | +2,600 | 27,163 (was 23,941) **over limit** |
| v4, kf8i | pure | 44 | 2,042,346 | 2,190,844 | +148,498 (+7.3%) | +67,420 | +52,242 | +14,025 | +10,326 | +1,885 | +2,600 | 22,797 (was 22,546) |
| v4, kf8i | pure | 65 | 3,564,626 | 3,640,890 | +76,264 (+2.1%) | -21,760 | +61,926 | +20,400 | +10,326 | +2,772 | +2,600 | 23,470 (was 23,219) |
| v4, kf8i | pure | 87 | 5,271,542 | 5,159,881 | -111,661 (-2.1%) | -220,672 | +75,867 | +25,500 | +1,659 | +3,385 | +2,600 | 24,192 (was 23,941) |
| v4, kf8i | mixed | 44 | 2,042,346 | 1,990,321 | -52,025 (-2.5%) | -89,180 | +9,450 | +14,025 | +10,326 | +754 | +2,600 | 24,318 (was 22,546) |
| v4, kf8i | mixed | 65 | 3,564,626 | 3,440,076 | -124,550 (-3.5%) | -178,360 | +18,900 | +20,400 | +10,326 | +1,584 | +2,600 | 24,991 (was 23,219) **over limit** |
| v4, kf8i | mixed | 87 | 5,271,542 | 5,024,616 | -246,926 (-4.7%) | -312,130 | +33,075 | +25,500 | +1,659 | +2,370 | +2,600 | 25,713 (was 23,941) **over limit** |
| glam, kf8m6 | pure | 44 | 1,850,700 | 2,070,462 | +219,762 (+11.9%) | +141,570 | +49,356 | +14,025 | +10,326 | +1,885 | +2,600 | 48,129 (was 53,971) |
| glam, kf8m6 | pure | 65 | 3,243,261 | 3,456,526 | +213,265 (+6.6%) | +118,150 | +59,017 | +20,400 | +10,326 | +2,772 | +2,600 | 48,802 (was 54,644) |
| glam, kf8m6 | pure | 87 | 4,766,670 | 4,900,405 | +133,735 (+2.8%) | +27,610 | +72,981 | +25,500 | +1,659 | +3,385 | +2,600 | 49,524 (was 55,366) |
| glam, kf8m6 | mixed | 44 | 1,850,700 | 1,864,435 | +13,735 (+0.7%) | -23,420 | +9,450 | +14,025 | +10,326 | +754 | +2,600 | 63,130 (was 53,971) |
| glam, kf8m6 | mixed | 65 | 3,243,261 | 3,250,231 | +6,970 (+0.2%) | -46,840 | +18,900 | +20,400 | +10,326 | +1,584 | +2,600 | 63,803 (was 54,644) |
| glam, kf8m6 | mixed | 87 | 4,766,670 | 4,749,904 | -16,766 (-0.4%) | -81,970 | +33,075 | +25,500 | +1,659 | +2,370 | +2,600 | 64,525 (was 55,366) |

Measured inputs: kernel gas, today's profiles, and the cross-swap cost.
Estimated inputs: the `blk` / `trabs` / `cext` / `ginit` factors, memory,
and +240 B of glue code. The fix-up, accumulation (`pass3*`) and group
bookkeeping are taken as unchanged.

### Reading

* **Kernel.** The memory-rotation kernel is the cheapest per state measured
  here:
  * 8,565 per state on today's EVM: −14.9% vs kf4 and −3.1% vs glam kf4;
  * 8,474 unrolled, but that is 36 KB of code.
* **Glamsterdam.** No win:
  * 8-slot groups waste slots: 44 needs 20 slots, 65 needs 35 and 87
    needs 60;
  * `blk` / `trabs` / `cext` pay for the half-word layout.
  The kernel gain is 3%, and the best case is mixed 87 at −0.4%.
* **Today's EVM (v4).** Real wins, but the 24,576 B limit binds:
  * kf8m mixed: −4.0 / −5.2 / −6.7%, over by 1.2 / 1.9 / 2.6 KB;
  * kf8m pure 87: −4.4%, over by 1.1 KB;
  * fitting without other changes: kf8i pure 87, −112k (−2.1%), and kf8i
    mixed 44, −52k (−2.5%, 258 B margin on an estimated glue size);
  * 65 has no fitting win: kf8i mixed is −125k but 415 B over.

### Integrating (v4 base)

1. **Layout and memory.**
   * KS and KB become 3,200 B each, in the duplicated half-word layout.
   * New regions: D (640 B) and the 48-word iota table RC8.
   * BK becomes 3,200 B, so the sixth-squeeze MCOPY moves 3,200 B.
2. **Kernel.** Add kf8m or kf8i to the generator. For mixed, keep kf4.
3. **`build_schedule`.**
   * Use 8-slot groups, plus the optional 4-slot group.
   * tr gets one slot in each of 2 / 3 / 4 consecutive groups, with μ after
     tr. For pure 87, put tr in groups 0–3 so that c̃ and μ ride later.
   * ABUF/FL hold two 4-slot sets per block. Per-slot `fix` / `gfix` and
     per-(column, 4 rows) `pass3*` stay as they are.
4. **`blk`.**
   * Add `xswap` (t = ((W0 >> 4) ⊕ W1) & 0x0f…; W1 ⊕= t; W0 ⊕= t << 4) per
     lane pair.
   * Then run v4's unzip and extraction on each half.
5. **Writers and readers.**
   * `trabs`: same zip network, then 8 extractions per word, each stored
     twice.
   * `ginit` and `mu0`: write both copies.
   * `cext`: gather and re-interleave the even/odd halves.
6. **Proofs.**
   * A new kernel proof: 8-way round algebra, the lemma "MLOAD at a + k of
     a word stored at a and a + 32 is its k-byte rotation", and the D frame
     bookkeeping.
   * kf8i adds the parking/store order.
   * Smaller lemma changes: the `blk` prologue (one delta swap), the
     `trabs` extraction, and the schedule.
7. **Code size.** For anything beyond kf8i pure 87 or kf8i mixed 44, find
   1–2.6 KB elsewhere.
