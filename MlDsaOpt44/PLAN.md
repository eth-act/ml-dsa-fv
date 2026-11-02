# MlDsaOpt44: proof plan

## Status (v4, round 4)

Target: `MlDsaOpt/44/opt.hex` (v4: 24,050 bytes, 12,125 instructions, memory
2616 words; the proved v3 bytes are `MlDsaOpt/44/v3/opt.hex`, v2 in
`MlDsaOpt/44/v2/`). The final theorems in `MlDsaOpt44/Main.lean` are stated
with `code := MlDsaOpt44.optBytecode` (the v4 bytes) and `Gas.schedule`.
`checks/Axioms.lean` prints their axioms and lists every declaration with a
direct `sorry` (`#open_items`).

Retarget v3 → v4 (done):

* generated modules: `python3 scripts/proofgen_artifact.py MlDsaOpt/44/opt.hex MlDsaOpt44 MlDsaOpt44 opt44 2616`;
* unchanged proofs relocated in place: `python3 scripts/proofgen_port.py --reloc 44 FILES`
  (index/pc maps from `MlDsaOpt/44/v3/opt.hex` to `opt.hex`; changed regions are
  now mapped on their matching stretches (difflib), not only prefix/suffix).
  Files with pcs in custom predicates need `--all-jd --pc-lines REGEX`
  (`Fn/Decode/HintMain.lean`, `Main/Rho/Blocks.lean`, `Main/Fin/*.lean`);
  hand fixes: the sizing store (`Main/Init/Blocks.lean`), one index list of
  `Main/Fin/Blocks.lean`, `(ret := N)` arguments of the segment files;
* unchanged and re-checked: `kf4`, `kf1`, `ginit`, `cext`, `spr`, `absorb17`,
  `tbuild`, `pack`, `dhint`, `final_hash`; segments `init`, `tbl`, `rho`,
  `fin`, `short`;
* `Layout.lean`: v4 entries, `SB` (two side buffers above `KZ`), `LIM`, the
  state images `SAVE0`, `SAVE1`, `SC` in `FIN`, `zLane` with the `8q` bias,
  `zLo`/`zHi`, `spOff`, `St4At`; `Budget.lean`, `Main/Base.lean`, `Gas.lean`:
  v4 budgets and segments;
* `Main/Inv.lean`: v4 boundaries (table in the file); `SegGroups`, `SegZ`,
  `SegNtt`, `SegSib`, `SegCt`, `SegW` re-proved against the v4 contracts,
  `Valid.lean` composes all segments.

Open items (direct `sorry`; the subroutine contracts are stated, the proofs
are the work packages below):

| WP | open item | code | notes |
|---|---|---|---|
| A | `blk_call`, `blkh_call`, `blkt_call` (`Fn/Blk.lean`) | `blk` | v3 loop body over lanes `[xp, xe)`, any `abp`/`flp` (v3 proof: `Fn/Blk/*`) |
| B | `fix_call`, `gfix_call` (`Fn/Fix.lean`) | `fix`, `gfix` | `fix`: same contract, new compaction (R4-5); `gfix`: `blkt` before the first fix-up (`SlotHead`) |
| C | `group_call`, `pass3f4_call` (`Fn/Group.lean`) | `group`, `pass3f4` | group without accumulation; fused pass: exact word equation `acc4Word` |
| D | `trabs_call` (`Fn/Sponge.lean`) | `trabs` | same contract, new delta-swap network (R4-2) |
| E | `mub0_call`, `kmove_call`, `lmerge_call` (`Fn/Sponge.lean`) | `mub`, `kmove`, `lmerge` | straight line / short loops |
| F | `dz_call` (`Fn/Decode.lean`) | `dz` | `z + 8q`, flag bit 27, one multiply (R4-3, R4-6) |
| G | `ntt_call` (`Fn/Ntt.lean`) | `ntt` | bias, `b' = a − u`, Shoup in pass A; interval bounds `opt_selftest.py` |
| H | `intt_call` (`Fn/Ntt.lean`) | `intt` | GS without swap, UseHint fused into the last pass (`uh_word`) |
| I | `csum_call` (`Fn/Ct.lean`) | `csum` | replicated codes, pre-negated count, `spOff`; bases on the stack |
| J | `sib_call` (`Fn/Ball.lean`) | `sample_in_ball` | lane-unrolled loop, `±REP` codes, `c`'s 2nd block on demand from `SC` |
| K | `seg_g2`, `seg_win`, `seg_zd`, `seg_mu` (`Main/Seg*.lean`) | `expand_a`, `hash_mu` | mixed group, packed window (`kmove`, `lmerge`, images), zeroing + `dhint`, μ from the slot / `kf1` from `SC` |

v3 proof modules of changed code are still in the tree but outside the v4
import graph (`Fn/Blk/{Proof,Blocks,BodyA,Bits,Mem}`, `Fn/Fix/{Top,Phase,Loop,
Blocks,GBlocks,Lane,Rej}`, `Fn/Group/{Main,Squeeze,Common,Pass3*}`,
`Fn/Ntt/*` except `Fn/Ntt.lean`, `Fn/Decode/Z{Loop,Blocks}`, `Fn/Ct/Csum*`,
`Fn/Ball/{Blocks,Proof}`, `Fn/Hint/UseHint*`, `Fn/Sponge/{Trabs,Mu*}`,
`Main/Wp11Gen`, `Math/Sponge`): each WP adapts or replaces its files; the
ML-DSA-65/87 ports still import some of them.

Budgets of data-dependent routines (`Gas.fixNo`, `fixSq`, `gfix`, `sib`,
`mub0`, `pMu`) are the static longest paths with trip counts as documented in
`Budget.lean`; `Gas.sib` is a placeholder until WP J fixes its path count.

```sh
export TMPDIR=$PWD/.lake/tmp
lake build MlDsaOpt44
lake env lean MlDsaOpt44/checks/Axioms.lean
```

The v3 status and the original (v2) plan follow; the contract form, recipe
and pitfalls still apply. Pcs/indices quoted below are v3/v2.

## Status (v3, round 3)

Target: `MlDsaOpt/44/opt.hex` (v3: 23,091 bytes, 11,792 instructions, memory
2097 words; the proved v2 bytes are `MlDsaOpt/44/v2/opt.hex`, git tag
`opt-v2-proved`). The final theorems `MlDsaOpt44.Proofs.opt_correctInAnyContextWithSchedule`,
`opt_correctInAnyContext`, `opt_correctWithSchedule`, `opt_correct`
(`MlDsaOpt44/Main.lean`) are stated with `code := MlDsaOpt44.optBytecode` (the v3
bytes) and `Gas.schedule`. `checks/Axioms.lean` prints their axioms and lists every
declaration with a direct `sorry` (`#open_items`).

Retarget v2 → v3 (done):

* generated modules: `python3 scripts/proofgen_artifact.py MlDsaOpt/44/opt.hex MlDsaOpt44 MlDsaOpt44 opt44 2097`;
* every unchanged proof relocated in place: `python3 scripts/proofgen_port.py --reloc 44 FILES`
  (index/pc maps from `MlDsaOpt/44/v2/opt.hex` to `opt.hex`, memory size 2065 → 2097;
  the kernel re-checks everything). Hand fixes: `pc0` of the kf4 entry in
  `Main/SegG234/G3.lean`, the sizing store in `Main/Init/Blocks.lean`, `Fin` count in
  `Fn/Group/Common.lean`, heartbeats of `Fn/Sponge/Cext.lean`;
* `Layout.lean`: new `KZ` (kf1's third buffer, above `TOP`; `TOP` keeps its value);
* changed code, re-proved: `kf1` (3 rounds per iteration, `Fn/Kf1/`, generator
  `gen_kf1.py`; contract frame now `[KS, KB, KZ]`, 32,571 gas) and `usehint`
  (exact multiply-shift, `Fn/Hint/UseHint*.lean`, 56,089 gas).

Open items: **none**. The four final theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`.

```sh
export TMPDIR=$PWD/.lake/tmp
lake build MlDsaOpt44
lake env lean MlDsaOpt44/checks/Axioms.lean
python3 scripts/proofgen_gas.py --schedule   # budgets / schedule
```

The sections below are the original (v2) plan; the contract form, recipe and
pitfalls still apply. Pcs/indices quoted in them are v2.

## Layout of the development

| path | content | status |
|---|---|---|
| `MlDsaOptCommon/` | artifact-independent: `callState`, `wd`, `flag`, `word`, `byteAt`, `FrameExcept`, `FrameLocal`, `Reach` + loops, word algebra (`ofNat_*`, incl. `ofNat_not`), memory lemmas, `testBit_lit` | proved |
| `MlDsaOpt44/Bytecode.lean`, `Artifact.lean`, `Infra/*`, `Infra.lean`, `listing.tsv` | generated by `scripts/proofgen_artifact.py MlDsaOpt/44/opt.hex MlDsaOpt44 MlDsaOpt44 opt44 2065` | proved |
| `Layout.lean` | memory map, entry pcs, stack budgets, `Call`, representations (`lane`, `pack4`, `rep`, `spread`, `compress`, `il`, `cpl`, `KS4`, `KS1`, `RC4Table`, `RC1Table`, `nttRec`/`TblAt`), spec data (`zLane`, `hintOf`, `cOf`, `aOf`, `trOf`, `muOf`, …), `optAccepts` | definitions |
| `Budget.lean` | every subroutine budget | definitions |
| `Fn/*.lean` | 24 subroutine contracts | **open** |
| `Math.lean` | pure lemmas (lanes: proved; spec facts: **open**) | partly open |
| `Bridge.lean` | `accepts_eq_optAccepts`, `finBytes_size` | **open** |
| `Main/Inv.lean`, `Main/Frame.lean`, `Main/Base.lean` | boundary invariants, frame transport, segment budgets | proved |
| `Main/Seg*.lean` | one segment per file | 7 proved, 6 **open** |
| `Main/Short.lean`, `Main/Valid.lean`, `Gas.lean`, `Main.lean` | short path, composition, schedule, final theorems | proved |

## Calling convention and contract form

Caller: `PUSH2 ret; PUSH args…; PUSH2 fn; JUMP`. Callee entry stack is
`args ++ wd ret :: tail` (args top first), exit is `callState s ret
(results ++ tail) post` (the caller's return `JUMPDEST` not yet executed).
`Call s entry args ret tail pre results post gas` is `Reach` between them
(`call_iff`). Contract form, as in the reference:

```lean
theorem f_call {s} (hs : Ctx s) {ret tail} (hr : RetOK Stack.f ret tail) (m : ByteArray) (hyps…) :
    ∃ m', (functional facts, conditional on data validity) ∧ FrameExcept m m' [regions] ∧
      Call s Entry.f [args] ret tail m [results] m' Gas.f
```

**Design rule.** Hypotheses are only what termination, gas and the memory
footprint need, plus facts that are always true at the call site (tables,
zeroed scratch). Functional preconditions that adversarial input can violate
(bounds of NTT inputs, valid hints, …) are implications inside the post, so
every segment can call every contract on every input.

## Work packages

Sizes are rough (instructions to symbolically execute / Lean lines). Each WP
owns the listed files; a WP may add private helper files under
`MlDsaOpt44/Fn/<Name>/` or `MlDsaOpt44/Math/`. **Do not change a contract
statement without telling the coordinator**: segments in `Main/` consume them.
Fn contracts are independent of each other (they are stated, not proved, in
terms of each other), so all WPs can start at once.

| WP | sorries (file) | depends on (statements) | difficulty | size |
|---|---|---|---|---|
| WP1 | `kf4_call` (`Fn/Keccak.lean`) | — | hard | 760 instr (2 rounds + loop), ~1500 lines |
| WP2 | `kf1_call` (`Fn/Keccak.lean`) | — | hard | 700 instr, ~1500 lines |
| WP3 | `blk_call` (`Fn/Blk.lean`) | — | medium-hard | 590 instr, ~600 lines |
| WP4 | `spr_call`, `ginit_call`, `trabs_call`, `cext_call`, `absorb17_call`, `mu0_call` (`Fn/Sponge.lean`) | `spr` inside `mu0` | medium | 1400 instr, ~1200 lines |
| WP5 | `fix_call`, `gfix_call` (`Fn/Fix.lean`) | `kf4`, `blk`, `reach_mcopy` | hard (loop invariants) | 500 instr, ~1200 lines |
| WP6 | `pass3_call`, `pass3m_call`, `pass3k4_call`, `group_call` (`Fn/Group.lean`) | `ginit`, `kf4`, `blk`, `gfix`; Math WP12 pieces `aI = rejNTTPoly` | medium | 400 instr, ~800 lines |
| WP7 | `ntt_call`, `intt_call` (`Fn/Ntt.lean`) | — | hard (Montgomery, bounds, layer merging) | 1500 instr, ~2000 lines |
| WP8 | `dz_call`, `dhint_call` (`Fn/Decode.lean`) | — | medium | 600 instr, ~900 lines |
| WP9 | `sib_call` (`Fn/Ball.lean`) | — | medium-hard (SampleInBall list invariant) | 130 instr, ~700 lines |
| WP10 | `tbuild_call`, `csum_call`, `usehint_call`, `pack_call` (`Fn/Ct.lean`, `Fn/Hint.lean`) | — | medium | 1900 instr, ~1500 lines |
| WP11 | `seg_init`, `seg_tbl`, `seg_rho`, `seg_mu`, `seg_fin` (`Main/Seg{Init,Tbl,Rho,Mu,Fin}.lean`) | `spr`, `kf1`, `absorb17`; sponge lemmas | medium (long straight line, memory tables) | 1900 instr, ~1500 lines |
| WP12 | `seg_g234` (`Main/SegG234.lean`) + sponge meaning of `KS4`/`ginit`/`trabs`/`cext` | WP4–WP6 statements | hard (three inline mixed groups, tr/μ/c̃ riders) | 600 instr + glue, ~1500 lines |
| WP13 | `Math.lean` spec facts, `Bridge.lean` | — | hard (`accepts_eq_optAccepts`: NTT convolution theorem) | ~1500 lines |

### Guidance per WP

* **WP1 kf4.** Index range: entry pc 21032 = index 10319 (`listing.tsv`);
  one loop iteration is two rounds `KS→KB→KS`. Prove one round as a lemma on
  arbitrary interleaved input words (`il`), split into ~15 blocks of ≤ 60
  instructions (stack never deeper than ~12). Pure lemmas: 256-bit rotation
  by `4n` of `il v` is `il (rotl64 n ∘ v)`; `il` commutes with `&&&`, `|||`,
  `^^^`, NOT (`2^256 − 1 − x`); lane-complementing chi identities (`CHI` table
  in `scripts/opt_keccak.py`) against `Keccak.round`. Then 12 iterations with
  `Reach.loop` and `RC4Table`. Keep `S` abstract (`Sized4`).
* **WP2 kf1.** Same template, replicated lanes, rotations are single shifts:
  state an invariant "word = rep(v) on bit window W" (`decay_windows` in
  `opt_keccak.py` gives the windows; check them by `decide +kernel`), and
  the re-replication `((x >> 64) & M64) · REP = rep(lane 1 of x)`.
* **WP3 blk.** Six delta swaps compose to `deinterleave` (bit `4b+k ↦
  64k+b`); prove with `eq_of_testBit_lt` + per-bit `simp` (256 bits per
  swap: do it once on the composed map). Candidate extraction is 3 bytes per
  lane with bit 23 masked; flag word lanes never carry (`cand + 8191 < 2^24`).
* **WP4.** `spread`/`compress` networks: 6 shift-or-mask stages, bit lemmas as
  in WP3. `ginit`'s word is fully given by `ginitWord`. `trabs`/`absorb17`
  are loops over calldata words (`bsw`/`le64`); `mu0` composes `spr`,
  `trabs` (`kp = KS + 256`, `n4 = 3`, top-lane mask) and its own padding XORs.
* **WP5 fix/gfix.** Invariant for the group loop: lane `s` of `ABUF[0, wp)` is
  the accepted prefix of `candI`, `rp` the next unread position, writes stay
  below `rp` (positions up to 263 may be overwritten in lane `s`); `Pending`
  is the per-slot bundle (see the docstring). The 6th squeeze is
  `reach_mcopy` + `kf4_call` + `blk_call (b := 5)` + `reach_mcopy`. Gas: the
  first-flag scan ≤ 32 visits, ≤ 44 group-loop visits; the contract's gas
  `if HAVE6 flipped then Gas.fixSq else Gas.fixNo` lets `gfix` charge one
  squeeze. Relate to `rejNTTPolyOf` with the reference's scan lemmas
  (`MlDsa44/Proofs/Math/Sampling/Rej.lean`).
* **WP6.** `pass3*` are 32 iterations of an 8-word unrolled body (exact word
  equations). `group_call` composes `ginit` (with `L4` computed in its prologue),
  `kf4`/`blk` ×5, `gfix 15`, `pass3`; needs the WP12/WP13 lemma "`ginitWord`
  with `amult = 15`, `keep = 0` is `KS4` of the padded seeds `ρ‖col‖r`", and
  `aI (seed state) = rejNTTPoly seed` (`squeeze_extract_shake` in the
  reference's `Math/Sponge.lean`).
* **WP7.** `opt_ntt.py` docstring has the bound argument per merged layer.
  Prove the Montgomery lemma once (`(t + m q) >> 32 ≡ t · 2^-32`, low 32 bits
  zero, per lane, no cross-lane carry) and a butterfly lemma per CT/GS shape;
  then the three passes as loops; finally relate to `Fips204.ntt`/`nttInv`
  (reference `Math/Ntt/Model.lean` has the layer model).
* **WP8.** `dz`: `gen_decode` loop with gather sub-loop; z lanes are
  `K − raw`; norm flag iff via the two SIMD comparison constants. `dhint`:
  4 unrolled rows + trailing scan; mirror the reference `Math/Decode/Hint.lean`.
* **WP9 sib.** Loop invariant: `CW` codes, `BASES`/`IDX`/`CNT` describe the
  current SampleInBall array (moves update `BASES[IDX[j]−1]`); fold over the
  reference's `sampleIndex` characterisation (`Math/Sampling/Ball.lean`).
* **WP10.** `tbuild`: 10 chunks of 6 words, 16-bit cells (transpose16 = 2
  delta swaps); `csum`: 64 iterations × τ unaligned loads (the window
  addressing is the whole point: `be16` at `tt + 6142 − 8e − 2r`);
  `usehint`: multiply-shift exactness checked by `decide +kernel` over the
  input range split; `pack`: 6-bit packing into 24 lanes per row.
* **WP11.** Long straight-line stores: state memory as `storeWords` (copy the
  reference's `rc_blocks` pattern), prove table predicates by `decide +kernel`
  per entry. `seg_init` uses `reach_block_pot` (memory grows once).
  `seg_mu`: branch on `|M| ≤ 69` (`MU` copy) vs `hash_mu` (`kf1` loop,
  `absorb17`, padding); needs "kf1 sponge = `Fips202.absorb`" (WP13).
  `seg_fin`: six `kf1` absorptions + final permutation, then the c̃
  comparison block; the `E` of the statement is the comparison bit.
* **WP12.** `seg_g234`: groups 2–4 inline (`ginit`, `trabs ×10`, `mu0`,
  `cext` for `CB`, `MU`, `TRL`, `gfix 7/7/12`, `pass3m ×2`, `pass3k4`).
  Establishes `Inv5`: `AccAt` from `AccCols 2` plus two masked columns and the
  Kronecker lane, `TRL = tr`, `CB = H(c̃) stream`, `MU = μ` for short messages.
* **WP13.** `Math.lean`: `cStream_size`, `sampleInBallOf_coeffs`,
  `rejNTTPoly_range`, `ntt_zLane`, `nttInv_congr`, `csum_congr` (the
  `2^13 · 1023 = q − 1` identity), `hintBitUnpack_range`, `useHint_emod`,
  `useHint_range`, `finBytes_le64_*`; `Bridge.lean`: reuse
  `MlDsa44.Proofs.verifyInternal_eq_flat` and prove `nttInv` linearity plus
  the convolution theorem `nttInv(ĉ ∘ t̂) = c · t` (negacyclic). `nttInv_range`
  is currently unused.

## Segment map (`Main/Inv.lean`)

| segment | pcs | file | status | uses |
|---|---|---|---|---|
| init | 0 → 992 | SegInit | open (WP11) | — |
| zh | 992 → 1085 | SegZh | **proved** | dz, dhint |
| tbl | 1085 → 3068 | SegTbl | open (WP11) | — |
| ntt | 3068 → 3078 | SegNtt | **proved** | ntt, `ntt_zLane` |
| rho | 3078 → 3439 | SegRho | open (WP11) | spr |
| g0, g1 | 3439 → 3466 | SegGroups | **proved** | group, `rejNTTPoly_range` |
| g234 | 3466 → 4648 | SegG234 | open (WP12) | many |
| mu | 4648 → 5926 | SegMu | open (WP11) | kf1, absorb17 |
| sib | 5926 → 5936 | SegSib | **proved** | sib |
| ct | 5936 → 5963 | SegCt | **proved** | tbuild, csum |
| w | 5963 → 6001 | SegW | **proved** | intt, usehint, pack, Math |
| fin | 6001 → RETURN | SegFin | open (WP11) | kf1 |

## Infrastructure recipe and measured costs

Same recipe as `MlDsa44/Proofs/Infra/README.md`, with the artifact-specific
names `MlDsaOpt44.Proofs.Infra.*` and the tactics `opt44_block` /
`opt44_reach path with [lemmas]`; `Ctx.sized` is `2065 ≤ activeWords`
(fixed memory). Instruction indices and pcs: `MlDsaOpt44/listing.tsv`;
annotated listing with labels: `MlDsaOpt/44/opt.asm`;
`#eval MlDsaOpt44.Proofs.Infra.blockCostEval [indices]` for block costs.
`reach_mcopy` covers the two `MCOPY`s in `fix`.

* 71-instruction kf4 theta block (`scratch/opt/Timing.lean`): simp 1.8 s,
  kernel 2.5 s, ~6 s elaboration (≈ 4 s per 50 instructions); file 18 s /
  2.2 GB with imports.
* `Artifact.lean` 50 s / 2.6 GB; `Infra/Code.lean` (29 chunked table checks)
  67 s / 2.8 GB; every other module < 25 s / 2.3 GB.

## Pitfalls found while building the skeleton

* Never let the kernel unfold `located`, `instructionPC` or `instructionList`
  (as for the reference). The artifact's whole-list equalities (`assemble`,
  `all wellFormedB`, the table check) are proved chunk by chunk; `rw [def]`
  on these lists makes `rw`'s closing `rfl` evaluate them — use
  `unfold` + `rewrite`.
* **`List.sum`/`List.range` over terms that mention spec data** (`aD`, `word m …`)
  made one `simp only` proof take 500 s of kernel time and 19 GB. Use explicit
  recursion (`accSum`, `okUpTo`) and `congrArg pack4 (funext …)`; avoid
  `congr 1` / `rw` closing goals by `rfl` on such terms.
* `rw` on a goal whose `Decidable` instance depends on the rewritten term
  fails ("motive is not type correct"); use `simp only [lemma]`.
* `&&` binds weaker than `=`: parenthesise Bool equations.
* `Avoids [(ZH, …)] MISC TOP` is false: shrink a `ZeroOn` with `.mono` before
  transporting it.

## Reuse for ML-DSA-65/87

`MlDsaOptCommon` and `scripts/proofgen_artifact.py` are artifact-independent:
run it on `MlDsaOpt/65/opt.hex` with namespace `MlDsaOpt65` and the memory
size of that layout. Kernels generated by the same Python with the same
parameters (`kf4`, `kf1`, `blk`, `spr`, `cext`, `trabs`, `ntt`, `intt`,
`pass3`, `fix` up to `FL`/`ABUF` addresses) are the same instruction
sequences at different offsets: state their block lemmas with the instruction
index as a parameter offset (`base + i`) and the pc as `pcAt (base + i)`, and
discharge per artifact with a generated `instrAt (base + i) = instrAt₄₄ (i₄₄ + i)`
table check (one `decide +kernel` per kernel). Contracts whose statements
depend only on `KS`/`KB`/`RC*`/`TBL` (kf4, kf1, ntt, intt) carry over
verbatim; parameters (`k`, `l`, `τ`, `ω`, `γ2`) enter `dz`, `dhint`, `sib`,
`csum`, `usehint`, `pack` and the main flow.
