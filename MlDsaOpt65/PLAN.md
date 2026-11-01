# MlDsaOpt65 / MlDsaOpt87: proof plan for the parallel phase

One plan for both artifacts (`MlDsaOpt87/PLAN.md` points here): every work
package below closes the same contract, lemma or segment for ML-DSA-65 *and*
ML-DSA-87.

Targets: `MlDsaOpt/65/opt.hex` (22,512 bytes, 11,461 instructions) and
`MlDsaOpt/87/opt.hex` (23,443 bytes, 11,950 instructions). The final theorems

```lean
MlDsaOpt65.Proofs.opt_correctInAnyContextWithSchedule :
  MlDsa65.CorrectInAnyContextWithSchedule MlDsaOpt65.optBytecode Gas.schedule
MlDsaOpt65.Proofs.opt_correctInAnyContext : MlDsa65.CorrectInAnyContext optBytecode
MlDsaOpt65.Proofs.opt_correctWithSchedule : MlDsa65.CorrectWithSchedule optBytecode Gas.schedule
MlDsaOpt65.Proofs.opt_correct : MlDsa65.Correct optBytecode
```

(and the same four in `MlDsaOpt87.Proofs` against `MlDsa87`) are stated with
the audited `MlDsa65/Spec.lean` / `MlDsa87/Spec.lean` definitions and are
**proved** from the open items listed below. They depend on `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`; `checks/Axioms.lean` lists the
declarations with a direct `sorry` and the ones the final theorems use.

```sh
export TMPDIR=$PWD/.lake/tmp
lake build MlDsaOpt65 MlDsaOpt87                 # everything; ported block modules 30–130 s each
lake env lean MlDsaOpt65/checks/Axioms.lean      # axioms, open items, ported contracts axiom-clean
lake env lean MlDsaOpt87/checks/Axioms.lean
python3 scripts/proofgen_gas_param.py 65 --analyse|--schedule   # budgets (also 87)
```

Memory is shared with other jobs: iterate with `lake env lean FILE` or
`lake build <Module>`; a ported block module peaks at 3.5 GB.

## Reuse of the ML-DSA-44 proofs

`scripts/gen_opt.py` emits most kernels identically for all three sets; in the
65/87 bytes they differ from 44 only in absolute jump targets (and, for `fix`
and `group`, one data constant). Two routes were evaluated:

* **Semantic code-window transport** (a theorem moving a 44 `Reach` to another
  code): rejected. Every 44 contract quantifies over a return address with
  `RetOK`, i.e. a valid JUMPDEST *of the 44 code*, so it cannot be
  instantiated at a 65/87 return address; inside a window, inverting the
  relational `Steps` of a 44 trace needs an argument that no exception
  (resume of the caller frame) path rejoins the frame, i.e. a gas/call-stack
  invariant over all of the EVM semantics. Even the in-window part would
  still need the kernels' compositions redone per artifact.
* **Relocating port** (chosen): `scripts/proofgen_port.py NN [--sub A=B] [--path A=B] FILE…`
  rewrites a 44 proof file for artifact NN — instruction indices in
  `opt44_reach [..]` / `locatedPath [..]` / `reach_mcopy`, program counters in
  `callState X N` / `then N` / `else N`, return addresses `wd N` (only if `N`
  is a 44 JUMPDEST), the memory size, tactic and namespace names — through
  index/pc maps built from the two `listing.tsv` files and `layout.txt`
  (regions with equal instruction counts; data constants via `--sub`). The
  ported file imports and opens the 44 modules for every pure lemma (models,
  bit identities, loop invariants), so only the `Reach`-bearing files are
  re-elaborated. Nothing is trusted: the ported proofs are re-checked by the
  kernel against the 65/87 bytes. Hand fixes are marked `-- port:`; the exact
  regeneration commands are in each contract file's docstring. A full port of
  kf4 + kf1 for both sets builds in ~1 min wall time.

**Proved by the port** (axiom-clean, `checks/Axioms.lean`), for both sets:
`kf4_call`, `kf1_call` (`Fn/Keccak.lean`), `blk_call` (`Fn/Blk.lean`),
`spr_call`, `trabs_call`, `cext_call`, `absorb17_call` (`Fn/Sponge.lean`),
`fix_call`, `gfix_call` (`Fn/Fix.lean`, `--sub` for `BK`), `ntt_call`,
`intt_call` (`Fn/Ntt.lean`: the 44 proof is pinned to one address, so it is
ported twice, `Fn/Ntt` at `ZH`/`ACC` and `Fn/Ntt2` at `ZH2`/`ACC + 0x2000`),
`tbuild_call` (`Fn/TBuild.lean`, generalised to a table pointer and `t1`
offset), `pass3_call` (`Fn/Group.lean`, generalised to pointers), and for 87
`pass3m_call`.

## Layout of the development (per set; `NN` = 65 or 87)

| path | content | status |
|---|---|---|
| `MlDsaOptNN/{Bytecode,Artifact,Infra/*,Infra}.lean`, `listing.tsv` | generated: `python3 scripts/proofgen_artifact.py MlDsaOpt/NN/opt.hex MlDsaOptNN MlDsaOptNN optNN <2833 \| 2865>` | proved |
| `Layout.lean` | memory map (constants differing from 44), calldata offsets, `Entry`, `Stack`, spec-level data at `P = Params.mldsaNN`, `optAccepts`; shared 44 vocabulary re-exported (`export MlDsaOpt44.Proofs (…)`) | definitions |
| `Budget.lean` | subroutine budgets (`proofgen_gas_param.py NN --analyse`) | definitions |
| `Fn/*.lean` | contracts (see table) | 14 (65) / 14 (87) proved, rest **open** |
| `Math.lean` | spec facts: parameter-free ones proved via `MlDsa/Bridge44.lean`, the rest **open** | partly open |
| `Bridge.lean` | `pkLen_eq`, `sigLen_eq`, `finBytes_size`, `accepts_eq_optAccepts` proved (WP M1: `MlDsaOptNN/Math/M1/Verify.lean`; parametric helpers `MlDsaOpt65/Math/M1/{Row,Ball,Hint}.lean`, namespace `MlDsaOptM1`) | proved |
| `Main/Inv.lean`, `Main/Base.lean`, `Main/Frame.lean` | boundary invariants, segment budgets, frame transport (`avoids_tac`, `X.frame`) | definitions / proved |
| `Main/Seg*.lean` | one theorem per segment | **open** |
| `Main/Short.lean`, `Main/Valid.lean`, `Gas.lean`, `Main.lean` | short path, composition, schedule, final theorems | proved |

## Contracts

| contract | 65 | 87 | file | notes |
|---|---|---|---|---|
| kf4, kf1, blk, spr, trabs, cext, absorb17 | proved | proved | `Fn/{Keccak,Blk,Sponge}` | port, 44 statements |
| fix, gfix | proved | proved | `Fn/Fix` | port `--sub` BK; `gfix_call` has an extra conjunct: inactive ABUF lanes unchanged |
| ntt, intt | proved | proved | `Fn/Ntt` | `p = ZH ∨ p = ZH2`, `p = ACC ∨ p = ACC + 0x2000` |
| tbuild | proved | proved | `Fn/TBuild` | `[tp, off]` general |
| pass3 | proved | proved | `Fn/Group` | `[64k, zh, acc]` general |
| pass3m | — | proved | `Fn/Group` | |
| ginit | proved | proved | `Fn/Ginit/Call` | new `ginitWord` (`Fn/Group/Defs`); 25 lane blocks `Fn/Ginit/Lanes`, generated by `Fn/Ginit/gen_lanes.py NN` |
| group | proved | proved | `Fn/Group` | `[amask, col, rb]`; junk lanes `< 2^23`; `Fn/Group/{Prologue,Blocks,Main}` (`GroupP.g1_group_reach`) |
| dz, dhint | **open** | **open** | `Fn/Decode` | `g < 2` row group; `okZ_iff_zNormOk` open |
| sib | proved | proved | `Fn/Ball` | 65 stream from `CB` (44 proof over the parametric scan `MlDsaOptCommon/BallScan`); 87 squeezes H(c̃) with kf1 (`Fn/Ball/{Prologue,Stream}`) |
| csum | proved | proved | `Fn/Csum` | `g < 2`; τ unrolled loads, blocks generated by `Fn/Csum/gen_blocks.py NN`; `Math.csum_congr`, `Math.csum_lt` (all rows) proved in `Math/G4/` (generic core `MlDsaOpt65/Math/G4/CsumCore`) |
| usehint, pack | proved | proved | `Fn/Hint` | `γ2 = (q−1)/32`, 4-bit w1; `Fn/Hint/G5{UseHint,PackBlocks,Pack}` per set, pure part `MlDsaOpt65/Fn/Hint/G5Pure` (shared); `Math.useHint_emod/range`, `finBytes_le64_*` via `MlDsaOpt65/Math/G5/Hint` |
| mu0 | proved | — | `Fn/Mu0` | 44 code with `TRL` as PUSH3; port in `Fn/Mu0/` (`--sub` HDR, TRL, return pcs), `muBlock` in `Fn/Mu0/Defs` |
| pass3k14 | — | proved | `Fn/Pass3k14` | Kronecker group 14 (`kronWord14`); `Fn/Pass3k14/Proof` |

## Segments and gas

Boundaries and budgets (`proofgen_gas_param.py NN --schedule`; each `Gas.p*`
in `Main/Base.lean` is static glue plus the callees' budgets and equals the
script's longest static path). Every segment theorem is open.

**65**: init 0→992, zh →1110, tbl →3093, ntt →3115, rho →3565, g0–g4 →3578 →3592
→3606 →3620 →3634 (`group [15,col,0]`), g5 →4074, g6 →4517, g7 →5029, g8 →5221
(mixed row-group-1 groups: c̃ stream into `CB`, tr in slot 3, μ via `mu0`),
g9 →5236 (`group [3,4,1]`), mu →6545, sib →6555, ct →6610, w →6688, fin →RETURN.

**87**: init 0→992, zh →1126, sib →1135 (H(c̃) by kf1), tbl →3118, ntt →3140,
rho →3389, g0–g9 →3402 … →3530 (`group [15,col,rb]`), g10 →3963, g11 →4430,
g12 →4898, g13 →5435 (tr riders, `TRL` by `cext` in g13), g14 →5593
(Kronecker, `pass3k14`), mu →6591 (always kf1), ct →6646, w →6724, fin →RETURN.

**Schedules** (`Gas.schedule`, function of the calldata length; 37 for short
calldata):

| | `|M| = 0` | growth | adversarial worst case (`docs/opt.md`) | typical |
|---|---:|---|---:|---:|
| 65 | 5,549,448 (`|M| ≤ 69`); 5,660,598 (`70 ≤ |M| ≤ 205`) | +37,128 per 136 bytes | 5,350,581 | 3,930,640 |
| 87 | 8,249,418 | +37,128 per 136 bytes (`(66+|M|)/136`) | 8,014,074 | 5,478,088 |

Both are far below the 16.6M per-transaction budget. The gap to the measured
worst case is the conservative fix-up / SampleInBall / hint loop counts, as for 44.

## Work packages

Each WP owns the listed files for both sets (and may add helper files under
`MlDsaOptNN/Fn/<Name>/`, `MlDsaOptNN/Main/<Seg>/`, `MlDsaOptNN/Math/`).
**Do not change a contract or invariant statement without telling the
coordinator** — segments consume contracts, segments chain through `Main/Inv.lean`.
Contracts are independent of each other (stated, not proved, in terms of each
other), so contract WPs start at once; segment WPs can start against the
stated contracts. Port first: most 44 proofs carry over with
`scripts/proofgen_port.py` plus constant changes.

| WP | items (both sets unless noted) | template | difficulty |
|---|---|---|---|
| G1 group | `ginit_call`, `group_call`; 87 `pass3k14_call` | 44 `Fn/Sponge/Ginit`, `Fn/Group/{Main,Pass3k4}` | medium-hard |
| G2 decode | `dz_call`, `dhint_call`, `okZ_iff_zNormOk` | 44 `Fn/Decode/*` | medium |
| G3 ball | `sib_call` | 65: 44 `Fn/Ball/*`; 87: new | 65 easy, 87 hard |
| G4 csum | `csum_call`, `Math.csum_congr` | 44 `Fn/Ct/Csum*`, `Math/Csum` | medium |
| G5 hint | `usehint_call`, `pack_call`, `Math.useHint_emod/range`, `finBytes_le64_*` | 44 `Fn/Hint/*` | medium |
| G6 mu0 | 65 `mu0_call` | 44 `Fn/Sponge/Mu*` (port, `--sub` TRL) | easy |
| M1 math | `accepts_eq_optAccepts`, `sampleInBallOf_coeffs`, `hintBitUnpack_range`, `ntt_zLane` | 44 `Math/{BridgeMain,BridgeRow,Facts,SpecFacts}` | hard (k, ℓ, 4-bit w1) |
| S1 straight-line | `seg_init`, `seg_tbl`, `seg_rho`, `seg_fin` | 44 `Main/{Init,Tbl,Rho,Fin}` + `Main/Wp11Gen/*.py` | medium |
| S2 call segments | `seg_zh`, `seg_ntt`, `seg_sib`, `seg_ct`, `seg_w` | 44 `Main/Seg{Zh,Ntt,Sib,Ct,W}` | medium |
| S3 pure groups | 65 `seg_g0`–`g4`, `seg_g9`; 87 `seg_g0`–`g9` | 44 `Main/SegGroups` | easy-medium |
| S4 mixed 65 | `seg_g5`–`seg_g8` | 44 `Main/SegG234/*` | hard |
| S5 mixed 87 | `seg_g10`–`seg_g14` | 44 `Main/SegG234/*` | hard |
| S6 μ | `seg_mu` — **proved** (both sets, `Main/Mu/{Spec,Blocks,Proof}`: the 44 proof relocated) | 44 `Main/Mu/*` | medium |

### Guidance

* **G1.** `group_call`'s statement (`Fn/Group.lean`) uses `gOk cd amask col rb`
  and a `junk` lane `< 2^23` for inactive slots (the code always seeds with
  `AMULT = 15`, so an inactive slot runs row `4rb`'s instance: `GroupP.gRow`).
  `Fn/Group/{Seed,Squeeze}.lean` already prove the seed lemmas and the five
  squeezes. What remains is porting 44 `Fn/Group/Main.lean`: 65 pcs 14256,
  11644, 14359 + 22b, 20991, 9857, 14469, 11314, 14478, 11032, 14512, 14520
  (indices = 44 + 223); 87 pcs 15099, 12945, 15202 + 22b, 21922, 10772, 15312,
  12615, 15321, 11947, 15355, 15363 (indices = 65 + 423). A first attempt did not
  elaborate in 15 min: elaborate block by block; do not put `gL4` in the simp set
  of the symbolic prologue (close the leftover by `rfl` / `gL4_eq`); case-split
  the symbolic pointer arithmetic (`rb <<< 13`, `col >>> 2`, `col &&& 3`) with
  `interval_cases`. `ginit` differs from 44 (RHO1 moved; 65 seeds carry the
  48-byte c̃); `ginitWord` is in `Fn/Group/Defs.lean`.
* **G2.** dz: 20-bit fields, 640 bytes per polynomial, two calls
  (`g = 0, 1`); the second reads past the last polynomial (lanes of polys `≥ ℓ`
  are stated as `zLane` of the bytes there). The flag is per lane
  (`zFlagBit j`); the zh segment masks the second flag word. dhint: k rows, ω.
* **G3.** 87 `sib_call` needs the absorb prologue as `KS1` of the padded c̃
  state, two `kf1_call`s (prologue and refill at position 136), and a lemma that
  the two squeezes are `cStream`; the budget charges the refill once.
* **G4/G5.** Pointer arguments are row-group parametric (`g < 2`); `usehint`
  also states an unconditional `lane < 16` (pack needs it for 65's rows 6, 7).
* **M1.** Port `BridgeMain`/`BridgeRow`: NTT and convolution lemmas are
  parameter-free (`MlDsa/Bridge44.lean` equates `MlDsa.Fips204.ntt`, `nttInv`,
  `rejNTTPoly`, `H`, … with the 44 functions). Flag order: 65
  `((okZ ∧ okH) ∧ okA) ∧ okC`, 87 `((okZ ∧ okH) ∧ okC) ∧ okA`; c̃ is 48 / 64 bytes.
* **S1.** Regenerate the 44 `Main/Wp11Gen` scripts for the 65/87 listings
  (RC tables and NTT records are identical; pcs/indices differ); rho: 65 has 4 ρ
  + 6 c̃ lanes (10 `spr`), 87 4 ρ lanes; fin: 6 (65) / 8 (87) loop visits,
  48 / 64-byte compare.
* **S3–S5.** 65 `AccCols1` bounds the junk lanes 2, 3 of `ACC + 0x2000` (rows 6,
  7 do not exist) by `n · 2^51`; `intt` needs every lane `< 2^58`. Groups 5–8
  (65) and 10–13 (87) carry tr in slot 3 (`TrSlot`), 65 g5 writes the c̃ stream
  into `CB` (`cext 17` ×2), 65 g8 absorbs μ for `|M| ≤ 69` (`mu0`), 87 g13 extracts
  `TRL`, 87 g14 is the Kronecker group.

## Pitfalls (in addition to `MlDsaOpt44/PLAN.md`)

* Shared vocabulary is re-exported from `MlDsaOpt44.Proofs`; inside
  `MlDsaOptNN.Proofs` a 65/87 name shadows the 44 one, and a missing 65/87 name
  silently falls back to the 44 constant if the file opens `MlDsaOpt44.Proofs`
  (ported files do). Check addresses in statements you write.
* Dot notation on re-exported constants does not find 65/87 lemmas
  (`hz.frame` for `ZeroOn` resolves in the 44 namespace): apply `ZeroOn.frame` explicitly.
* The port rewrites only the contexts listed above; numbers it did not
  relocate are printed as `CHECK` lines — read them. Data values equal to a 44
  JUMPDEST in `wd N` are relocated wrongly (reported); keep data symbolic.
* `padPk` exists in `MlDsaOpt87.Proofs` (`Main/Inv.lean`) and in 44's
  `Main/SegG234/G2.lean`: opening `MlDsaOpt44.Proofs` with that module imported
  makes it ambiguous.
* Block timings differ slightly per artifact: ported files set `maxHeartbeats 0`.
