# 959ed80 vs. 5c698bb / 21ea039, one orb

All numbers come from one a1.3xlarge orb (16 vCPU, 43 GB, Lean 4.33.0), measured
1–2 Nov 2026 (UTC). Every run started with the 1-minute load below 1.0, and
nothing else ran on the orb during a run.

The orb's speed drifted during the session: 959ed80 clean builds took
976–1,089 s in the evening (rounds 1–4) and 716–813 s after midnight
(rounds 5–7). Compare each "after" run with the 959ed80 run next to it, not
across the session.

## Per module (`time_modules.py --jobs 1`)

`module-times-959ed80.tsv` (here) and `module-times-5c698bb.tsv` were run 26
minutes apart; the only work in between was one clean build of each commit. EvmProof is the same code in
both and sums to 48.4 s vs. 48.7 s, so the two tables compare directly.
`../module-times-959ed80.tsv` was taken earlier on the faster orb (6,197 s) and
does not compare with these.

| | 959ed80 | 5c698bb | Change |
|---|---|---|---|
| Modules | 579 | 588 | +9 |
| Σ wall | 7,257 s | 3,926 s | −46% |
| Σ CPU | 8,760 s | 5,024 s | −43% |
| Max RSS | 4,649 MB | 4,952 MB | +7% |
| Nonzero exit | 0 | 0 | |

| Library | Σ wall 959ed80 | Σ wall 5c698bb | Change |
|---|---|---|---|
| MlDsaOpt87 | 2,266 | 994 | −56% |
| MlDsaOpt65 | 2,269 | 1,077 | −53% |
| MlDsaOpt44 | 2,086 | 1,257 | −40% |
| MlDsa44 | 562 | 508 | −10% |
| MlDsaOptCommon | 15 | 31 | +5 modules |
| EvmProof | 48 | 49 | |
| MlDsa, MlDsa65, MlDsa87 | 10 | 10 | |

The biggest per-module gains are the reflected blocks: Sponge.Trabs (×3)
122–127 → 21–25 s and Blk.BodyA (×3) 92–99 → 14–17 s. Fix.Blocks, Fix.GBlocks,
Csum.Blocks, Ball.Blocks, Mu0.MuBlocks and Kf4.Blocks2 each fell from 53–70 s
to 9–17 s. Opt87 Decode.HintBlocks fell 95 → 37 s and S1.Tbl (65/87) 83/89 →
40/39 s.

Regressions above 1 s: Opt44 Fn.Blk.Mem (19.1 → 25.1 s), Infra.Code
(34.8 → 38.9), Artifact (19.8 → 23.8), Group.Pass3/Pass3m (10.8/11.9 →
14.3/14.8), and about twenty-five modules at +1–2 s (mostly MlDsa44.Proofs). Most
small modules got 0.2–0.5 s slower, consistent with the added imports.

## Clean builds (`clean-builds.tsv`)

Each run used a fresh worktree with `.lake/build` and `.lake/config` removed,
`.lake/packages` copied from a set-up checkout, then
`/usr/bin/time -v lake build` of all default targets. Rows are in run order.

| Pair | 959ed80 wall / CPU | After wall / CPU | Ratio wall / CPU |
|---|---|---|---|
| 4f25d96 r1 vs. 959ed80 r1 | 976 / 11,069 | 712 / 8,637 | 0.73 / 0.78 |
| 4f25d96 r2 vs. 959ed80 r2 | 995 / 11,514 | 775 / 9,253 | 0.78 / 0.80 |
| e3d6f39 r1 vs. 959ed80 r3 | 1,025 / 11,885 | 814 / 9,816 | 0.79 / 0.83 |
| 6c266c7 r1 vs. 959ed80 r3 | 1,025 / 11,885 | 736 / 8,625 | 0.72 / 0.73 |
| 6c266c7 r2 vs. 959ed80 r4 | 1,089 / 12,472 | 688 / 7,999 | 0.63 / 0.64 |
| 5c698bb r1 vs. 959ed80 r5 | 813 / 9,209 | 493 / 5,665 | 0.61 / 0.62 |
| 5c698bb r2 vs. 959ed80 r6 | 744 / 8,355 | 481 / 5,506 | 0.65 / 0.66 |
| 21ea039 r1 vs. 959ed80 r7 | 716 / 8,104 | 303 / 4,051 | 0.42 / 0.50 |

Max RSS was 4.5–4.9 GiB for every build except 21ea039 (3.44 GiB).

`.olean` bytes under `.lake/build/lib` after a clean build:

| Commit | .olean |
|---|---|
| 959ed80 | 4,485 MB |
| 4f25d96 | 4,690 MB |
| e3d6f39 | 4,453 MB |
| 6c266c7 | 3,849 MB |
| 5c698bb | 1,666 MB |
| 21ea039 | 1,523 MB |
