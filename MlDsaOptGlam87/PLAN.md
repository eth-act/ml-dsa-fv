# Glamsterdam ML-DSA-87 (`MlDsaOpt/87/glam/opt.hex`): proof status

The four final theorems (`Main.lean`: `opt_correct`, `opt_correctWithSchedule`,
`opt_correctInAnyContext`, `opt_correctInAnyContextWithSchedule`) are stated over
`MlDsa87.Amsterdam` (`MlDsa87/SpecAmsterdam.lean`, `MlDsa/Spec/InterfaceAmsterdam.lean`:
`MlDsa87.Spec` on the `Amsterdam` fork) for `MlDsaOptGlam87.optBytecode`.

## Status: closed (no open items)

`checks/Axioms.lean`: no direct `sorry`; the final theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`. The public schedule is
`schedule (7219 + n) = 6,614,433 + ⌊(66 + n) / 136⌋ · 27,175` (`Gas.schedule_msg`).

## How the tree is made

| files | made by |
|---|---|
| `Bytecode`, `Artifact`, `Infra/*`, `listing.tsv` | `scripts/proofgen_artifact_glam.py` |
| `Fn/Kf4/*`, `Fn/Kf1/*` | `MlDsaOptGlam44/Fn/{Kf4,Kf1}/gen_*.py 87` |
| `Fn/Blk/{Iters,Glue,Proof}`, `Fn/Ntt/{FwdA,FwdB,Ctl,Passes,Top}` | `MlDsaOptGlam44/Fn/Blk/gen.py 87`, `MlDsaOptGlam44/Fn/Ntt/gen_nttg.py 87` |
| `Fn/Ntt/{Inv1,Inv2,InvCtl,InvTop}` | `MlDsaOptGlam65/Fn/Ntt/gen_inttg.py 87` (UseHint fused, as v4 65) |
| `Fn/Decode/Z4G{Blocks,Loop}` | `MlDsaOptGlam44/Fn/Decode/gen_dz.py 87` |
| `Fn/Csum/{Blocks,Iter}` | `MlDsaOptGlam44/Fn/Ct/gen_csum.py 87` (all τ = 60 bases on the stack) |
| the ported v4 87 files | `port.py` (`proofgen_port.py --glam 87` and the recorded adjustments) |
| the rest | hand-written: `Layout`, `Budget`, `Gas`, `Main.lean`, `Main/SegW.lean` (no `usehint` call), `Main/S1/{Init,Tbl}`, the `Fn` wrappers |

The gate reproduces every generator and the port.
