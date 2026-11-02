# Glamsterdam ML-DSA-65 (`MlDsaOpt/65/glam/opt.hex`): proof status

The four final theorems (`Main.lean`) are stated over `MlDsa65.Amsterdam`
(`MlDsa65/SpecAmsterdam.lean`) for `MlDsaOptGlam65.optBytecode`.

## Status: retargeted, with open items (`checks/Axioms.lean`)

| item | code | package |
|---|---|---|
| `seg_exp` | ExpandA, the 42-call schedule (`Layout.PACK65`), `Gas.pExp` provisional | 4 |
| `seg_mu` | `hash_mu` (restores μ's state image at `0x15040`), `Gas.pMu` | 4 |
| `WP4.mub_call_aux` | `mub` (unreachable in glam 65; removed with package 4) | 4 |

Proved: the kernels, `blk`/`blkh`/`blkt`, `ntt`, `intt` (UseHint fused), `dz`, `csum`,
`kmove`, `lmerge`, `pass3f7`, `pass3f8` (`Fn/Pack65.lean`), every ported routine and
segment, and the composition.

## How the tree is made

| files | made by |
|---|---|
| `Bytecode`, `Artifact`, `Infra/*`, `listing.tsv` | `scripts/proofgen_artifact_glam.py` |
| `Fn/Kf4/*`, `Fn/Kf1/*` | `MlDsaOptGlam44/Fn/{Kf4,Kf1}/gen_*.py 65` |
| `Fn/Blk/{Iters,Glue,Proof}`, `Fn/Ntt/{FwdA,FwdB,Ctl,Passes,Top}` | `MlDsaOptGlam44/Fn/Blk/gen.py 65`, `MlDsaOptGlam44/Fn/Ntt/gen_nttg.py 65` |
| `Fn/Ntt/{Inv1,Inv2,InvCtl,InvTop}` | `Fn/Ntt/gen_inttg.py 65` |
| `Fn/Decode/Z4G{Blocks,Loop}` | `MlDsaOptGlam44/Fn/Decode/gen_dz.py 65` |
| `Fn/Csum/{Blocks,Iter}` | `MlDsaOptGlam44/Fn/Ct/gen_csum.py 65` (all τ = 49 bases on the stack) |
| the ported v4 65 files | `port.py` (`proofgen_port.py --glam 65` and the recorded adjustments) |
| the rest | hand-written: `Layout`, `Budget`, `Gas`, `Main.lean`, `Main/{SegExp,SegMu}`, `Main/S1/{Init,Tbl}`, `Fn/Pack65*`, `Fn/Pass3f/Defs`, the `Fn` wrappers |
