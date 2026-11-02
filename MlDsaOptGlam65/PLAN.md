# Glamsterdam ML-DSA-65 (`MlDsaOpt/65/glam/opt.hex`): proof status

The four final theorems (`Main.lean`) are stated over `MlDsa65.Amsterdam`
(`MlDsa65/SpecAmsterdam.lean`) for `MlDsaOptGlam65.optBytecode`.

## Status: closed (no open items)

`checks/Axioms.lean`: no direct `sorry`; the final theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`. ExpandA (`seg_exp`, the 42-call schedule `Layout.PACK65`)
is `Main/Exp/*` (package 4) with exact `Gas.pExp = 3,082,145`; μ (`seg_mu`, the state image
at `MUIMG`) has the exact `Gas.pMu`. `mub` is unreachable in glam 65 and has no contract.

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
| `Main/Exp/G/Grp{3,4,5,6}` | `Main/Exp/G/gen.py N` (stdout) |
| the rest | hand-written: `Layout`, `Budget`, `Gas`, `Main.lean`, `Main/{SegExp,SegMu}`, `Main/Exp/*`, `Main/Mu/*`, `Main/S1/{Init,Tbl}`, `Fn/Pack65*`, `Fn/Pass3f/Defs`, the `Fn` wrappers |
