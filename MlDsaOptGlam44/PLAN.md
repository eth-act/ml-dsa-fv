# MlDsaOptGlam44: proof plan

Target: `MlDsaOpt/44/glam/opt.hex` (57,649 bytes, 34,557 instructions, memory
2616 words; `docs/glam.md`), the v4 verifier with Glamsterdam-only changes,
on the `Amsterdam` fork of the patched semantics (EIP-8024 `DUPN` / `SWAPN` /
`EXCHANGE`, EIP-7954; `deps/README.md`, `EvmProof/Amsterdam.lean`). The final
theorems in `Main.lean` are the four of v4 stated over `MlDsa44.Amsterdam`
(`MlDsa44/SpecAmsterdam.lean`: `MlDsa44.Spec` with only the fork changed).
`checks/Axioms.lean` prints their axioms and lists the open items.

## How the tree is made

| part | source |
|---|---|
| `Bytecode`, `Artifact`, `Infra/*`, `listing.tsv` | `scripts/proofgen_artifact_glam.py MlDsaOpt/44/glam/opt.hex MlDsaOptGlam44 MlDsaOptGlam44 glam44 2616` (`EvmProof.XInstr` paths, `glam44_rreach`) |
| `Fn/Kf4/*`, `Fn/Kf1/*` | `Fn/Kf4/gen_kf4.py 44`, `Fn/Kf1/gen_kf1.py 44` (the stack-resident kernels; 65 and 87 share `Model` / `Algebra`) |
| every v4 proof of unchanged code | `python3 MlDsaOptGlam44/port.py`: `scripts/proofgen_port.py --glam 44` on the files listed there (index and pc maps v4 → glam, region by region; `opt44_reach` → `glam44_rreach`) and the recorded adjustments |
| the rest | hand-written: `Layout` (entries, 74-slot stack leaf, `RC4Table` / `RC1Table` trivial, the 4 + 4 `TblAt`, `FLAG`), `Budget`, `Gas`, `Main.lean`, `Main/{Base,Valid,SegMu,SegSwitch}`, `Main/{Init,Tbl}/*`, the `Fn` wrappers `Keccak`, `Blk`, `Ntt`, `Decode`, `Ct`, `Ball` |

Pure v4 modules (models, spec facts, `Defs`) are imported, not copied, so the
v4 lemmas apply to the same definitions. All three generators and the port are
reproduced by the gate.

## Status: retargeted, with open items

Proved: the kernels (`kf4_spec`, `kf1_spec`), every ported routine (`fix`,
`gfix`, `group`, `pass3f4`, `ginit`, `trabs`, `cext`, `absorb17`, `mub0`,
`kmove`, `lmerge`, `spr`, `tbuild`, `pack`, `dhint`), the main flow up to the
long-message switch and the packed schedule's segments (`|M| < 342`), the
shared tail (`tbuild` / `csum`, `intt` / `pack`, the final hash), the short
path, and the composition into the final theorems.

Open (`#open_items`, 10 declarations):

| item | code | notes |
|---|---|---|
| `blk_call`, `blkh_call`, `blkt_call` | `blk` | fully unrolled, immediate lane addresses, un-complemented on load; v4's bit lemmas (`Fn/Blk/Bits`) apply |
| `ntt_call`, `intt_call` | `ntt`, `intt` | 4 + 4 passes, 16 words on the stack, table `TblAt` (`nttRecG`); v4's per-layer bounds and butterflies apply |
| `dz_call` | `dz` | gather loop unrolled per chunk |
| `csum_call` | `csum` | all τ bases on the stack (DUPN) |
| `sib_call` | `sample_in_ball` | two loop copies (the first stops at block 1's end, where c's 2nd block is squeezed from `SC` if `FLAG = 1`); contract as v4's with `FLAG = 1`; `Gas.sib` to re-derive |
| `seg_mu` | `hash_mu` + dispatch | v4's proof plus four blocks reading `FLAG` (`Gas.pMu`: +17 / +73) |
| `seg_alt` | `alt` … `altj`, `mulong`, `pass3f4b`, the tail with `FLAG = 0` | the long-message schedule; `Gas.pAlt` is a provisional bound (`Gas.lean`) |

```sh
export TMPDIR=$PWD/.lake/tmp
lake build MlDsaOptGlam44
lake env lean MlDsaOptGlam44/checks/Axioms.lean
python3 MlDsaOptGlam44/port.py && git status --short MlDsaOptGlam44   # reproduces the ported files
```
