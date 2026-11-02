# MlDsaOpt: gas-optimised ML-DSA-44/65/87 verifiers

This directory holds generated artifacts; do not edit them. Regenerate with
`python3 scripts/gen_opt.py` (v4, current and formally verified, in `NN/`),
`python3 scripts/gen_opt.py --version v3` (`NN/v3/`) and `--version v2`
(`NN/v2/`); both earlier versions were also proved. The proofs of the v4 bytes
are `MlDsaOpt44/`, `MlDsaOpt65/`, `MlDsaOpt87/`. Design, gas log, profiles,
validation, floor analysis and proof plan are in `docs/opt.md`.

| file | content |
|---|---|
| `NN/opt.hex` | runtime bytecode (EIP-8355: calldata pk ‖ σ ‖ M, returns the 32-byte word 1 iff FIPS 204 Verify accepts with empty context) |
| `NN/opt.asm` | readable intermediate form: annotated listing (pc, mnemonic, immediate, subroutine, generator comments) |
| `NN/layout.txt` | subroutine pc ranges, memory map, SIMD slot schedule |
| `NN/v3/` | the same three files for v3 (round 3, proved before v4; `gen_opt.py --version v3`) |
| `NN/v2/` | the same three files for v2 (proved first; git tag `opt-v2-proved`) |
| `NN/glam/` | Glamsterdam prototype (EIP-8024 DUPN/SWAPN, EIP-7954 64 KiB code), not proved: v4 with stack-resident Keccak kernels, `scripts/gen_glam.py`, see `docs/glam.md` |

Gas for a valid signature over an empty message, frame gas as measured by
`mldsa44tool run-file` and foundry's GasProbe (v4: `docs/opt.md`, "Round 4 (v4)"):

| set | **v4 (proved) gas** | v4 worst case | v4 size | v3 gas | v3 size | v2 gas | v2 size | reference |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 44 | **1,929,359** | 2,580,497 | 24,089 B | 2,105,097 | 23,091 B | 2,136,608 | 22,553 B | 12,953,021 |
| 65 | **3,509,486** | 4,610,258 | 24,049 B | 3,701,979 | 23,422 B | 3,930,640 | 22,512 B | 21,334,964 |
| 87 | **5,227,912** | 7,261,604 | 23,798 B | 5,424,737 | 23,982 B | 5,478,088 | 23,443 B | 35,708,719 |

44 v4 includes the R4-8 fix (SampleInBall's fail exit clears BASES; 24,089 B,
SHA-256 `8f90565e…`; the full hashes of all three sets are pinned in
`scripts/opt_selftest.py`, `V4_SHA256`). For 65, v4 computes μ in a SIMD slot
for messages up to 613 bytes; 44 squeezes μ's first block in a slot and
continues on kf1 from |M| = 70 (R4-7).

There is no Yul source. Every component is hand-written bytecode generated
from Python (`scripts/gen_opt.py`, `opt_keccak.py`, `opt_ntt.py`,
`opt_asm.py`); `docs/opt.md` explains why. Only opcodes supported by
`EvmProof/Stepper.lean` are used.
