# MlDsaOpt: gas-optimised ML-DSA-44/65/87 verifiers

This directory holds generated artifacts; do not edit them. Regenerate with
`python3 scripts/gen_opt.py` (v3, current) and `python3 scripts/gen_opt.py
--version v2` (the formally verified bytes, in `NN/v2/`, proved in
`MlDsaOpt44/`, `MlDsaOpt65/`, `MlDsaOpt87/`). Design, gas log, profiles, validation, floor
analysis and proof plan are in `docs/opt.md`.

| file | content |
|---|---|
| `NN/opt.hex` | runtime bytecode (EIP-8355: calldata pk ‖ σ ‖ M, returns the 32-byte word 1 iff FIPS 204 Verify accepts with empty context) |
| `NN/opt.asm` | readable intermediate form: annotated listing (pc, mnemonic, immediate, subroutine, generator comments) |
| `NN/layout.txt` | subroutine pc ranges, memory map, SIMD slot schedule |
| `NN/v2/` | the same three files for v2 (the proved bytes) |
| `NN/v4/` | the same three files for v4 (round 4, not yet proved; `gen_opt.py --version v4`) |

Gas for a valid signature over an empty message, frame gas as measured by
`mldsa44tool run-file` and foundry's GasProbe:

| set | v3 gas | v3 worst case | v3 size | v2 (proved) gas | v2 size | reference |
|---|---:|---:|---:|---:|---:|---:|
| 44 | 2,105,097 | 2,864,301 | 23,091 B | 2,136,608 | 22,553 B | 12,953,021 |
| 65 | 3,701,979 | 5,073,355 | 23,422 B | 3,930,640 | 22,512 B | 21,334,964 |
| 87 | 5,424,737 | 7,954,105 | 23,982 B | 5,478,088 | 23,443 B | 35,708,719 |

v4 (round 4, `NN/v4/`, not yet proved; see "Round 4 (v4)" in `docs/opt.md`):

| set | v4 gas | v4 worst case | v4 size |
|---|---:|---:|---:|
| 44 | 2,042,346 | 2,809,039 | 22,546 B |
| 65 | 3,564,626 | 4,947,325 | 23,219 B |
| 87 | 5,271,542 | 7,823,331 | 23,941 B |

There is no Yul source. Every component is hand-written bytecode generated
from Python (`scripts/gen_opt.py`, `opt_keccak.py`, `opt_ntt.py`,
`opt_asm.py`); `docs/opt.md` explains why. Only opcodes supported by
`EvmProof/Stepper.lean` are used.
