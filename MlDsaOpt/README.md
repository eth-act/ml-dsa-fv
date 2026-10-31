# MlDsaOpt: gas-optimised ML-DSA-44/65/87 verifiers

This directory holds generated artifacts; do not edit them. Regenerate with
`python3 scripts/gen_opt.py`. Design, gas log, profiles, validation, floor
analysis and proof plan are in `docs/opt.md`.

| file | content |
|---|---|
| `NN/opt.hex` | runtime bytecode (EIP-8355: calldata pk ‖ σ ‖ M, returns the 32-byte word 1 iff FIPS 204 Verify accepts with empty context) |
| `NN/opt.asm` | readable intermediate form: annotated listing (pc, mnemonic, immediate, subroutine, generator comments) |
| `NN/layout.txt` | subroutine pc ranges, memory map, SIMD slot schedule |

Gas for a valid signature over an empty message, frame gas as measured by
`mldsa44tool run-file` and foundry's GasProbe:

| set | gas | reference | code size |
|---|---:|---:|---:|
| 44 | 2,184,320 | 12,953,021 | 23,109 B |
| 65 | 3,993,518 | 21,334,964 | 23,312 B |
| 87 | 5,514,373 | 35,708,719 | 23,882 B |

There is no Yul source. Every component is hand-written bytecode generated
from Python (`scripts/gen_opt.py`, `opt_keccak.py`, `opt_ntt.py`,
`opt_asm.py`); `docs/opt.md` explains why. Only opcodes supported by
`EvmProof/Stepper.lean` are used.
