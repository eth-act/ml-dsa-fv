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

| set | gas | worst case | reference | code size |
|---|---:|---:|---:|---:|
| 44 | 2,136,608 | 2,895,812 | 12,953,021 | 22,553 B |
| 65 | 3,930,640 | 5,350,581 | 21,334,964 | 22,512 B |
| 87 | 5,478,088 | 8,014,074 | 35,708,719 | 23,443 B |

There is no Yul source. Every component is hand-written bytecode generated
from Python (`scripts/gen_opt.py`, `opt_keccak.py`, `opt_ntt.py`,
`opt_asm.py`); `docs/opt.md` explains why. Only opcodes supported by
`EvmProof/Stepper.lean` are used.
