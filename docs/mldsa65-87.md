# ML-DSA-65 and ML-DSA-87: phase A

Phase A extends the ML-DSA-44 artifact to the other two FIPS 204 parameter
sets. It covers the trusted specification, test vectors, a proof-friendly
reference implementation, and gas measurements. Phase A contains no bytecode
proofs. Those come after the gas-optimized ML-DSA-44 design lands, so that the
65/87 proofs are written once, against the final design.

| Item | Status |
|---|---|
| Parametric FIPS 204 spec + EIP-8355 statements for 65/87 | `lake build MlDsa MlDsa65 MlDsa87` builds; no `sorry`, `native_decide` or axioms |
| Anchor to the audited 44 spec | **Fully proved.** `verify`, `accepts`, `spec` and all five statements are equal at `Params.mldsa44` (axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Spec vs vectors | 44: ACVP 30/30, calldata 47/47 (also equal to `MlDsa44.spec`); 65: 30/30, 57/57; 87: 30/30, 57/57 |
| Reference bytecode | 65: 5302 bytes, 87: 5303 bytes (limit 24576); all 57 + 57 vectors pass in the Lean EVM semantics |
| Gas vs the 2^24 = 16,777,216 transaction cap | **Neither fits.** 65: 21.33M (127% of the cap); 87: 35.71M (213%), both for an empty message |

## Files

| Path | Role |
|---|---|
| `MlDsa/Spec/Params.lean` | `Params` (k, ℓ, η, τ, λ, γ₁, γ₂, ω), `beta`, the three Table 1 instances (**trusted**) |
| `MlDsa/Spec/Fips204.lean` | FIPS 204 verification, parametric in `P : Params`; Table 2 sizes and Table 3 limits checked by `decide` (**trusted**) |
| `MlDsa/Spec/Interface.lean` | EIP-8355 `accepts`/`spec`, `initialState`, `Correct`, `CorrectWithSchedule`, `FrameEntry`, `CorrectInAnyContextWithSchedule`, `CorrectInAnyContext`, parametric in `P` and the deployment address (**trusted**) |
| `MlDsa65/Spec.lean`, `MlDsa87/Spec.lean` | The audit statement per set: `Params.mldsa65`/`mldsa87`, deployment addresses `0x8213`/`0x8214`, the same names as `MlDsa44.Spec` (**trusted**) |
| `MlDsa/Bridge44.lean` | Proof that the parametric spec at `Params.mldsa44` is `MlDsa44.Fips204`/`MlDsa44.Spec` (not trusted) |
| `MlDsaTool.lean` (`mldsatool`) | `spec NN`, `run NN HEX`, `profile NN HEX YUL ROW` |
| `scripts/gen_vectors_param.py` | Vectors for 44/65/87; for 44 the output is byte-identical to `vectors/*.txt` |
| `scripts/gen_reference_param.py` | Reference Yul for 44/65/87; for 44 the output is byte-identical to `MlDsa44/Reference/reference.yul` |
| `vectors/mldsa65/`, `vectors/mldsa87/` | `acvp_internal.txt` (30 rows each), `calldata.txt` (57 rows each) |
| `MlDsa65/Reference/`, `MlDsa87/Reference/` | `reference.yul`, `reference.hex` |

Nothing under `MlDsa44/`, `EvmProof/` or `vectors/*.txt` was changed.

```sh
export TMPDIR=$PWD/.lake/tmp
lake build MlDsa MlDsa65 MlDsa87 mldsatool
for n in 44 65 87; do .lake/build/bin/mldsatool spec $n; done
PYTHONPATH=.ref/pylib python3 scripts/gen_vectors_param.py 65 .ref/acvp_sigver.json vectors/mldsa65
python3 scripts/gen_reference_param.py 65 > MlDsa65/Reference/reference.yul
.lake/build/bin/mldsa44tool compile MlDsa65/Reference/reference.yul MlDsa65/Reference/reference.hex
.lake/build/bin/mldsatool run 65 MlDsa65/Reference/reference.hex
.lake/build/bin/mldsatool profile 65 MlDsa65/Reference/reference.hex MlDsa65/Reference/reference.yul 1
```

## Specification

### What is shared

There is one FIPS 204 transcription for all three sets. `MlDsa.Fips204` is
`MlDsa44.Fips204` with each per-set constant replaced by a field of `P`. The
following parts are textually unchanged:

* the constants `q`, `ζ`, `d`, `bitlen`;
* H and G, which reuse `MlDsa44.Fips202`;
* `bit`, `bitsToInteger`, `coeffFromThreeBytes`, `simpleBitPack`,
  `simpleBitUnpack`, `bitUnpack`;
* the bounded samplers `sampleIndex` and `rejNTTPolyOf`/`rejNTTPoly`;
* `modPm`, `bitRev8`, `zetas`, `ntt`, `nttInv`, `addNTT`, `multiplyNTT` and
  `normBelow`.

The functions that take `P` are `pkLen`, `sigLen`, `hintBitUnpack`,
`pkDecode`, `sigDecode`, `w1Encode`, `sampleInBallOf`/`sampleInBall`,
`expandA`, `decompose`, `useHint`, `matrixVectorNTT`, `verifyInternal` and
`verify`.

The 44 spec was already written in terms of its named constants, and every
derived quantity is the FIPS formula. Generalizing it therefore needed no
algorithmic change.

The Appendix C limits are the same for all sets. Table 3 gives one minimum
per algorithm: 894 bytes of G and 221 bytes of H, where 221 is computed for
the largest τ = 60. `rejNTTPolyLimit = 1008` and `sampleInBallLimit = 272`
therefore serve all three sets. RejBoundedPoly is used only when signing.
`τ ≤ 64` keeps the sign bits inside the first 8 bytes of H, and this is
checked by `decide`.

### What differs (Table 1 and derived values)

| | 44 | 65 | 87 |
|---|---:|---:|---:|
| (k, ℓ) | (4, 4) | (6, 5) | (8, 7) |
| η, τ, β = τη | 2, 39, 78 | 4, 49, 196 | 2, 60, 120 |
| λ, \|c̃\| = λ/4 | 128, 32 | 192, 48 | 256, 64 |
| γ₁; z width bitlen(γ₁−1)+1; z bytes/poly | 2¹⁷; 18; 576 | 2¹⁹; 20; 640 | 2¹⁹; 20; 640 |
| γ₂; 2γ₂; m = (q−1)/2γ₂ | (q−1)/88; 190464; 44 | (q−1)/32; 523776; 16 | (q−1)/32; 523776; 16 |
| w1Encode bits/coeff (bitlen(m−1)); bytes | 6; 768 | 4; 768 | 4; 1024 |
| ω | 80 | 55 | 75 |
| \|pk\|, \|σ\|, minimum calldata | 1312, 2420, 3732 | 1952, 3309, 5261 | 2592, 4627, 7219 |

SampleInBall is seeded with the whole c̃ ∈ 𝔹^{λ/4} (Algorithm 29 input and
Algorithm 8 line 8 of the final standard), not with its first 32 bytes as in
round-3 Dilithium. The ACVP sigVer rows confirm this choice: their valid
65/87 signatures would fail under a 32-byte seed. dilithium-py 1.4.0 makes the
same choice.

### Statements

`MlDsa.Interface` contains the five definitions of `MlDsa44.Spec`, word for
word, parametric in `P` and `deployAddress`. `FrameEntry`,
`CorrectInAnyContextWithSchedule` and `CorrectInAnyContext` do not depend on
the address. `MlDsa65.Spec` and `MlDsa87.Spec` instantiate them and keep the
names of the 44 file, so the proof phase can state, for example,
`MlDsa65.CorrectInAnyContextWithSchedule referenceBytecode Gas.schedule`.

### Anchor to the audited 44 spec (`MlDsa/Bridge44.lean`)

The following are proved for all inputs:

* `verify_eq`: `Fips204.verify .mldsa44 = MlDsa44.Fips204.verify`, and the
  same for `verifyInternal` and for every algorithm;
* `accepts_eq`, `spec_eq` and `initialState_eq` (at `0x8212`);
* `correct_iff`, `correctWithSchedule_iff`,
  `correctInAnyContextWithSchedule_iff` and `correctInAnyContext_iff`.

The existing proofs therefore already establish the parametric statements at
`Params.mldsa44`. The spec audit in `docs/spec-review.md` transfers to every
line of `MlDsa.Fips204` that does not mention `P`.

The proof technique matters if the bridge is ever extended. Plain `rfl`
between the two unfolded transcriptions does not work. Their `match`
auxiliaries are distinct constants (for example
`rejNTTPolyOf.match_1`), and `simp` does not rewrite constants inside
`Decidable` instance arguments. A first-order mismatch then makes the unifier
and the kernel unfold the bounded XOF loops, which exhausted 12 GB. The
`bridge` tactic avoids this. It `delta`-unfolds both sides, `rw`s every
constant and matcher to its twin (`rw` reaches instance arguments), and
closes with reducible `rfl`. The whole file checks in about 5 s.

## Vectors

`scripts/gen_vectors_param.py NN` writes two files:

* `acvp_internal.txt`: every ML-DSA-NN ACVP sigVer row that is usable by
  `verifyInternal`. These are the external/pure rows with
  M' = 0 ‖ |ctx| ‖ ctx ‖ M, and the internal rows without external μ: 15 + 15
  rows, 6 of them valid.
* `calldata.txt`: EIP-8355 calldata rows with the FIPS verdict:
  * dilithium-py signatures for message lengths 0, 1, 31, 32, 69, 70, 71,
    135, 136, 137, 205, 206, 207 and 1000. These include the μ-block
    boundaries at 70 and 206 (66 + n crossing 136), the message-copy
    boundaries at 31 and 32, and the 1000-byte case;
  * flipped c̃, z, t1 and ρ, and an extended message;
  * z = γ₁, z = ±(γ₁ − β) (rejected: the norm check is strict) and
    z = ±(γ₁ − β − 1) (passes the norm check, then fails);
  * a hint count above ω, a last hint count equal to ω, decreasing counts, a
    repeated index (dilithium-py accepts it; FIPS Algorithm 21 rejects it),
    decreasing indices and nonzero padding;
  * flipped last c̃ byte (a byte that only affects SampleInBall's seed
    beyond 32 bytes), last t1 byte and last z byte;
  * the valid base signature;
  * the single ACVP external/pure row with an empty context;
  * one byte short and empty calldata.

Every malformed row with a full-length pk and σ is cross-checked against
dilithium-py. The two must agree, except where the strict Algorithm 21
transcription in the script rejects a hint that dilithium-py accepts.

## Reference implementation

`scripts/gen_reference_param.py` builds the 65/87 Yul from the 44 generator's
template. It replaces 34 fragments, listed in `SLOTS` with their expected
occurrence counts, by placeholders. It then asserts that no ML-DSA-44
constant survives outside those fragments. `SLOTS` is therefore the complete
diff between the three verifiers. With NN = 44 the generator reproduces
`MlDsa44/Reference/reference.yul`, and the compiled bytes, exactly.

The differences are:

* the calldata offsets: pk/σ/hint/count positions and the minimum length;
* the loop bounds k and ℓ;
* `HB` zeroing (8k words);
* the z unpacking: width 20, 640 bytes/poly, norm window (β, 2γ₁ − β), γ₁;
* `UseHint` constants: 2γ₂, γ₂, m, m − 1;
* the w1 packing: 4 coefficients → 2 bytes instead of 3, row stride 128,
  hash input length 64 + 128k;
* SampleInBall's start index 256 − τ and the c̃ seed length;
* the final c̃ comparison: 32 bytes (44); 32 + 16 bytes with a `shr(128, …)`
  on both sides (65); 2 × 32 bytes (87).

Memory map (byte offsets; ST/BT/CT/RC/ZETA = 0x0/0x320/0x640/0x6e0/0x9e0 in
all three):

| Region | 44 | 65 | 87 | Size |
|---|---|---|---|---|
| ZH z-hat | 0x29e0 | 0x29e0 | 0x29e0 | ℓ × 0x2000 |
| CH c-hat | 0xa9e0 | 0xc9e0 | 0x109e0 | 0x2000 |
| AP A[i][j] | 0xc9e0 | 0xe9e0 | 0x129e0 | 0x2000 |
| ACC | 0xe9e0 | 0x109e0 | 0x149e0 | 0x2000 |
| TP t1·2^d | 0x109e0 | 0x129e0 | 0x169e0 | 0x2000 |
| HB hint bytes | 0x129e0 | 0x149e0 | 0x189e0 | k × 0x100 |
| XOF | 0x12de0 | 0x14fe0 | 0x191e0 | 0x420 |
| SEEDA ρ‖s‖r | 0x13200 | 0x15400 | 0x19600 | 0x40 |
| SEEDC c̃ | 0x13240 | 0x15440 | 0x19640 | 0x40 (c̃ ≤ 64) |
| PADB | 0x13280 | 0x15480 | 0x19680 | 0xc0 |
| W1 μ‖w1Encode | 0x13340 | 0x15540 | 0x19740 | 64 + 128k (65: 832, 87: 1088), rounded up to 0x40 |
| PK | 0x13680 | 0x15880 | 0x19b80 | \|pk\| rounded up to 0x40 |
| MSGIN tr‖00‖00‖M | 0x13bc0 | 0x16040 | 0x1a5c0 | 66 + n (+256 touched) |
| highest byte touched + 1 (n = 0) | 81120 | 90464 | 108256 | |

### Size and gas

Bytecode sizes are 65: 5302 bytes and 87: 5303 bytes, against 5289 bytes for
44. All gas figures were measured with `mldsatool run`: a fresh frame in the
pinned Osaka semantics, the gas used by the frame, and no transaction
intrinsic or calldata cost.

| message bytes | 65 gas | 87 gas |
|---:|---:|---:|
| 0 | 21,334,964 | 35,708,719 |
| 1 | 21,338,284 | 35,708,340 |
| 32 | 21,336,955 | 35,709,148 |
| 69 | 21,336,408 | 35,709,078 |
| 70 | 21,396,879 | 35,768,862 |
| 136 | 21,396,229 | 35,766,842 |
| 206 | 21,454,816 | 35,826,835 |
| 1000 | 21,751,802 | 36,124,635 |
| 3645 (ACVP tcId 39) | 22,940,977 | |
| 7965 (ACVP tcId 64) | | 39,213,851 |

Each further 136 bytes of message costs about 59k gas: one Keccak-f
permutation plus absorption. Across the vectors, data-dependent branches move
the cost by a few thousand gas. Short calldata costs 267 gas.

**Neither set fits the 2^24 = 16,777,216 per-transaction gas cap (EIP-7825).**
Even for an empty message:

* ML-DSA-65 is 4.56M over the cap (127%).
* ML-DSA-87 is 18.93M over the cap (213%).

A real call also pays the 21,000 intrinsic gas and calldata cost (5–7 kB,
so roughly 80–115k at 16 gas per nonzero byte). The verifier's actual budget
is therefore about 16.6M.

Per-function profile for the valid empty-message row. *Inclusive* includes
callees; `keccakF`, `rejSample` and `ntt` have no callees, so their figures
are self gas.

| Function | calls 44 | inclusive 44 | calls 65 | inclusive 65 | calls 87 | inclusive 87 |
|---|---:|---:|---:|---:|---:|---:|
| whole run | 1 | 12,953,021 | 1 | 21,334,964 | 1 | 35,708,719 |
| computeRow (ExpandA row, A·ẑ − ĉ·t̂1, NTT⁻¹) | 4 | 9,689,020 | 6 | 17,311,454 | 8 | 30,488,936 |
| shake | 20 | 7,113,016 | 34 | 12,571,506 | 60 | 22,573,098 |
| keccakF | 116 | 6,302,048 | 205 | 11,137,240 | 368 | 19,992,704 |
| ntt | 9 | 1,896,669 | 12 | 2,528,892 | 16 | 3,371,856 |
| rejSample | 16 | 968,268 | 30 | 1,815,740 | 56 | 3,389,088 |
| nttInv | 4 | 945,504 | 6 | 1,418,256 | 8 | 1,891,008 |
| decodeZ (incl. ℓ NTTs) | 1 | 1,173,208 | 1 | 1,466,498 | 1 | 2,053,078 |
| encodeRow (incl. useHint) | 4 | 362,439 | 6 | 529,480 | 8 | 707,414 |
| unpack | 2048 | 313,344 | 2816 | 430,848 | 3840 | 587,520 |
| initZetas | 1 | 222,253 | 1 | 222,253 | 1 | 222,253 |
| zeroPoly | 5 | 91,090 | 7 | 127,526 | 9 | 163,962 |
| sampleInBall | 1 | 45,779 | 1 | 47,569 | 1 | 49,874 |
| decodeHint | 1 | 14,281 | 1 | 10,814 | 1 | 16,347 |

One Keccak-f[1600] permutation costs 54.3k gas. ExpandA alone uses 6 kℓ
permutations: 96, 180 and 336. For 87, ExpandA's Keccak is 18.3M, more than
the whole cap. Keccak is 49% of the total for 44, 52% for 65 and 56% for 87.

What the gas-optimized design must reach for 87 to fit:

* Squeeze RejNTTPoly blocks on demand. Nearly always 5 blocks (840 bytes ≥
  768) suffice instead of a fixed 6, for about 280 + 30 permutations in
  total.
* Cut the permutation cost below roughly 30k gas.
* Shrink the remaining arithmetic: 24 NTTs, 56 RejNTTPoly scans, unpacking
  and the pointwise products, about 13M for 87 outside `shake`.

For 65 the same two Keccak changes alone bring it near the cap.

## What the proof phase needs

The proofs will target the gas-optimized design. For the reference design
above, comparing the three compiled artifacts gives the following picture.

**Byte-identical at the same addresses in all three bytecodes:** `keccakF`,
`bswap64`, `loadLE64`, `storeLE64`, `xorBlock`, `brv8`, `initZetas`,
`zeroPoly`, `ntt`, `nttInv` and `unpack`. Their 44 contracts (memory regions
ST/BT/CT/RC/ZETA and the pointer arguments) carry over unchanged. Only the
located-instruction certificates are per artifact, regenerated by
`mldsa44tool artifact`.

**Same code with different memory-map constants:**

| Function | Constants that change |
|---|---|
| `shake` | PADB |
| `rejSample` | XOF |
| `sampleInBall` | CH, XOF and the start index 256 − τ |

Their contracts need the layout as a parameter.

**Parameter-dependent code:**

| Function | What depends on the parameter set |
|---|---|
| `decodeHint` | k, ω, offsets |
| `decodeZ` | ℓ, width 20, norm window, γ₁ |
| `useHint` | γ₂, m = 16 |
| `encodeRow` | 4-bit packing |
| `computeRow` | ℓ, layout |
| main | k, lengths, the c̃ comparison over 48/64 bytes |

**Math libraries:**

| Library | Status |
|---|---|
| NTT model, sampling scans, Keccak/SHAKE | Parameter-free; reuse as is |
| Hint arithmetic and decompose/UseHint lemmas | Need statements over γ₂ = (q−1)/32 |
| BitUnpack/packing lemmas | Need widths 20 (z) and 4 (w1) |

**Statement side:** the analogue of `MlDsa44/Proofs/Bridge.lean`, which
aligns `verifyInternal` with the implementation's data flow, should be proved
once over `MlDsa.Fips204` for an arbitrary `P`, then instantiated.
`MlDsa/Bridge44.lean` already transfers anything stated for
`Params.mldsa44`. The memory-map and `Layout` predicates must be
parametrized by k and ℓ. Gas schedules must be rederived per set, and the
memory-expansion term changes with the map: `w = ⌈(90464 + n)/32⌉` for 65 and
`w = ⌈(108256 + n)/32⌉` for 87.

## Risks

* **Gas.** As built, neither 65 nor 87 fits in one transaction, and 87 needs
  more than a 2× reduction. If the optimized design cannot get 87 under about
  16.6M, `CorrectWithSchedule` remains provable, but the verifier is not
  callable on mainnet within EIP-7825.
* **Proof scale.** Larger k·ℓ loops, eight-row hint decoding and 64-byte
  c̃ comparison add loop-composition work but no new proof techniques. The
  per-artifact instruction certificates grow with the code, which is about the
  same size.
* **Kernel defeq.** Proofs that compare the 44 spec with the parametric spec
  must avoid `rfl`/`decide` across the two transcriptions; see the `bridge`
  tactic. The same hazard applies to any new `Bridge` lemma that unfolds
  bounded XOF loops.
* **Oracle quality.** dilithium-py accepts duplicate hint indices. The vector
  verdicts are the FIPS ones, and the Lean spec agrees with them, but
  dilithium-py cannot be used as an unchecked oracle for malformed hints
  (the fuzzing harness should use a strict Algorithm 21).
* **ACVP coverage.** Only one ACVP 65/87 row is usable as EIP calldata (empty
  context), and it is invalid. All valid ACVP signatures are checked through
  `verifyInternal` with M' = 0 ‖ |ctx| ‖ ctx ‖ M. The calldata path for valid
  signatures is covered by dilithium-py vectors only.
