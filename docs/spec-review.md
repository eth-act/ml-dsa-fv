# Independent trusted-specification audit

## 1. Verdict

**Faithful on the EIP-8355 calldata domain, with one malformed-input deviation in the standalone `Fips204.verify` API.** No discrepancy was found in SHAKE/Keccak, ML-DSA-44 verification on correctly sized fields, or the EIP field extraction/output. The bounded samplers are a permitted FIPS 204 Appendix C implementation choice, not a discovered cryptographic error.

The exported standalone verifier accepts an otherwise valid signature with extra trailing bytes, contrary to FIPS 204 §3.6.2. This is **not reachable through `MlDsa44.accepts`**, which always extracts exactly 1312 public-key bytes and 2420 signature bytes after checking the calldata minimum. Thus this finding does not demonstrate an incorrect result for the verified calldata artifact.

The final context-generalized definitions were reviewed, including `FrameEntry`, `CorrectInAnyContextWithSchedule`, and `CorrectInAnyContext` at `Spec.lean:106–142`. Their distinction between a frame-local `Steps` conclusion and a top-level `Eval` conclusion is sound. No theorem-statement defect was found; important scope limitations are explained below.

This is a source audit plus the concrete differential checks listed in §5, not a formal proof of equivalence to the standards or a certification of their operational requirements.

### References used

- [FIPS 204, final August 2024 standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf), using the repository's `.ref/fips204.txt`: §§2.3–2.4, 3.6.2, 3.7; Table 1; Algorithms 3, 8–14, 16, 18–19, 21, 23, 27–30, 32, 36–37, 40–48; Appendices B–C.
- [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf): §§3.1–3.4, 4, 5.1–5.2, 6.2, Appendix B.2. Fetched and read directly through the document reader; no reference file was written.
- [EIP-8355 draft](https://raw.githubusercontent.com/ethereum/EIPs/master/EIPS/eip-8355.md), fetched during this audit: Sizes, Input format, Semantics, Output, and Gas cost.

## 2. Findings

| Severity | Location | Specification versus standard | Concrete counterexample / reasoning | Suggested fix |
|---|---|---|---|---|
| **Major — standalone malformed-input API only** | `MlDsa44/Spec/Fips204.lean:301–302`; related decoding at `118–125` | `verify` accepts arbitrary `ByteArray` arguments and delegates without checking their lengths. `sigDecode` extracts only bytes `[0,2420)`, ignoring a suffix. FIPS 204 §3.6.2 requires returning false whenever an accepted public-key or signature input has a nonstandard length. | Use **row 1 of `vectors/calldata.txt`**: `pk = calldata[0:1312]`, `M = empty`, `sig = calldata[1312:3732]`. Both `verify pk M sig` and `verify pk M (sig ++ 00)` evaluated to **true**. The latter signature has 2421 bytes and must be rejected under §3.6.2; dilithium-py returned false for it. SHA-256 of the original 2420-byte signature: `a16b5095839841596e3b79a9863b1b3b613b27a131e4f48c14ae16bd09337b6f`. In fact every accepted signature is an equivalence-class witness because suffixes are ignored. `accepts` is unaffected: trailing calldata bytes are the **message**, not extra signature bytes. | Check `pk.size == pkLen && sig.size == sigLen` in the public `verify` wrapper. Alternatively make the exact-length precondition explicit in its type/domain and stop presenting the unrestricted function as a complete Algorithm 3 implementation. Internal decoding helpers may retain their specified-domain preconditions. |

Severity follows the requested malformed/edge-input category: this is Major rather than a claim of Critical EIP/artifact behavior. No reachable EIP acceptance/rejection discrepancy was found. No separate finding is assigned to helper behavior outside its FIPS input domain (e.g. a polynomial array of the wrong length or `shake` with an unsupported rate).

### Non-findings worth distinguishing

- `zetas 0 = 1`, whereas Appendix B's displayed table has dummy entry `zetas[0] = 0`. The standard specifies/precomputes the values used for indices **1 through 255**, and both NTTs use only those indices. All 255 used values matched Appendix B. This unused-entry difference is not a verification deviation.
- The installed dilithium-py hint decoder accepts duplicate indices `[5,5]` within one polynomial. FIPS Algorithm 21 and the Lean spec correctly reject them. The crafted malformed-hint audit therefore used a separate strict transcription of Algorithm 21, not that library function as an unquestioned oracle.
- EIP-8355 says both “big-endian throughout” and “standard compressed FIPS 204 encoding.” The spec correctly passes the raw byte strings to FIPS decoding and uses FIPS little-endian bit packing internally; reversing the key/signature bytes would contradict the EIP's explicit FIPS verification semantics.

## 3. Complete per-definition checklist

`✓` means faithful on the specified/reachable domain, not that a formal refinement proof was constructed. `✗` identifies the finding above. Line numbers are from the source read during this audit.

### `MlDsa44/Spec/Fips202.lean`

| Definition | Lines | FIPS reference | Result / note |
|---|---:|---|---|
| `SpongeState` | 22 | 202 §3.1 | ✓ 25 lanes; invariant supplied by construction, not the array type. |
| `emptyState` | 24 | 202 Alg.8 step5 | ✓ All 1600 state bits zero. |
| `pad` | 28–31 | 202 §5.1, §6.2, App.B.2 | ✓ For rates 136/168, padding length is in `[1,rate]`; suffix `1f`, terminal `80`; shared final byte `9f`. A block-aligned message gets a full additional padded block. |
| `xorBlock` | 34–37 | 202 Alg.8 step6; §3.1.2 | ✓ XOR rate/8 little-endian lanes, capacity unchanged. |
| `absorbBlock` | 40–42 | 202 Alg.8 step6 | ✓ XOR then permutation. |
| `absorb` | 45–47 | 202 Alg.8 steps2–6 | ✓ Every full padded block, in order, starting at zero state. |
| `stateBytes` | 50–51 | 202 §3.1.3, Alg.8 step8 | ✓ First rate bytes, lane and byte order correct. |
| `squeeze` | 54–56 | 202 Alg.8 steps7–10 | ✓ Emit current state before permuting for subsequent blocks. |
| `shake` | 59–61 | 202 §6.2, Alg.8 | ✓ SHAKE suffix; ceiling block count; exact byte-prefix extraction. Zero-length output is empty. |
| `shake128` | 64 | 202 §6.2 | ✓ 168 bytes = 1344-bit rate, 256-bit capacity. |
| `shake256` | 67 | 202 §6.2 | ✓ 136 bytes = 1088-bit rate, 512-bit capacity. |

Only the two supported byte-aligned rates are used. This is not a general arbitrary-bit-message SHAKE API.

### Used dependency: `.lake/packages/evm_semantics/EvmSemantics/Crypto/Keccak256.lean`

| Definition | Lines | FIPS reference | Result / note |
|---|---:|---|---|
| `RC` | 35–41 | 202 §3.2.5, Algs.5–6 | ✓ All 24 constants independently regenerated from FIPS `rc(t)` and matched. |
| `rotOff` | 44–49 | 202 §3.2.2, Alg.2/Table2 | ✓ All 25 offsets independently regenerated modulo64 and matched; indexing `x+5y`. |
| `rotl64` | 52–54 | 202 §3.2.2 | ✓ Left rotation; special zero case avoids shifting by64; used offsets are 0–63. |
| `round` | 57–85 | 202 §§3.2.1–3.2.5 | ✓ θ uses previous column and next column rotated left1; ρ/π send `(x,y)` to `(y,2x+3y mod5)`; χ reads an unmodified intermediate row and uses 64-bit complement; ι XORs lane0. |
| `permute` | 88–92 | 202 §§3.3–3.4, Alg.7 | ✓ Rounds 0–23, in order; correct Keccak-f[1600]. |
| `readLE64` | 96–101 | 202 §3.1.2/App.B.1 | ✓ Bytes at offsets0–7 occupy bits0–63; explicit out-of-range zero fill is not exercised by padded absorption. |
| `writeLE64` | 104–108 | 202 §3.1.3/App.B.1 | ✓ Appends eight bytes least significant first. |

The dependency's Ethereum `hash`, `keccak256Impl`, and opaque/`implemented_by` `keccak256` are **not** the SHAKE implementation used here. SHAKE calls the concrete permutation and lane conversion functions directly; Ethereum's `01` delimiter is not accidentally imported into SHAKE.

### `MlDsa44/Spec/Fips204.lean`

| Definition | Lines | FIPS reference | Result / note |
|---|---:|---|---|
| `q` | 24 | Table1 | ✓ 8380417. |
| `zeta` | 25 | Table1, §7.5 | ✓ 1753. |
| `d` | 26 | Table1 | ✓ 13. |
| `tau` | 27 | Table1 | ✓ 39. |
| `lambda` | 28 | Table1 | ✓ 128. |
| `gamma1` | 29 | Table1 | ✓ 131072. |
| `gamma2` | 30 | Table1 | ✓ `(q−1)/88 = 95232`. |
| `k` | 31 | Table1 | ✓ 4. |
| `l` | 32 | Table1 | ✓ 4. |
| `eta` | 33 | Table1 | ✓ 2. |
| `beta` | 34 | Table1 | ✓ `tau*eta = 78`. |
| `omega` | 35 | Table1 | ✓ 80. |
| `bitlen` | 38 | §2.3 | ✓ `log2(b)+1` for positive b; all reachable arguments positive. |
| `pkLen` | 41 | Alg.3, Table2 | ✓ 1312 = 32 + 4·320. |
| `sigLen` | 42 | Alg.3, Table2 | ✓ 2420 = 32 + 4·576 + 80 + 4. |
| `rejNTTPolyLimit` | 45 | App.C/Table3 | ✓ 1008 bytes, 336 three-byte trials, at least894/298. |
| `sampleInBallLimit` | 46 | App.C/Table3 | ✓ 272 total bytes, at least221. |
| `Poly` | 48 | §2.4.1 | ✓ Integer coefficient array representation; size256 is a call-chain invariant. |
| `zeroPoly` | 50 | Algs.21/29/30/48 | ✓ Exactly256 zeros. |
| `H` | 54 | §3.7 | ✓ SHAKE256, length argument measured in bytes. |
| `G` | 55 | §3.7 | ✓ SHAKE128, length argument measured in bytes. |
| `bit` | 60 | Alg.13 | ✓ Low bit first within each byte. |
| `bitsToInteger` | 63–64 | Alg.10 | ✓ Sum of bit j times2^j, equivalent to reverse Horner loop. |
| `coeffFromThreeBytes` | 67–70 | Alg.14 | ✓ Mask the third byte's top bit; little-endian23-bit integer; accept iff `<q`. |
| `simpleBitPack` | 73–77 | Algs.9/12/16 | ✓ Coefficient-major, low bits first, exactly32·bitlen(b) bytes; `.toNat` is safe on reachable nonnegative high bits. |
| `simpleBitUnpack` | 80–82 | Alg.18 | ✓ Exactly256 adjacent fixed-width fields. Public-key width10 covers exactly0–1023. |
| `bitUnpack` | 85–87 | Alg.19 | ✓ Integer `b−decoded`; width18 for z gives `[-131071,131072]` with no Nat subtraction underflow. |
| `hintBitUnpack` | 90–105 | Alg.21 | ✓ All three malformed checks: monotone bounded endpoints; strictly increasing per-polynomial indices; zero unused bytes. Index255 allowed; duplicates across different polynomials allowed. |
| `pkDecode` | 110–115 | Alg.23 | ✓ Seed `[0,32)`; four320-byte t1 fields; b=1023. |
| `sigDecode` | 118–125 | Alg.27 | ✓ On exact-length input: c `[0,32)`; z `[32,608)`, `[608,1184)`, `[1184,1760)`, `[1760,2336)`; hints `[2336,2420)`. It intentionally slices, and so does not itself enforce caller lengths. |
| `w1Encode` | 128–130 | Alg.28 | ✓ Four6-bit coefficient polynomials, b=43; total768 bytes. |
| `sampleIndex` | 137–141 | Alg.29 steps7–10; App.C | ✓ Reject `j>i`; accept equality; monotonically consume the bounded XOF prefix. |
| `sampleInBallOf` | 145–156 | Alg.29 | ✓ First8 bytes are signs; i=217…255; `j≤i`; copy old c[j] before writing sign; sign bit `i+39−256` is0…38. |
| `sampleInBall` | 159–160 | Alg.29, §3.7/App.C | ✓ Bounded SHAKE256 prefix models incremental H output exactly until exhaustion. |
| `rejNTTPolyOf` | 164–174 | Alg.30/App.C | ✓ At most336 trials; rejected coefficient does not advance j; exactly256 accepted coefficients required; stops modifying after success. |
| `rejNTTPoly` | 177–178 | Alg.30, §3.7/App.C | ✓ Bounded SHAKE128 prefix. |
| `expandA` | 181–184 | Alg.32, Alg.11 | ✓ Four rows/four columns; seed `rho || byte(s) || byte(r)`, not row/column reversal; any exhaustion propagates none. |
| `modPm` | 189–191 | §2.3 | ✓ Euclidean remainder followed by `>floor(alpha/2)` correction; correct positive tie. |
| `decompose` | 194–198 | Alg.36 | ✓ Normalize modq; balanced mod2gamma2; special case `rPlus−r0=q−1` returns `(0,r0−1)`; otherwise exact integer division. |
| `useHint` | 201–206 | Alg.40 | ✓ h=1 shifts high bits according to strict positive/nonpositive low bits; modular wrap modulo44, including negative wrap. |
| `bitRev8` | 211–212 | Alg.43 | ✓ Eight bit positions reversed. |
| `zetas` | 215 | §7.5/App.B | ✓ All used indices1…255 match; unused index0 explained above. |
| `ntt` | 219–234 | Alg.41 | ✓ Eight lengths128…1, 128/len blocks; m increments before use1…255; exact butterflies and modq. |
| `nttInv` | 238–257 | Alg.42 | ✓ Eight lengths1…128; m decrements before use255…1; negative zeta; correct update order; scale8347681 =256 inverse modq. |
| `addNTT` | 262 | Alg.44 | ✓ Componentwise addition in Zq. |
| `multiplyNTT` | 265 | Alg.45 | ✓ Componentwise multiplication, no extraneous convolution/Montgomery factor. |
| `matrixVectorNTT` | 268–270 | Alg.48 | ✓ Row-wise sum of four scalar products with zero accumulator. |
| `normBelow` | 275–276 | §2.3, Alg.8 step13 | ✓ Integer-coefficient absolute norm, **strictly** below130994; equality rejected. |
| `verifyInternal` | 279–297 | Alg.8; Algs.37/46/47 inlined componentwise | ✓ On standard-length inputs: malformed hints/bound exhaustion false; tr64; mu64; `Az−c·t1·2^d`; inverse NTT; hints componentwise; H(mu||encoded w1,32); norm and byte equality. Reordering pure computations does not change its Boolean result. |
| `verify` | 301–302 | Alg.3; §3.6.2 | ✗ Correct empty-context formatting `00 00 || M`; missing exact-length rejection for the unrestricted public ByteArray API. |

### `MlDsa44/Spec.lean`

| Definition | Lines | Reference | Result / note |
|---|---:|---|---|
| `pkLen` | 24 | EIP Sizes | ✓ Alias1312. |
| `sigLen` | 25 | EIP Sizes | ✓ Alias2420. |
| `accepts` | 28–31 | EIP Input format/Semantics | ✓ Minimum3732; pk `[0,1312)`, sig `[1312,3732)`, message `[3732,L)`; equality permits empty message. |
| `spec` | 34–35 | EIP Output | ✓ Exactly32 bytes; 31 zeros followed by Boolean0/1. |
| `CalldataFits` | 38 | Theorem domain restriction | ✓ Explicit `<2^64` size restriction; not part of the cryptographic predicate itself. |
| `deployAddress` | 41 | Chosen execution model | ✓ 0x8212, deliberately not native EIP address0x12. |
| `executionConfig` | 43 | Chosen execution model | ✓ Empty custom precompile configuration. |
| `initialState` | 46–78 | Fresh fixed Osaka frame | ✓ Code and calldata installed; pc0, empty stack/memory/call stack, zero active words/counters/buffers; fixed caller/origin/value; original world snapshot installed. |
| `Correct` | 82–85 | Functional total-return property | ✓ All admissible calldata; per-calldata sufficient gas threshold; exact returned word. |
| `CorrectWithSchedule` | 88–91 | Length-indexed gas bound | ✓ Any gas at least schedule(length) suffices; strictly more informative than unspecified threshold. |
| `correct_of_schedule` | 93–95 | Elementary implication | ✓ Witness g0=schedule(length), correct quantifier order. |
| `FrameEntry` | 106–116 | Fresh bytecode-entry precondition | ✓ Fresh machine fields, Osaka, matching code, non-precompile dispatch, calldata bound; environment/world/call stack otherwise unrestricted. |
| `CorrectInAnyContextWithSchedule` | 127–135 | Frame-local contextual property | ✓ Steps to Returned/hReturn; gas lower bound; final equality preserves world, environment, returnData, callStack and all unlisted fields. |
| `CorrectInAnyContext` | 139–142 | Arbitrary top-level context property | ✓ Explicit empty-call-stack premise makes Eval appropriate; sufficient gas threshold per entry state. |

## 4. Design choices, indexing invariants, and theorem meaning

### Choice 1: bounded XOF output

**Permitted, with the standard's qualification.** Appendix C says implementations *should not* bound these loops, but explicitly permits limits no lower than Table3. RejNTTPoly's1008 bytes correspond to336 trials, not1008 trials; both exceed894 bytes/298 trials. SampleInBall's272 is a **total byte bound including the8 sign bytes**, exceeding the221 total-byte minimum. The separate121 figure bounds one rejection while-loop; it is not a requirement that a total-byte-bound implementation separately impose that loop limit.

Both bounded algorithms produce exactly the unbounded pseudocode's result whenever enough prefix bytes suffice. Failure returns none and is uniformly collapsed to verification false. No partly filled polynomial/hint escapes. Byte positions and last permitted accesses are correct (`p≤271`; rejection triple at indices1005,1006,1007). A mathematically valid unbounded signature might fail only because of this allowed exhaustion behavior; that is a permitted bounded implementation, not a claim that bounded and unbounded predicates are extensionally identical.

FIPS operational requirements to erase sensitive intermediate state are not established by a pure Boolean specification or by equality of return values. The spec exposes no intermediate output, but that is not a memory-zeroization proof.

### Choice 2: empty context and byte messages

**Correct for the EIP profile.** Algorithm3 contributes a zero domain byte, one zero context-length byte, and no context bytes; `00 00 || M` is correct. No prehash or HashML-DSA identifier is inserted. The EIP has a raw byte-message interface; general FIPS non-byte-aligned messages and nonempty contexts are deliberately outside this profile.

### Choice 3: integer arrays and `% q`

**Sound on every reachable arithmetic use.** Lean Int remainder with positive q is Euclidean; evaluated examples `(-1)%q = q−1`, `(-q−1)%q = q−1`, and `(-1)%44 =43` confirm the relevant signs. The NTT difference, inverse negative-zeta product, add/multiply, and wApprox subtraction are all Int operations reduced with positive q. Signed c and z are legitimate representatives of elements in Rq; initial NTT butterflies normalize them.

`modPm` uses the correct positive tie. In Decompose the ordinary quotient is exact after selecting r0; the q−1 exceptional case is handled separately. UseHint wraps with positive modulus44; for example h=1,r=0 gives43. The norm uses integer z from BitUnpack, not an accidental unsigned representative. z lies between−131071 and131072, so ordinary absolute value is also consistent with its centered representative modq.

**Out-of-bounds audit (reasoned over the complete reachable call chain):**

- `accepts` establishes exact key/signature slice lengths for any input whose result can be true. Helpers can have default-zero behavior off their declared domains; this does not create an EIP acceptance path.
- All decoded polynomials have256 entries; all vectors have4 entries and matrices4×4 entries. `set!` never silently loses a reachable write.
- Packed public-key fields have320 bytes at10 bits/coeff; z fields have576 bytes at18 bits/coeff; w1 packing consumes256 valid coefficients at6 bits/coeff. Bit accesses end exactly at each field's boundary.
- Hint endpoints are checked before use, are in0…80 and nondecreasing. Each payload index is a byte, so each polynomial coefficient index is0…255. Equal endpoints produce empty ranges correctly; strict ordering resets per polynomial.
- SampleInBall reads signs only from the first39 bits of the initial8 bytes. Its selected j is at most i≤255. The i+tau−256 Nat expression cannot underflow because i starts at217.
- Both NTTs process blocks ending below256; j+len≤255. The forward twiddle index sequence is1…255; inverse255…1. No use of index0 or256.
- Keccak states always have25 lanes. Rates give17 or21 lanes; round mappings stay within25; theta arrays within5; RC indices within24. Padding length is never zero at supported rates.

### Choice 4: fixed Osaka initial frame

**Sound but intentionally limited.** `Correct` is not a statement about arbitrary deployments/callers/worlds, CALL/STATICCALL/DELEGATECALL behavior, or native activation at EIP address0x12. It fixes address0x8212, an otherwise empty world, zero caller/origin/value, mutable mode, default block header, Osaka, no suspended callers, and empty custom precompile configuration.

`Correct` proves eventual exact RETURN for all sufficiently large Nat gas budgets. It neither specifies the EIP's6500+6·ceil(messageBytes/32) precompile charge nor demonstrates that the threshold is affordable under transaction/block limits. `CorrectWithSchedule` supplies a length-dependent sufficiency bound, not an exact charge, exact remaining gas, or up-front charging assertion. These are scope distinctions, not false claims in the definitions.

### Generalized statements

- `FrameEntry` restricts execution to bytecode dispatch, not a configured native precompile, and to Osaka. It permits arbitrary world/accounts/storage/substate, address/codeAddr, header, caller/origin/value, gas price, static flag, depth, precompile configuration, and enclosing call stack, subject to its explicit conditions. It does **not** require that these form a reachable transaction state or that accountMap(codeAddr).code matches executionEnv.code; this is a stronger entry-state domain, not a missing adversarial context.
- Entry `returnData`, `hReturn`, and `execLength` are not required empty/zero. The contextual frame theorem requires preserving `returnData` and `execLength`; hReturn may be replaced. This is stronger than only quantifying over conventional freshly initialized buffers.
- `CorrectInAnyContextWithSchedule` correctly concludes at a halted **active frame** using `Steps`, preserving the call stack. It does not confuse this with whole-transaction `Eval`, which only completes with an empty call stack (`EVM/BigStep.lean:37–44,65–68`). The Nat gas-subtraction bound is meaningful because its premise already ensures entry gas≥schedule.
- The record equality is stronger than return-value correctness: final accounts, storage, substate, environment, returnData, callStack, and execLength cannot change. It is an **endpoint** preservation property, not a trace-level assertion forbidding temporary intermediate changes, external observations, or gas/timing leakage.
- `CorrectInAnyContext` explicitly restricts to no suspended callers and uses Eval. It is arbitrary **top-level** context correctness, not a misleading nested-frame Eval theorem. Its threshold may depend on the entire entry state. Only the scheduled frame statement gives a uniform length-indexed bound across contexts.
- These are proposition definitions. This audit of their meaning does not establish that a particular frozen bytecode has a proof of the new contextual propositions.

## 5. Checks actually executed

All generated harnesses/results were confined to `scratch/review/` and removed after the audit. No reviewed source file was modified. No rebuild, lint, or formatter was run.

1. **Existing specification vectors**

   Command: `export TMPDIR=$PWD/.lake/tmp && .lake/build/bin/mldsa44tool spec`

   Observed: `acvp verifyInternal: 30/30 agree`; `calldata spec: 47/47 agree`; exit0.

2. **Targeted Lean evaluation**

   Command: `export TMPDIR=$PWD/.lake/tmp && lake env lean --run scratch/review/Audit.lean`

   After correcting scratch-only harness namespace errors, observed `wrote 10434 result rows`, exit0. The JSON contained:

   - Parameters/lengths/limits and three negative-remainder examples.
   - **384 SHAKE comparisons**: both rates; input lengths0,1,134,135,136,137,166,167,168,169,271,272,273,335,336,337; output lengths0,1,32,135,136,137,167,168,169,272,337,512; input byte i=`(73i+19) mod256`.
   - All256 computed zetas; six signed-input NTT transforms and inverse round trips; six SampleInBall seeds and six RejNTTPoly seeds.
   - **10018 Decompose/UseHint cases**, including negative representatives and 0, gamma2±1, 2gamma2±1, q−1−gamma2±1, q−1, q, q+1, plus10000 deterministic samples.
   - Eight crafted hint encodings: valid empty, valid cross-polynomial reuse, duplicate indices, descending indices, decreasing endpoint, endpoint81, nonzero unused byte, and valid coefficient255.
   - All-ff sampler prefixes exhaust and return none.
   - The accepted-signature-plus-00 counterexample from calldata row1.

3. **Independent Python comparisons**

   Executed Python through the evaluation tool, importing `.ref/pylib/dilithium_py` and standard-library `hashlib`, reading only generated JSON and the relevant reference data. Observed **all comparisons passed**:

   -384 SHAKE outputs matched `hashlib.shake_128/256` byte-for-byte.
   - All255 used zetas matched FIPS204 Appendix B and the independent polynomial library; unused index0 difference was explicitly checked.
   - Six NTT outputs and inverse outputs matched dilithium-py; all round trips recovered input coefficients moduloq.
   - Six SampleInBall polynomials matched dilithium-py; six RejNTTPoly outputs matched independently decoded hashlib SHAKE128 streams.
   -10018 Decompose/UseHint cases matched independent utility functions.
   - Eight hint cases matched a strict Algorithm21 oracle. Separately confirmed the installed library accepts duplicate hint indices, so it was not used as the malformed-hint authority.
   - Original row1 signature was accepted by both implementations; its2421-byte extension was accepted by Lean and rejected by dilithium-py.
   - Regenerated all24 Keccak RC values directly using FIPS202 Algorithms5–6 and all25 rho offsets using Algorithm2: all matched the pinned source constants.

4. **Encoding and boundary evaluation**

   Command: `export TMPDIR=$PWD/.lake/tmp && lake env lean --run scratch/review/Encoding.lean`

   After correcting scratch-only ByteArray JSON serialization, observed `wrote 31 encoding rows`, exit0. Independent Python comparison observed **all encoding comparisons passed**:

   - One complete ExpandA matrix: all16 polynomials matched dilithium-py, checking rho||column||row ordering.
   - Three SimpleBitPack/Unpack cases at widths1,6,10 matched a separate little-endian integer-field packer and round-tripped.
   - Four-polynomial w1 encoding matched the independent6-bit packer and had768 bytes.
   - Nine CoeffFromThreeBytes boundary/high-bit cases matched masked23-bit rejection, including q−1,q,2^23−1,2^23,2^24−1.
   - Positive and negative norm cases130993 accepted,130994 and130995 rejected.
   - pkDecode/sigDecode outputs matched dilithium-py on all14 valid calldata fixtures (rows1,7,8,9,15,16,17,23,24,25,31,32,33,39), including seed, t1, challenge, z, and hints.

The per-line algorithm comparison, reachability/index invariants, Appendix C permission assessment, and theorem-quantifier analysis are **reasoned source review**. No exhaustive SHAKE/NTT verification, exhaustive all-q Decompose evaluation, FIPS certification, memory-erasure proof, contextual bytecode proof, or EIP gas-charge proof was executed or claimed.
