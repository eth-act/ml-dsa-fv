# Reflection research prototype

Only scratch files; no shared tactic, theorem, generator, or build configuration
was changed. Base: `623dd95146893e6c43d6906133fc3ca2f2407b5e`.

## Reproduce

```sh
lake build MlDsaOpt44.Infra.Reach MlDsaOpt44.Fn.Blk.Bits MlDsaOpt44.Layout
export LEAN_PATH="$PWD:${LEAN_PATH:-}"
lake env lean -o Scratch/Reflection.olean Scratch/Reflection.lean
/usr/bin/time -f '%e s %M KB' lake env lean Scratch/ReflectBench.lean
/usr/bin/time -f '%e s %M KB' lake env lean Scratch/SimpBench.lean
/usr/bin/time -f '%e s %M KB' lake env lean Scratch/ReflectScale.lean
/usr/bin/time -f '%e s %M KB' lake env lean MlDsaOpt44/Fn/Blk/BodyA.lean
```

## What is proved

`Reflection.lean` proves symbolic PUSH1, DUP, XOR, AND, SHL, SHR sound against
the existing `runInstr`, then proves execution over the actual `locatedPath`
using checked instruction/PC alignment. Variables denote arbitrary UInt256
words; the untouched suffix is an arbitrary concrete list. Memory stays opaque
and unchanged. `decide +kernel` checks the symbolic result, not native evaluation.

`ReflectBench.lean` proves instructions 3678–3689 of BodyA (pc 9109–9123),
bridges the symbolic result to the existing `swm` definition, and lifts it to
`Reach ... 36`. `SimpBench.lean` proves exactly the same proposition with the
existing `opt44_block`. Both require the input word's natural representative
to be below 2^256, as is true of BodyA's memory-load result. Right shifts make
this hypothesis necessary; dropping it would be unsound.

The final theorems have exactly `[propext, Classical.choice, Quot.sound]` as
axioms. No sorry, new axiom, native_decide, or assumed soundness theorem.

## Measurements on this orb

Sequential runs, warm imports, each file alone, Lean 4.33.0:

| File | Wall seconds | Peak RSS KB |
| --- | ---: | ---: |
| Original BodyA | 96.61 | 2975552 |
| Reflection library including soundness and certificate | 4.51 | 2320936 |
| Reflected 12-instruction block plus Reach lift | 2.27 | 2264048 |
| Same block using existing simp plus Reach lift | 2.82 | 2294148 |

Earlier execution-only paired run: 2.28 versus 2.66 seconds. Profiler for that
pair: reflected proof elaboration 0.029 s versus simp 0.405 s; simp's final
kernel check another 0.090 s. These are not a BodyA speedup: the reflection
library already contains the block's result, safety, and alignment certificates.
Its 4.51 s first build must be counted before amortization.

`ReflectScale.lean` repeats the real 12-op delta-swap pattern 6, 12, and 28
times. Result-certificate kernel times were 0.023, 0.061, 0.144 s (another run
gave 0.189 s for 28). The longest is 336 instructions. This synthetic experiment
checks only symbolic result equality, not a real 336-op path or a denotation
bridge. Negative controls check wrong output mask, underflow, and both sides
of the stack-capacity boundary.

## Remaining design work

* Memory: use mutually recursive word and memory syntax, with `load mem off`
  and `store mem off value`, and an initial-memory variable denoting the opaque
  ByteArray. Denote stores using the exact existing `MachineState.writeBytes`
  and `natToBytesPadded`; do not evaluate bytes. Load/store soundness must also
  account for `activeWordsAfterUInt256`. This is a proposal, not implemented.
* Bounds: the prototype proves each prefix length bound through `Safe` using
  one symbolic tail length. Production should compute a maximum prefix depth
  and prove one inequality. Memory checks should emit a list of address/size
  obligations, proved from `hxp`, `habp`, and `hs.sized`; reflection alone
  cannot decide inequalities involving symbolic input addresses.
* Targets: `swm` already bridges cheaply after reflection. For `unz`, prove
  a compositional denotation lemma once, retaining word truncation facts.
  For `candMem`, preserve store order and offsets syntactically. A final giant
  unfolding/simp could recreate the original bottleneck; that bridge has NOT
  been measured. Do the same for `thetaY` only after inspecting its definition.
* Coverage: current implementation covers only the six instruction forms above
  and preserves memory. Adding ordinary arithmetic, SWAP/POP, memory operations,
  and JUMPDEST could cover straight-line no-expansion blocks across 44/65/87.
  Artifact alignment currently names Opt44 tables; abstract those for reuse.
  Dynamic jumps, memory expansion, MCOPY, calls, and custom read-after-write
  reasoning need additional soundness/side-condition work. No coverage percentage
  was measured.

Recommendation: reflection remains promising; symbolic evaluation itself is
comfortably below 21 seconds even at comparable instruction count. There is
no end-to-end evidence yet that full BodyA beats the 21-second chunked proof.
Keep chunking as the measured improvement, and pursue memory syntax plus the
full `candMem`/`unz` bridge as a separate follow-up before adopting reflection.
