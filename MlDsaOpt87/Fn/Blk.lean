import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
import MlDsaOpt87.Fn.Blk.Proof
/- Ported from `MlDsaOpt44/Fn/Blk.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# `blk`: de-interleave one squeezed SIMD block into RejNTTPoly candidates (WP3)

Entry `[flp, abp, ret]`. Un-complements the rate lanes of `KS` in place
(restoring them at the end), de-interleaves 3 words at a time with 6 delta
swaps (bit `4b + k` ↦ `64k + b`) and writes, per 8 candidates, 8 row-packed
candidate words at `abp` (lane = slot) and one rejection-flag word at `flp`.
The block number `b ≤ 5` selects `abp = ABUF + 1792 b`, `flp = FL + 224 b`.

`sbyte`, `cand`, `flagWord` are defined in `Blk/Defs.lean`; the proof is
`Blk/Proof.lean` (prologue 111 gas, 7 × 1087 per iteration, epilogue 116:
exactly `Gas.blk`).
-/

namespace MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem blk_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {b : Nat} (hb : b ≤ 5) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 56 → word m' (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 7 → word m' (FL + 224 * b + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)] ∧
      Call s Entry.blk [wd (FL + 224 * b), wd (ABUF + 1792 * b)] ret tail m [] m' Gas.blk :=
  blk_call_proof hs hr m hb

end MlDsaOpt87.Proofs
