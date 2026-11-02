import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
import MlDsaOpt44.Fn.Blk.Defs
/- Ported from `MlDsaOpt87/Fn/Blk.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Blk.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# `blk`, `blkh`, `blkt`: de-interleave a squeezed SIMD block into RejNTTPoly candidates (WP3)

One loop body over lanes `[xp, xe)` of `KS` (three per iteration). Each entry
un-complements the rate lanes of `KS` in place (restoring them at the end),
de-interleaves 3 words at a time with 6 delta swaps (bit `4b + k` ↦ `64k + b`)
and writes, per 8 candidates, 8 row-packed candidate words at `abp` (lane =
slot) and one rejection-flag word at `flp`.

* `blk [flp, abp, ret]`: lanes 0 … 20 (the 56 candidates and 7 flag words);
  block `b` of a group at `abp = ABUF + 1792 b`, `flp = FL + 224 b`, the
  window's staged blocks at `ACC` / `BASES`.
* `blkh [flp, abp, ret]`: lanes 0 … 11 (candidates 0 … 31, flag words 0 … 3).
* `blkt [ret]`: lanes 12 … 20 of block 4 (candidates 32 … 55 at
  `ABUF + 1792 · 4 + 32 · 32`, flag words 4 … 6), made by `gfix` before the
  first fix-up of a group.

`sbyte`, `cand`, `flagWord` are defined in `Blk/Defs.lean`; the proofs are in
`Blk/Proof.lean`.
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **blk**: the 56 candidates and 7 flag words of a block at any `abp`,
`flp` above `KS` and below `TOP` (disjoint). -/
theorem blk_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {abp flp : Nat}
    (ha : KS + 800 ≤ abp) (ha' : abp + 1792 ≤ TOP) (hf : KS + 800 ≤ flp) (hf' : flp + 224 ≤ TOP)
    (hd : abp + 1792 ≤ flp ∨ flp + 224 ≤ abp) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 56 → word m' (abp + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 7 → word m' (flp + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(abp, abp + 1792), (flp, flp + 224)] ∧
      Call s Entry.blk [wd flp, wd abp] ret tail m [] m' Gas.blk := by
  sorry  -- glam: open item (package 1)

/-- **blkh**: candidates `0 … 31` and flag words `0 … 3` of a block at any
32-byte aligned `abp`, `flp` below `TOP`. -/
theorem blkh_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {abp flp : Nat}
    (ha : KS + 800 ≤ abp) (ha' : abp + 1024 ≤ TOP) (hf : KS + 800 ≤ flp) (hf' : flp + 128 ≤ TOP)
    (hd : abp + 1024 ≤ flp ∨ flp + 128 ≤ abp) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 32 → word m' (abp + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 4 → word m' (flp + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(abp, abp + 1024), (flp, flp + 128)] ∧
      Call s Entry.blkh [wd flp, wd abp] ret tail m [] m' Gas.blkh := by
  sorry  -- glam: open item (package 1)

/-- **blkt**: the rest of block 4: candidates `32 … 55` and flag words `4 … 6`. -/
theorem blkt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, 32 ≤ i → i < 56 → word m' (ABUF + 1792 * 4 + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, 4 ≤ g → g < 7 → word m' (FL + 224 * 4 + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(ABUF + 1792 * 4 + 1024, ABUF + 1792 * 5), (FL + 224 * 4 + 128, FL + 224 * 5)] ∧
      Call s Entry.blkt [] ret tail m [] m' Gas.blkt := by
  sorry  -- glam: open item (package 1)

end MlDsaOptGlam87.Proofs
