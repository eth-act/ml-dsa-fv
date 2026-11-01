import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
/-!
# `blk`: de-interleave one squeezed SIMD block into RejNTTPoly candidates (WP3)

Entry `[flp, abp, ret]`. Un-complements the rate lanes of `KS` in place
(restoring them at the end), de-interleaves 3 words at a time with 6 delta
swaps (bit `4b + k` ↦ `64k + b`) and writes, per 8 candidates, 8 row-packed
candidate words at `abp` (lane = slot) and one rejection-flag word at `flp`.
The block number `b ≤ 5` selects `abp = ABUF + 1792 b`, `flp = FL + 224 b`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- Byte `j` of the squeezed block of a state (`stateBytes 168 S`). -/
def sbyte (S : Fips202.SpongeState) (j : Nat) : Nat := laneOf S (j / 8) / 2 ^ (8 * (j % 8)) % 256

/-- RejNTTPoly candidate `i < 56` of a block: three bytes, top bit masked
(FIPS 204 Algorithm 14 before the `< q` test). -/
def cand (S : Fips202.SpongeState) (i : Nat) : Nat :=
  sbyte S (3 * i) + 256 * sbyte S (3 * i + 1) + 65536 * (sbyte S (3 * i + 2) % 128)

/-- Flag word `g` of a block: lane `k` bit 23 is set iff slot `k` rejected one
of the candidates `8g … 8g + 7` (`cand + 2^23 − q < 2^24`, no carry). -/
def flagWord (S : Nat → Fips202.SpongeState) (g : Nat) : Nat :=
  orList ((List.range 8).map fun i => pack4 fun k => cand (S k) (8 * g + i) + 2 ^ 23 - Fips204.q)

theorem blk_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.blk ret tail) (m : ByteArray) {b : Nat} (hb : b ≤ 5) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        (∀ i, i < 56 → word m' (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, g < 7 → word m' (FL + 224 * b + 32 * g) = flagWord S g)) ∧
      FrameExcept m m' [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)] ∧
      Call s Entry.blk [wd (FL + 224 * b), wd (ABUF + 1792 * b)] ret tail m [] m' Gas.blk := by
  sorry

end MlDsaOpt44.Proofs
