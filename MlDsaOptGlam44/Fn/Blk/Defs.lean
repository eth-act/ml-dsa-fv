import MlDsaOptGlam44.Layout
import MlDsaOpt44.Fn.Blk.Mem
set_option warningAsError true
/-!
# Glam `blk`: memory transformer of one unrolled iteration

Iteration `it` of the unrolled `blk` loads lanes `3 it, 3 it + 1, 3 it + 2` of
`KS` at immediate addresses (`NOT` on the complemented ones), stores the eight
candidate words at `256 it + 32 k + abp` and the flag word at `32 it + flp`.
`cmemO M abp o …` is v4's `candMem` with the stores at `o + abp`,
`o + 32 + abp`, …, the shape the block lemmas produce (`cmemO_eq`).
-/

namespace MlDsaOptGlam44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Blk
open MlDsa44

/-- The eight candidate stores of one iteration, at `o + 32 k + abp`. -/
def cmemO (M : ByteArray) (abp o d0 d1 d2 : Nat) : ByteArray :=
  let w := fun (M : ByteArray) (v a : Nat) =>
    MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v % 2 ^ 256) 32) a
  w (w (w (w (w (w (w (w M (c0 d0 d1 d2) (o + abp)) (c1 d0 d1 d2) (o + 32 + abp))
    (c2 d0 d1 d2) (o + 64 + abp)) (c3 d0 d1 d2) (o + 96 + abp)) (c4 d0 d1 d2) (o + 128 + abp))
    (c5 d0 d1 d2) (o + 160 + abp)) (c6 d0 d1 d2) (o + 192 + abp)) (c7 d0 d1 d2) (o + 224 + abp)

theorem cmemO_eq (M : ByteArray) (abp o d0 d1 d2 : Nat) :
    cmemO M abp o d0 d1 d2 = candMem M (o + abp) d0 d1 d2 := by
  unfold cmemO candMem
  simp only [show ∀ c, o + c + abp = c + (o + abp) from fun c => by omega]

/-- A loaded rate lane, un-complemented: `NOT` on the complemented lanes. -/
def ldw (M : ByteArray) (x : Nat) : Nat :=
  if x ∈ complemented then 2 ^ 256 - 1 - word M (32 * x) else word M (32 * x)

/-- Under `KS4`, the un-complemented rate lanes are the plain interleaved lanes. -/
theorem ldw_lane {m : ByteArray} {S : Nat → Fips202.SpongeState} (hKS : KS4 m S) {x : Nat}
    (hx : x < 25) : ldw m x = il fun k => laneOf (S k) x := by
  have h := hKS x hx
  simp only [KS, Nat.zero_add] at h
  unfold ldw
  by_cases hc : x ∈ complemented
  · rw [if_pos hc, h]
    simp only [cpl, hc, if_true]
    exact not_il fun k _ => laneOf_lt _ _
  · rw [if_neg hc, h]
    simp only [cpl, hc, if_false]

end MlDsaOptGlam44.Proofs.Blk
