import MlDsaOpt44.Math.Sponge
set_option warningAsError true
/-!
# `SlotHead` from the group's block outputs

Blocks 0 … 3 (`blk`, 56 candidates and 7 flag words each) and the head of
block 4 (`blkh`, candidates 0 … 31 and flag words 0 … 3) make every slot's
first 256 candidates and 32 flag words, i.e. `SlotHead`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa44

theorem slotHead_of_blocks {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState} {sl : Nat}
    (hsl : sl < 4) {I : Fips202.SpongeState} (hSt : ∀ b, b < 5 → St b sl = permN (b + 1) I)
    (hA : ∀ b, b < 5 → ∀ i, i < 56 → b * 56 + i < 256 →
      word m (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (St b k) i)
    (hF : ∀ b, b < 5 → ∀ g, g < 7 → b * 7 + g < 32 →
      word m (FL + 224 * b + 32 * g) = flagWord (St b) g) :
    SlotHead m sl I := by
  refine ⟨fun t ht => ?_, fun g hg => ?_⟩
  · have hb : t / 56 < 5 := by omega
    rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
      hA _ hb _ (Nat.mod_lt _ (by norm_num)) (by omega), lane_pack4_cand _ _ hsl, hSt _ hb]
    rfl
  · have hb : g / 7 < 5 := by omega
    rw [show FL + 32 * g = FL + 224 * (g / 7) + 32 * (g % 7) by omega,
      hF _ hb _ (Nat.mod_lt _ (by norm_num)) (by omega), flagBit_flagWord _ _ hsl, hSt _ hb]
    rw [any_congr_mem (q := fun i => decide (Fips204.q ≤ candI I (8 * g + i))) fun i hi => by
      rw [List.mem_range] at hi
      unfold candI
      rw [show (8 * g + i) / 56 = g / 7 by omega, show (8 * g + i) % 56 = 8 * (g % 7) + i by omega]]

end MlDsaOpt44.Proofs
