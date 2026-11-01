import MlDsaOpt44.Main.Mu.Spec
set_option warningAsError true
/-!
# The c̃ comparison of `seg_fin`

* `ba_beq_eq`: `==` on byte arrays is equality;
* `eq_of_le64`: 32-byte arrays are equal when their four lanes are;
* `cmp_eq`: comparing the four squeezed lanes with the four c̃ lanes is
  `ctOf cd == H X 32`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem ba_beq_eq (a b : ByteArray) : (a == b) = decide (a = b) := by
  change ByteArray.beq a b = _
  unfold ByteArray.beq
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ByteArray.ext_iff]

theorem le64_beyond (b : ByteArray) {a : Nat} (h : b.size ≤ a) : le64 b a = 0 := by
  have z : ∀ k, byteAt b (a + k) = 0 := fun k => by unfold byteAt; rw [dif_neg (by omega)]
  rw [le64_eq, z, z, z, z, z, z, z, show a = a + 0 by rfl, z]

theorem eq_of_le64 {A B : ByteArray} (hA : A.size = 32) (hB : B.size = 32)
    (h : ∀ k, k < 4 → le64 A (8 * k) = le64 B (8 * k)) : A = B := by
  have hb : ∀ i, i < 32 → byteAt A i = byteAt B i := fun i hi => by
    have := congrArg (byteN · (i % 8)) (h (i / 8) (by omega))
    simp only [byteN_le64 _ _ (Nat.mod_lt i (by omega : 8 > 0))] at this
    rwa [show 8 * (i / 8) + i % 8 = i by omega] at this
  apply ByteArray.ext
  apply Array.ext (by change A.size = B.size; omega)
  intro i h1 h2
  have := hb i (by change i < A.size at h1; omega)
  unfold byteAt at this
  rw [dif_pos (by change i < A.size at h1; exact h1), dif_pos (by change i < B.size at h2; exact h2)] at this
  exact UInt8.toNat_inj.mp this

theorem le64_ctOf {cd : ByteArray} (hcd : HDR ≤ cd.size) {k : Nat} (hk : k < 4) :
    le64 (ctOf cd) (8 * k) = le64 cd (1312 + 8 * k) :=
  le64_congr fun i hi => by
    unfold ctOf
    rw [byteAt_extract _ _ _ _ (by unfold HDR at hcd; omega), if_pos (by omega), Nat.add_assoc]

theorem pack4_inj {v w : Nat → Nat} (hv : ∀ k, k < 4 → v k < 2 ^ 64) (hw : ∀ k, k < 4 → w k < 2 ^ 64) :
    pack4 v = pack4 w ↔ ∀ k, k < 4 → v k = w k := by
  constructor
  · intro h k hk
    rw [← pack4_div_mod hv hk, ← pack4_div_mod hw hk, h]
  · intro h
    unfold pack4
    rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- The comparison bit is the commitment check. -/
theorem cmp_eq (cd X : ByteArray) (hcd : HDR ≤ cd.size) :
    decide ((pack4 fun k => laneOf (Fips202.absorb 136 (Fips202.pad 136 0x1F X)) (3 - k)) =
        pack4 fun k => le64 cd (1312 + 8 * (3 - k))) = (ctOf cd == Fips204.H X 32) := by
  rw [ba_beq_eq]
  have hH : (Fips204.H X 32).size = 32 := shake_size _ (by norm_num)
  have lH : ∀ k, k < 4 → le64 (Fips204.H X 32) (8 * k) =
      laneOf (Fips202.absorb 136 (Fips202.pad 136 0x1F X)) k := fun k hk => by
    have := le64_shake256 X (n := 32) (j := 0) (x := k) (by omega) (by omega)
    simpa [Fips204.H, Fips202.shake256] using this
  apply decide_eq_decide.mpr
  rw [pack4_inj (fun _ _ => laneOf_lt _ _) (fun _ _ => le64_lt _ _)]
  constructor
  · intro h
    apply eq_of_le64 (ctOf_size (by unfold HDR at hcd; omega)) hH
    intro k hk
    have := h (3 - k) (by omega)
    rw [show 3 - (3 - k) = k by omega] at this
    rw [le64_ctOf hcd hk, lH k hk, this]
  · intro h k hk
    rw [← lH (3 - k) (by omega), ← h, le64_ctOf hcd (by omega)]

end MlDsaOpt44.Proofs
