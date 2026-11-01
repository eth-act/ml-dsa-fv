import MlDsaOpt44.Math.BridgeMain
import MlDsaOpt44.Math.Csum
/-!
# Proofs of the spec-level facts stated in `Math.lean`

`Math.lean` states them in the shape the segments consume; this module proves
them (and `csum_congr` up to unfolding `sPrime`/`nNeg`, which live in `Fn/Ct.lean`).
-/

namespace MlDsaOpt44.Proofs.SpecFacts

open MlDsa44 MlDsaOptCommon MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttConv

theorem cStream_size (cd : ByteArray) : (cStream cd).size = 272 :=
  Facts.H_size _ _

theorem poly_ext (a b : Fips204.Poly) (ha : a.size = 256) (hb : b.size = 256)
    (h : ∀ t, t < 256 → a[t]! = b[t]!) : a = b := by
  apply Array.ext (by omega)
  intro t h1 h2
  have := h t (by omega)
  rwa [getElem!_pos a t h1, getElem!_pos b t h2] at this

theorem ntt_zLane (cd : ByteArray) (hcd : HDR ≤ cd.size) {k : Nat} (hk : k < 4) :
    Fips204.ntt ((Array.range 256).map fun t => (zLane cd k t : Int)) = zHat cd k := by
  have hA : ((Array.range 256).map fun t => (zLane cd k t : Int)).size = 256 := by
    rw [Array.size_map, Array.size_range]
  have hZ := BridgeMain.zPolys_get_size cd hk
  have hA' : (((Array.range 256).map fun t => (zLane cd k t : Int)).map
      (· % (Fips204.q : Int))).size = 256 := by rw [Array.size_map, hA]
  have hZ' : ((zPolys cd)[k]!.map (· % (Fips204.q : Int))).size = 256 := by
    rw [Array.size_map, hZ]
  refine (Proofs.Math.ntt_map_emod _ hA).symm.trans (congrArg Fips204.ntt (poly_ext _ _ hA' hZ' ?_))
  intro t ht
  rw [Proofs.Math.getElem!_map ((Array.range 256).map fun t => (zLane cd k t : Int))
      (· % (Fips204.q : Int)) t (by rw [hA]; exact ht),
    Proofs.Math.getElem!_map (zPolys cd)[k]! (· % (Fips204.q : Int)) t (by rw [hZ]; exact ht),
    Proofs.Math.getElem!_map_range 256 t _ ht]
  unfold zPolys sigOf
  rw [Proofs.Decode.sigDecode_z_coeff (by unfold HDR at hcd; omega) hk ht]
  have hr : rawZ cd k t = Proofs.Decode.rawZ cd k t := by
    unfold rawZ Proofs.Decode.rawZ Z0
    rw [show 1344 + 576 * (k + 1) = 1344 + 576 * k + 576 by ring, Nat.mul_comm 18 t]
  have hlt := Proofs.Decode.rawZ_lt cd k t
  have hq : ((Fips204.q : Nat) : Int) = 8380417 := rfl
  unfold zLane
  rw [hr, hq, show Fips204.q = 8380417 from rfl]
  omega

theorem nttInv_congr (x y : Fips204.Poly) (hx : x.size = 256) (hy : y.size = 256)
    (h : ∀ t, t < 256 → (x[t]! - y[t]!) % (Fips204.q : Int) = 0) :
    Fips204.nttInv x = Fips204.nttInv y := by
  obtain ⟨sx, ex⟩ := nttInv_spec x hx
  obtain ⟨sy, ey⟩ := nttInv_spec y hy
  have hq : ((Fips204.q : Nat) : Int) = 8380417 := rfl
  have hxy : ∀ j, j < 256 → toF x j = toF y j := by
    intro j hj
    have := h j hj
    rw [hq] at this
    unfold toF
    exact (ZMod.intCast_eq_intCast_iff' _ _ 8380417).2 (by omega)
  apply poly_ext _ _ sx sy
  intro t ht
  have e : toF (Fips204.nttInv x) t = toF (Fips204.nttInv y) t := by
    rw [ex t ht, ey t ht, If_congr hxy 8 (Nat.le_refl _) t ht]
  have e2 := RowMath.eq_of_toF e
  have r1 := nttInv_reduced x ht
  have r2 := nttInv_reduced y ht
  rw [hq] at e2 r1 r2
  omega

/-- `csum_congr` with `sPrime`, `nNeg`, `negacyclic` as explicit sums. -/
theorem csum_sums (cd : ByteArray) (c : Fips204.Poly)
    (hc : Fips204.sampleInBallOf (cStream cd) = some c) {r t : Nat} (hr : r < 4) (ht : t < 256) :
    2 ^ 13 * ((List.range 256).map (CsumMath.sp c cd r t)).sum +
        ((List.range 256).map (CsumMath.np c t)).sum < 2 ^ 29 ∧
      (((2 ^ 13 * ((List.range 256).map (CsumMath.sp c cd r t)).sum +
          ((List.range 256).map (CsumMath.np c t)).sum : Nat) : Int) -
        2 ^ 13 * ((List.range 256).map (CsumMath.ng c cd r t)).sum) % (Fips204.q : Int) = 0 := by
  obtain ⟨-, hcoef, hcnt⟩ := Facts.sampleInBallOf_inv hc
  refine ⟨?_, ?_⟩
  · have h1 := CsumMath.sp_le (c := c) cd r t 256
    have h2 := CsumMath.np_le c t 256
    omega
  · rw [CsumMath.sums cd hr ht hcoef 256 (Nat.le_refl _)]
    exact Int.mul_emod_right _ _

theorem nNeg_eq (c : Fips204.Poly) (t : Nat) :
    ((List.range 256).filter fun p => (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1)).length =
      ((List.range 256).map (CsumMath.np c t)).sum := by
  rw [CsumMath.filter_length]
  congr 1
  apply List.map_congr_left
  intro p _
  unfold CsumMath.np
  by_cases h : (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1) <;> simp [h]

/-! ## Bytes of `μ ‖ w1Encode(w1)` -/

theorem byteAt_app (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  unfold byteAt
  by_cases h : i < a.size
  · rw [if_pos h, dif_pos (by rw [ByteArray.size_append]; omega), dif_pos h,
      ByteArray.getElem_append_left h]
  · rw [if_neg h]
    by_cases h2 : i - a.size < b.size
    · rw [dif_pos (by rw [ByteArray.size_append]; omega), dif_pos h2,
        ByteArray.getElem_append_right (by omega)]
    · rw [dif_neg (by rw [ByteArray.size_append]; omega), dif_neg h2]

theorem muOf_size (cd : ByteArray) : (muOf cd).size = 64 := Facts.H_size _ _

theorem w1Encode_eq (W : Array Fips204.Poly) :
    Fips204.w1Encode W = ByteArray.empty ++ Fips204.simpleBitPack W[0]! 43 ++
      Fips204.simpleBitPack W[1]! 43 ++ Fips204.simpleBitPack W[2]! 43 ++
      Fips204.simpleBitPack W[3]! 43 := by
  unfold Fips204.w1Encode
  rw [show (Fips204.q - 1) / (2 * Fips204.gamma2) - 1 = 43 from rfl,
    show List.range Fips204.k = [0, 1, 2, 3] from rfl]
  rfl

theorem byteAt_app_lt {a b : ByteArray} {i : Nat} (h : i < a.size) : byteAt (a ++ b) i = byteAt a i := by
  rw [byteAt_app, if_pos h]

theorem byteAt_app_ge {a b : ByteArray} {i : Nat} (h : a.size ≤ i) :
    byteAt (a ++ b) i = byteAt b (i - a.size) := by
  rw [byteAt_app, if_neg (by omega)]

theorem byteAt_w1Encode (W : Array Fips204.Poly) {r o : Nat} (hr : r < 4) (ho : o < 192) :
    byteAt (Fips204.w1Encode W) (192 * r + o) = byteAt (Fips204.simpleBitPack W[r]! 43) o := by
  rw [w1Encode_eq]
  have p0 := Proofs.Hint.simpleBitPack43_size W[0]!
  have p1 := Proofs.Hint.simpleBitPack43_size W[1]!
  have p2 := Proofs.Hint.simpleBitPack43_size W[2]!
  have se : ByteArray.empty.size = 0 := rfl
  have s0 : (ByteArray.empty ++ Fips204.simpleBitPack W[0]! 43).size = 192 := by
    rw [ByteArray.size_append, se, p0]
  have s1 : (ByteArray.empty ++ Fips204.simpleBitPack W[0]! 43 ++
      Fips204.simpleBitPack W[1]! 43).size = 384 := by rw [ByteArray.size_append, s0, p1]
  have s2 : (ByteArray.empty ++ Fips204.simpleBitPack W[0]! 43 ++ Fips204.simpleBitPack W[1]! 43 ++
      Fips204.simpleBitPack W[2]! 43).size = 576 := by rw [ByteArray.size_append, s1, p2]
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  · rw [byteAt_app_lt (by rw [s2]; omega), byteAt_app_lt (by rw [s1]; omega),
      byteAt_app_lt (by rw [s0]; omega), byteAt_app_ge (by rw [se]; omega), se]
    exact congrArg _ (by omega)
  · rw [byteAt_app_lt (by rw [s2]; omega), byteAt_app_lt (by rw [s1]; omega),
      byteAt_app_ge (by rw [s0]; omega), s0]
    exact congrArg _ (by omega)
  · rw [byteAt_app_lt (by rw [s2]; omega), byteAt_app_ge (by rw [s1]; omega), s1]
    exact congrArg _ (by omega)
  · rw [byteAt_app_ge (by rw [s2]; omega), s2]
    exact congrArg _ (by omega)

theorem finBytes_le64_mu (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (finBytes cd) (8 * x) = le64 (muOf cd) (8 * x) := by
  unfold le64 finBytes
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [byteAt_app_lt (by rw [muOf_size]; omega)]

theorem finBytes_le64_w1 (cd : ByteArray) {r j : Nat} (hr : r < 4) (hj : j < 24) :
    le64 (finBytes cd) (8 * (8 + 24 * r + j)) =
      le64 (Fips204.simpleBitPack (w1Of cd)[r]! 43) (8 * j) := by
  unfold le64 finBytes
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [byteAt_app_ge (by rw [muOf_size]; omega), muOf_size,
    show 8 * (8 + 24 * r + j) + i - 64 = 192 * r + (8 * j + i) by omega,
    byteAt_w1Encode _ hr (by omega)]

end MlDsaOpt44.Proofs.SpecFacts
