import MlDsaOpt65.Layout
import MlDsaOpt65.Fn.Csum.Defs
import MlDsaOpt65.Math.G4.CsumCore
import MlDsaOpt65.Math.M1.Ball
/-!
# `Math.csum_congr` (WP G4, ML-DSA-65)

The `t1` row `4 g + r` is the 10-bit row `r` read from calldata offset `32 + 1280 g`
(`t1f`), SampleInBall leaves at most `τ = 49` nonzero coefficients
(`MlDsaOptM1.sampleInBallOf_inv`), and `MlDsaOptG4.csum_core` is the identity.
-/

namespace MlDsaOpt65.Proofs.G4

open MlDsa
open MlDsaOpt65.Proofs

theorem t1f_lt (cd : ByteArray) (off r i : Nat) : t1f cd off r i < 1024 :=
  MlDsaOptG4.bitsToInteger_lt _ _ 10

theorem t1Of_get (cd : ByteArray) {g r i : Nat} (hrow : 4 * g + r < 6) (hi : i < 256) :
    (t1Of cd (4 * g + r))[i]! = (t1f cd (32 + 1280 * g) r i : Int) := by
  have hw : Fips204.bitlen (Fips204.q - 1) - Fips204.d = 10 := by decide
  have hc : Fips204.bitlen (2 ^ 10 - 1) = 10 := by decide
  unfold t1Of pkOf Fips204.pkDecode
  simp only [hw]
  rw [show P.k = 6 from rfl, MlDsa44.Proofs.Math.getElem!_map_range 6 _ _ hrow]
  unfold Fips204.simpleBitUnpack
  simp only [hc]
  rw [MlDsa44.Proofs.Math.getElem!_map_range 256 i _ hi, ByteArray.extract_extract, Nat.mul_comm i 10]
  unfold t1f
  have hct : CTOFF = 1952 := rfl
  congr 3 <;> omega

theorem nNeg_sum (c : Fips204.Poly) (t : Nat) :
    nNeg c t = ((List.range 256).map (MlDsaOptG4.np c t)).sum := by
  unfold nNeg
  rw [MlDsaOpt44.Proofs.CsumMath.filter_length]
  congr 1
  apply List.map_congr_left
  intro p _
  unfold MlDsaOptG4.np
  by_cases h : (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1) <;> simp [h]

/-- The body of `Math.csum_congr`. -/
theorem csum_congr_main (cd : ByteArray) (c : Fips204.Poly) (hc : cOf cd = some c) {g r t : Nat}
    (hrow : 4 * g + r < 6) (ht : t < 256) :
    2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t < 2 ^ 29 ∧
      (((2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t : Nat) : Int) -
        2 ^ 13 * negacyclic c (t1Of cd (4 * g + r)) t) % (Fips204.q : Int) = 0 := by
  unfold cOf Fips204.sampleInBall at hc
  obtain ⟨-, hco, hcnt⟩ := MlDsaOptM1.sampleInBallOf_inv P (by decide) hc
  have hτ : P.tau = 49 := rfl
  have e1 : sPrime c cd (32 + 1280 * g) r t =
      ((List.range 256).map (MlDsaOptG4.sp c (t1f cd (32 + 1280 * g) r) t)).sum := rfl
  have e3 : negacyclic c (t1Of cd (4 * g + r)) t =
      ((List.range 256).map (MlDsaOptG4.ng c (t1Of cd (4 * g + r)) t)).sum := rfl
  rw [e1, e3, nNeg_sum]
  exact MlDsaOptG4.csum_core hco (by omega) (t1f_lt cd _ r) (fun i hi => t1Of_get cd hrow hi) ht

/-- The body of `Math.csum_lt`: the lane bound holds for every row read from calldata. -/
theorem csum_lt_main (cd : ByteArray) (c : Fips204.Poly) (hc : cOf cd = some c) (off r t : Nat) :
    2 ^ 13 * sPrime c cd off r t + nNeg c t < 2 ^ 29 := by
  unfold cOf Fips204.sampleInBall at hc
  obtain ⟨-, -, hcnt⟩ := MlDsaOptM1.sampleInBallOf_inv P (by decide) hc
  have hτ : P.tau = 49 := rfl
  have e1 : sPrime c cd off r t = ((List.range 256).map (MlDsaOptG4.sp c (t1f cd off r) t)).sum := rfl
  rw [e1, nNeg_sum]
  have h1 := MlDsaOptG4.sp_le c (t1f_lt cd off r) t 256
  have h2 := MlDsaOptG4.np_le c t 256
  omega

end MlDsaOpt65.Proofs.G4
