import MlDsaOpt87.Layout
import MlDsaOpt87.Fn.Csum.Defs
import MlDsaOpt87.Math.G4.Csum
import MlDsaOpt44.Math
import MlDsa.Bridge44
/-!
# Pure lemmas for the ML-DSA-87 proof

The word/lane lemmas of `MlDsaOpt44/Math.lean` (`pack4_lt`, `lane_pack4`,
`pack4_add_mul`, `word_zero_of_zeroOn`, `ite01_land`, `lanesPoly_get`, …) are
about the shared vocabulary and apply verbatim (namespace `MlDsaOpt44.Proofs`).

This file states the spec-level facts the ML-DSA-87 segments are expected to
need, against `MlDsa.Fips204` at `P = Params.mldsa87`. The parameter-free ones
are proved from the ML-DSA-44 facts through `MlDsa/Bridge44.lean`; the
parameter-dependent ones are open (work package MATH in `PLAN.md`): their 44
proofs (`MlDsaOpt44/Math/{Facts,SpecFacts,Csum}.lean`) are the template.
-/

namespace MlDsaOpt87.Proofs

open MlDsa

/-! ## Parameter-free facts (proved from ML-DSA-44) -/

theorem cStream_size (cd : ByteArray) : (cStream cd).size = 272 :=
  MlDsaOpt44.Proofs.Facts.H_size _ _

/-- RejNTTPoly outputs 256 coefficients in `[0, q)`. -/
theorem rejNTTPoly_range (seed : ByteArray) (a : Fips204.Poly)
    (h : Fips204.rejNTTPoly seed = some a) :
    a.size = 256 ∧ ∀ t, t < 256 → (0 : Int) ≤ a[t]! ∧ a[t]! < (Fips204.q : Int) := by
  rw [Bridge44.rejNTTPoly_eq] at h
  exact MlDsaOpt44.Proofs.rejNTTPoly_range seed a h

/-- `NTT⁻¹` only depends on its input modulo `q`. -/
theorem nttInv_congr (x y : Fips204.Poly) (hx : x.size = 256) (hy : y.size = 256)
    (h : ∀ t, t < 256 → (x[t]! - y[t]!) % (Fips204.q : Int) = 0) :
    Fips204.nttInv x = Fips204.nttInv y := by
  rw [Bridge44.nttInv_eq]
  exact MlDsaOpt44.Proofs.nttInv_congr x y hx hy h

/-- `NTT⁻¹` outputs reduced coefficients. -/
theorem nttInv_range (x : Fips204.Poly) (t : Nat) (ht : t < 256) :
    (0 : Int) ≤ (Fips204.nttInv x)[t]! ∧ (Fips204.nttInv x)[t]! < (Fips204.q : Int) := by
  rw [Bridge44.nttInv_eq]
  exact MlDsaOpt44.Proofs.nttInv_range x t ht

/-! ## Parameter-dependent facts (open) -/

/-- SampleInBall (τ = 60) outputs 256 coefficients in `{−1, 0, 1}`.
Template: `MlDsaOpt44.Proofs.Facts.sampleInBallOf_inv`. -/
theorem sampleInBallOf_coeffs (bs : ByteArray) (c : Fips204.Poly)
    (h : Fips204.sampleInBallOf P bs = some c) :
    c.size = 256 ∧ ∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1 := by
  sorry

/-- The `dz` lanes of a 20-bit `z_k` polynomial are `ẑ_k` after the NTT
(`γ1 + q − raw ≡ γ1 − raw`). Template: `MlDsaOpt44.Proofs.SpecFacts.ntt_zLane`. -/
theorem ntt_zLane (cd : ByteArray) (hcd : HDR ≤ cd.size) {k : Nat} (hk : k < 7) :
    Fips204.ntt ((Array.range 256).map fun t => (zLane cd k t : Int)) = zHat cd k := by
  sorry

/-- HintBitUnpack (k = 8, ω = 75) outputs 0/1 coefficients.
Template: `MlDsaOpt44.Proofs.Facts.hintBitUnpack_range`. -/
theorem hintBitUnpack_range (y : ByteArray) (h : Array Fips204.Poly)
    (hh : Fips204.hintBitUnpack P y = some h) {r t : Nat} (hr : r < 8) (ht : t < 256) :
    (0 : Int) ≤ h[r]![t]! ∧ h[r]![t]! ≤ 1 := by
  sorry

/-- `UseHint` only sees its argument modulo `q`. Template: `Facts.useHint_emod`. -/
theorem useHint_emod (h r : Int) :
    Fips204.useHint P h (r % (Fips204.q : Int)) = Fips204.useHint P h r := by
  sorry

/-- `UseHint` outputs `r1 ∈ [0, m)`, `m = (q − 1)/(2γ2) = 16`. Template: `Facts.useHint_range`. -/
theorem useHint_range (h r : Int) : 0 ≤ Fips204.useHint P h r ∧ Fips204.useHint P h r < 16 := by
  sorry

set_option linter.unusedVariables false in
/-- The windowed-sum identity behind `csum` (row group `g`, `t1` offset
`32 + 1280 g`): `2^13 S'_r(t) + n_neg(t) ≡ 2^13 (c · t1_{4g+r})(t)` (negacyclic) mod `q`,
and the lane value is below `2^29` (τ · 1023 < 2^16). Proof: `Math/G4/Csum.lean` (WP G4). -/
theorem csum_congr (cd : ByteArray) (hcd : HDR ≤ cd.size) (c : Fips204.Poly)
    (hc : cOf cd = some c) {g r t : Nat} (hg : g < 2) (hr : r < 4) (hrow : 4 * g + r < 8)
    (ht : t < 256) :
    2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t < 2 ^ 29 ∧
      (((2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t : Nat) : Int) -
        2 ^ 13 * negacyclic c (t1Of cd (4 * g + r)) t) % (Fips204.q : Int) = 0 := by
  exact G4.csum_congr_main cd c hc hrow ht

set_option linter.unusedVariables false in
/-- The `csum` lane bound for every row of both row groups (as `MlDsaOpt65.Proofs.csum_lt`;
here every row exists). -/
theorem csum_lt (cd : ByteArray) (hcd : HDR ≤ cd.size) (c : Fips204.Poly)
    (hc : cOf cd = some c) {g r t : Nat} (hg : g < 2) (hr : r < 4) (ht : t < 256) :
    2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t < 2 ^ 29 :=
  G4.csum_lt_main cd c hc _ r t

/-- The 136 stream lanes of `μ ‖ w1Encode(w1)` (1088 bytes): lanes `0 … 7` are μ. -/
theorem finBytes_le64_mu (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (finBytes cd) (8 * x) = le64 (muOf cd) (8 * x) := by
  sorry

/-- Lane `8 + 16 r + j` of `μ ‖ w1Encode(w1)` is lane `j` of row `r`'s 128-byte
`SimpleBitPack(w1_r, 15)`. Template: `SpecFacts.finBytes_le64_w1`. -/
theorem finBytes_le64_w1 (cd : ByteArray) {r j : Nat} (hr : r < 8) (hj : j < 16) :
    le64 (finBytes cd) (8 * (8 + 16 * r + j)) =
      le64 (Fips204.simpleBitPack (w1Of cd)[r]! 15) (8 * j) := by
  sorry

end MlDsaOpt87.Proofs
