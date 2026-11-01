import MlDsaOpt87.Layout
import MlDsaOpt87.Fn.Csum.Defs
import MlDsaOpt87.Math.G4.Csum
import MlDsaOpt65.Math.G5.Hint
import MlDsaOpt65.Math.M1.Ball
import MlDsaOpt65.Math.M1.Hint
import MlDsaOpt87.Math.M1.Verify
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

/-- SampleInBall (τ = 60) outputs 256 coefficients in `{−1, 0, 1}`
(`MlDsaOpt65/Math/M1/Ball.lean`). -/
theorem sampleInBallOf_coeffs (bs : ByteArray) (c : Fips204.Poly)
    (h : Fips204.sampleInBallOf P bs = some c) :
    c.size = 256 ∧ ∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1 := by
  have := MlDsaOptM1.sampleInBallOf_inv P (by decide) h
  exact ⟨this.1, this.2.1⟩

/-- The `dz` lanes of a 20-bit `z_k` polynomial are `ẑ_k` after the NTT
(`γ1 + q − raw ≡ γ1 − raw`; `MlDsaOpt87/Math/M1/Verify.lean`). -/
theorem ntt_zLane (cd : ByteArray) (_hcd : HDR ≤ cd.size) {k : Nat} (hk : k < 7) :
    Fips204.ntt ((Array.range 256).map fun t => (zLane cd k t : Int)) = zHat cd k :=
  M1.ntt_zLane cd hk

/-- HintBitUnpack (k = 8, ω = 75) outputs 0/1 coefficients (`MlDsaOpt65/Math/M1/Hint.lean`). -/
theorem hintBitUnpack_range (y : ByteArray) (h : Array Fips204.Poly)
    (hh : Fips204.hintBitUnpack P y = some h) {r t : Nat} (hr : r < 8) (ht : t < 256) :
    (0 : Int) ≤ h[r]![t]! ∧ h[r]![t]! ≤ 1 :=
  MlDsaOptM1.hintBitUnpack_range P y h hh hr ht

/-- `UseHint` only sees its argument modulo `q` (`MlDsaOpt65/Math/G5/Hint.lean`). -/
theorem useHint_emod (h r : Int) :
    Fips204.useHint P h (r % (Fips204.q : Int)) = Fips204.useHint P h r :=
  MlDsaOpt65.Proofs.G5.useHint_emod P h r

/-- `UseHint` outputs `r1 ∈ [0, m)`, `m = (q − 1)/(2γ2) = 16` (`MlDsaOpt65/Math/G5/Hint.lean`). -/
theorem useHint_range (h r : Int) : 0 ≤ Fips204.useHint P h r ∧ Fips204.useHint P h r < 16 :=
  MlDsaOpt65.Proofs.G5.useHint_range P rfl h r

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

theorem G5_muOf_size (cd : ByteArray) : (muOf cd).size = 64 := MlDsaOpt44.Proofs.Facts.H_size _ _

/-- The 136 stream lanes of `μ ‖ w1Encode(w1)` (1088 bytes): lanes `0 … 7` are μ. -/
theorem finBytes_le64_mu (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (finBytes cd) (8 * x) = le64 (muOf cd) (8 * x) := by
  unfold MlDsaOpt44.Proofs.le64 finBytes
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [MlDsaOpt44.Proofs.SpecFacts.byteAt_app_lt (by rw [G5_muOf_size]; omega)]

/-- Lane `8 + 16 r + j` of `μ ‖ w1Encode(w1)` is lane `j` of row `r`'s 128-byte
`SimpleBitPack(w1_r, 15)` (`MlDsaOpt65.Proofs.G5.byteAt_w1Encode`). -/
theorem finBytes_le64_w1 (cd : ByteArray) {r j : Nat} (hr : r < 8) (hj : j < 16) :
    le64 (finBytes cd) (8 * (8 + 16 * r + j)) =
      le64 (Fips204.simpleBitPack (w1Of cd)[r]! 15) (8 * j) := by
  unfold MlDsaOpt44.Proofs.le64 finBytes
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [MlDsaOpt44.Proofs.SpecFacts.byteAt_app_ge (by rw [G5_muOf_size]; omega), G5_muOf_size,
    show 8 * (8 + 16 * r + j) + i - 64 = 128 * r + (8 * j + i) by omega,
    MlDsaOpt65.Proofs.G5.byteAt_w1Encode P rfl _ (hr : r < P.k) (by omega)]

end MlDsaOpt87.Proofs
