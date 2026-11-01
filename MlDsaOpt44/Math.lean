import MlDsaOpt44.Fn.Ct.Defs
import MlDsaOpt44.Math.SpecFacts
/-!
# Pure lemmas used by the main-flow segments

Word/lane arithmetic (proved here) and spec-level facts (proved in `Math/*.lean`):
output sizes of SHAKE, coefficient ranges of the samplers, NTT congruences,
the sparse `c · t1` identity, `UseHint` range and `w1Encode` layout.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa44

/-! ## Lanes (proved) -/

theorem pack4_lt {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) : pack4 v < 2 ^ 256 := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem lane_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] <;> omega

theorem pack4_add_mul (v a : Nat → Nat) (z : Nat) :
    pack4 v + pack4 a * z = pack4 fun r => v r + a r * z := by
  unfold pack4; ring

theorem word_zero_of_zeroOn {m : ByteArray} {lo hi a : Nat} (hz : ZeroOn m lo hi) (h1 : lo ≤ a)
    (h2 : a + 32 ≤ hi) : word m a = 0 := by
  rw [word_eq_beNat]
  have : ∀ w, w ≤ 32 → beNat m a w = 0 := by
    intro w hw
    induction w with
    | zero => rfl
    | succ w ih => simp only [beNat, ih (by omega), hz (a + w) (by omega) (by omega)]
  exact this 32 le_rfl

theorem ite01_land (a b : Bool) :
    ((if a = true then 1 else 0 : Nat) &&& (if b = true then 1 else 0)) =
      if (b && a) = true then 1 else 0 := by
  cases a <;> cases b <;> rfl

theorem getElem!_map_range {β : Type} [Inhabited β] (n i : Nat) (F : Nat → β) (h : i < n) :
    ((Array.range n).map F)[i]! = F i := by
  simp [getElem!_pos, h]

theorem lanesPoly_size (m : ByteArray) (base k : Nat) : (lanesPoly m base k).size = 256 := by
  simp [lanesPoly]

theorem lanesPoly_get (m : ByteArray) (base k : Nat) {t : Nat} (ht : t < 256) :
    (lanesPoly m base k)[t]! = (lane (word m (base + 32 * t)) k : Int) := by
  unfold lanesPoly; exact getElem!_map_range 256 t _ ht

theorem azRow_size (cd : ByteArray) (r : Nat) : (azRow cd r).size = 256 := by
  simp [azRow]

theorem wRow_get (cd : ByteArray) (r : Nat) {t : Nat} (ht : t < 256) :
    (wRow cd r)[t]! = ((Fips204.nttInv (azRow cd r))[t]! -
      2 ^ 13 * negacyclic (cD cd) (t1Of cd r) t) % (Fips204.q : Int) := by
  unfold wRow; exact getElem!_map_range 256 t _ ht

theorem w1Of_row (cd : ByteArray) {r : Nat} (hr : r < 4) :
    (w1Of cd)[r]! = (Array.range 256).map fun t =>
      Fips204.useHint (hintD cd)[r]![t]! (wRow cd r)[t]! := by
  unfold w1Of; exact getElem!_map_range 4 r _ hr

theorem w1Of_get (cd : ByteArray) {r t : Nat} (hr : r < 4) (ht : t < 256) :
    (w1Of cd)[r]![t]! = Fips204.useHint (hintD cd)[r]![t]! (wRow cd r)[t]! := by
  rw [w1Of_row cd hr]; exact getElem!_map_range 256 t _ ht

theorem zLane_lt (cd : ByteArray) (k t : Nat) : zLane cd k t < 2 ^ 25 := by
  unfold zLane Fips204.q; omega

/-! ## Spec-level facts

Proved in `Math/{Facts,Csum,SpecFacts}.lean` and `Math/Ntt/*.lean`. -/

/-- `H(c̃)` truncated to the SampleInBall bound has 272 bytes. -/
theorem cStream_size (cd : ByteArray) : (cStream cd).size = 272 := by
  exact SpecFacts.cStream_size cd

/-- SampleInBall outputs 256 coefficients in `{−1, 0, 1}`. -/
theorem sampleInBallOf_coeffs (bs : ByteArray) (c : Fips204.Poly)
    (h : Fips204.sampleInBallOf bs = some c) :
    c.size = 256 ∧ ∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1 := by
  obtain ⟨h1, h2, -⟩ := Facts.sampleInBallOf_inv h
  exact ⟨h1, h2⟩

/-- RejNTTPoly outputs 256 coefficients in `[0, q)`. -/
theorem rejNTTPoly_range (seed : ByteArray) (a : Fips204.Poly)
    (h : Fips204.rejNTTPoly seed = some a) :
    a.size = 256 ∧ ∀ t, t < 256 → (0 : Int) ≤ a[t]! ∧ a[t]! < (Fips204.q : Int) := by
  exact Facts.rejNTTPoly_range seed a h

/-- `dz`'s lanes are `z mod q` representatives, so their NTT is `ẑ`. -/
theorem ntt_zLane (cd : ByteArray) (hcd : HDR ≤ cd.size) {k : Nat} (hk : k < 4) :
    Fips204.ntt ((Array.range 256).map fun t => (zLane cd k t : Int)) = zHat cd k := by
  exact SpecFacts.ntt_zLane cd hcd hk

/-- `NTT⁻¹` only depends on its input modulo `q`. -/
theorem nttInv_congr (x y : Fips204.Poly) (hx : x.size = 256) (hy : y.size = 256)
    (h : ∀ t, t < 256 → (x[t]! - y[t]!) % (Fips204.q : Int) = 0) :
    Fips204.nttInv x = Fips204.nttInv y := by
  exact SpecFacts.nttInv_congr x y hx hy h

/-- `NTT⁻¹` outputs are reduced. -/
theorem nttInv_range (x : Fips204.Poly) (t : Nat) (ht : t < 256) :
    (0 : Int) ≤ (Fips204.nttInv x)[t]! ∧ (Fips204.nttInv x)[t]! < (Fips204.q : Int) := by
  exact NttConv.nttInv_reduced x ht

set_option linter.unusedVariables false in
/-- **The sparse product identity**: `2^13 · 1023 = q − 1`, so
`2^13 S'_r(t) + n_neg(t) ≡ 2^13 (c · t1_r)(t)` (negacyclic) mod q, and the
lane value is below `2^29`. -/
theorem csum_congr (cd : ByteArray) (hcd : HDR ≤ cd.size) (c : Fips204.Poly)
    (hc : Fips204.sampleInBallOf (cStream cd) = some c) {r t : Nat} (hr : r < 4) (ht : t < 256) :
    2 ^ 13 * sPrime c cd r t + nNeg c t < 2 ^ 29 ∧
      (((2 ^ 13 * sPrime c cd r t + nNeg c t : Nat) : Int) -
        2 ^ 13 * negacyclic c (t1Of cd r) t) % (Fips204.q : Int) = 0 := by
  have e1 : sPrime c cd r t = ((List.range 256).map (CsumMath.sp c cd r t)).sum := rfl
  have e3 : negacyclic c (t1Of cd r) t = ((List.range 256).map (CsumMath.ng c cd r t)).sum := rfl
  rw [e1, e3, show nNeg c t = _ from SpecFacts.nNeg_eq c t]
  exact SpecFacts.csum_sums cd c hc hr ht

/-- Decoded hints are bits. -/
theorem hintBitUnpack_range (y : ByteArray) (h : Array Fips204.Poly)
    (hh : Fips204.hintBitUnpack y = some h) {r t : Nat} (hr : r < 4) (ht : t < 256) :
    (0 : Int) ≤ h[r]![t]! ∧ h[r]![t]! ≤ 1 := by
  exact Facts.hintBitUnpack_range y h hh hr ht

/-- `UseHint` only depends on `r mod q` and lands in `[0, 44)`. -/
theorem useHint_emod (h r : Int) : Fips204.useHint h (r % (Fips204.q : Int)) = Fips204.useHint h r := by
  exact Facts.useHint_emod h r

theorem useHint_range (h r : Int) : 0 ≤ Fips204.useHint h r ∧ Fips204.useHint h r < 44 := by
  exact Facts.useHint_range h r

/-- The 104 stream lanes of `μ ‖ w1Encode(w1)`: lanes `0 … 7` are μ, lane
`8 + 24 r + j` is lane `j` of row `r`'s 192-byte `SimpleBitPack`. -/
theorem finBytes_le64_mu (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (finBytes cd) (8 * x) = le64 (muOf cd) (8 * x) := by
  exact SpecFacts.finBytes_le64_mu cd hx

theorem finBytes_le64_w1 (cd : ByteArray) {r j : Nat} (hr : r < 4) (hj : j < 24) :
    le64 (finBytes cd) (8 * (8 + 24 * r + j)) =
      le64 (Fips204.simpleBitPack (w1Of cd)[r]! 43) (8 * j) := by
  exact SpecFacts.finBytes_le64_w1 cd hr hj

end MlDsaOpt44.Proofs
