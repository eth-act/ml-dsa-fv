set_option warningAsError true
/-!
# FIPS 204 parameter sets

`Params` collects the per-set constants of FIPS 204 Table 1 that the
verification algorithms depend on. The constants shared by all three sets
(`q`, `ζ`, `d`) and the Appendix C sampling limits live in
`MlDsa.Fips204`. Every derived quantity is a function of these fields, written
exactly as FIPS 204 writes it.
-/

namespace MlDsa

/-- FIPS 204 Table 1 parameters used by verification. -/
structure Params where
  /-- Rows of `A`. -/
  k : Nat
  /-- Columns of `A`. -/
  l : Nat
  /-- Private-key range. Enters verification only through `β = τ·η`. -/
  eta : Nat
  /-- Number of ±1 coefficients of the challenge polynomial. -/
  tau : Nat
  /-- Collision strength of `c̃`, in bits. -/
  lambda : Nat
  /-- Coefficient range of `y`. -/
  gamma1 : Nat
  /-- Low-order rounding range. -/
  gamma2 : Nat
  /-- Maximum number of ones in the hint `h`. -/
  omega : Nat

namespace Params

/-- `β = τ · η` (Table 1). -/
def beta (P : Params) : Nat := P.tau * P.eta

/-- ML-DSA-44 (security category 2). -/
def mldsa44 : Params where
  k := 4
  l := 4
  eta := 2
  tau := 39
  lambda := 128
  gamma1 := 2 ^ 17
  gamma2 := (8380417 - 1) / 88
  omega := 80

/-- ML-DSA-65 (security category 3). -/
def mldsa65 : Params where
  k := 6
  l := 5
  eta := 4
  tau := 49
  lambda := 192
  gamma1 := 2 ^ 19
  gamma2 := (8380417 - 1) / 32
  omega := 55

/-- ML-DSA-87 (security category 5). -/
def mldsa87 : Params where
  k := 8
  l := 7
  eta := 2
  tau := 60
  lambda := 256
  gamma1 := 2 ^ 19
  gamma2 := (8380417 - 1) / 32
  omega := 75

/-! Table 1 values, restated as numbers. -/

example : mldsa44.beta = 78 := by decide
example : mldsa65.beta = 196 := by decide
example : mldsa87.beta = 120 := by decide
example : mldsa44.gamma2 = 95232 := by decide
example : mldsa65.gamma2 = 261888 := by decide
example : mldsa87.gamma2 = 261888 := by decide
example : mldsa65.gamma1 = 524288 ∧ mldsa87.gamma1 = 524288 := by decide

end Params

end MlDsa
