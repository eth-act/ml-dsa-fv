import MlDsaOpt44.Layout
/-!
# The verification result in the optimised data flow (WP14)

Pure lemmas, no EVM reasoning. `optAccepts` computes `w′` in the normal
domain as `NTT⁻¹(Â ∘ ẑ) − 2^13 · (c · t1)` (sparse negacyclic product)
instead of FIPS 204's `NTT⁻¹(Â ∘ ẑ − ĉ ∘ NTT(t1 · 2^d))`; the two agree by
linearity of `NTT⁻¹` and the convolution theorem (`NTT⁻¹(ĉ ∘ t̂) = c · t` in
`Z_q[X]/(X^256 + 1)`). The reference proof's `verifyInternal_eq_flat`
(`MlDsa44/Proofs/Bridge.lean`) already flattens `verifyInternal` into
independent flags; this module reuses that shape.
-/

namespace MlDsaOpt44.Proofs

open MlDsa44

theorem pkLen_eq : pkLen = 1312 := by
  simp only [pkLen, Fips204.pkLen, Fips204.bitlen, Fips204.k, Fips204.q, Fips204.d]; decide

theorem sigLen_eq : sigLen = 2420 := by
  simp only [sigLen, Fips204.sigLen, Fips204.bitlen, Fips204.k, Fips204.l, Fips204.lambda,
    Fips204.gamma1, Fips204.omega]; decide

/-- **Bridge**: for calldata of at least `|pk| + |σ|` bytes, the EIP-8355
verdict is the bytecode's flag-and-hash result. -/
theorem accepts_eq_optAccepts (cd : ByteArray) (hcd : 3732 ≤ cd.size) :
    accepts cd = optAccepts cd := by
  sorry

/-- The final hash input is 64 + 768 bytes. -/
theorem finBytes_size (cd : ByteArray) : (finBytes cd).size = 832 := by
  sorry

end MlDsaOpt44.Proofs
