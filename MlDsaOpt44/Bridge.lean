import MlDsaOpt44.Math.BridgeMain
/-!
# The verification result in the optimised data flow (WP13)

Pure lemmas, no EVM reasoning. `optAccepts` computes `w′` in the normal
domain as `NTT⁻¹(Â ∘ ẑ) − 2^13 · (c · t1)` (sparse negacyclic product)
instead of FIPS 204's `NTT⁻¹(Â ∘ ẑ − ĉ ∘ NTT(t1 · 2^d))`; the two agree modulo
`q` by linearity of `NTT⁻¹` and the convolution theorem (`NTT⁻¹(ĉ ∘ t̂) = c · t`
in `Z_q[X]/(X^256 + 1)`), and `UseHint` only sees its argument modulo `q`.
Proofs: `Math/Ntt/{Layer,Model,Conv}.lean` (NTT as linear maps over `ZMod q`,
evaluation at the roots of `X^256 + 1`, inverse, convolution),
`Math/BridgeRow.lean` (one row of `w′`), `Math/BridgeMain.lean` (flattening
`verifyInternal` as the reference's `verifyInternal_eq_flat` does).
-/

namespace MlDsaOpt44.Proofs

open MlDsa44

theorem pkLen_eq : pkLen = 1312 := BridgeMain.pkLen_eq

theorem sigLen_eq : sigLen = 2420 := BridgeMain.sigLen_eq

/-- **Bridge**: for calldata of at least `|pk| + |σ|` bytes, the EIP-8355
verdict is the bytecode's flag-and-hash result. -/
theorem accepts_eq_optAccepts (cd : ByteArray) (hcd : 3732 ≤ cd.size) :
    accepts cd = optAccepts cd :=
  BridgeMain.accepts_eq_optAccepts cd hcd

/-- The final hash input is 64 + 768 bytes. -/
theorem finBytes_size (cd : ByteArray) : (finBytes cd).size = 832 :=
  BridgeMain.finBytes_size cd

end MlDsaOpt44.Proofs
