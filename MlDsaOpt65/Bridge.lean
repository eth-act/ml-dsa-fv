import MlDsaOpt65.Layout
import MlDsaOpt44.Math.SpongeG234
/-!
# The verification result in the optimised data flow (ML-DSA-65)

Pure lemmas, no EVM reasoning. `optAccepts` (`Layout.lean`) computes `w′` in
the normal domain as `NTT⁻¹(Â ∘ ẑ) − 2^13 · (c · t1)` (sparse negacyclic
product) instead of FIPS 204's `NTT⁻¹(Â ∘ ẑ − ĉ ∘ NTT(t1 · 2^d))`; the two
agree modulo `q` by linearity of `NTT⁻¹` and the convolution theorem, and
`UseHint` only sees its argument modulo `q`. The ML-DSA-44 proof
(`MlDsaOpt44/Math/BridgeMain.lean`, `BridgeRow.lean`, `Ntt/*`) is the template:
its NTT lemmas are parameter-free (`MlDsa/Bridge44.lean` equates the
parameter-free `MlDsa.Fips204` functions with their `MlDsa44.Fips204` twins);
the row count `k = 6`, `ℓ = 5`, `γ2 = (q − 1)/32` (4-bit `w1Encode`) and the
48-byte `c̃` change.
-/

namespace MlDsaOpt65.Proofs

open MlDsa

theorem pkLen_eq : MlDsa65.pkLen = 1952 := by decide

theorem sigLen_eq : MlDsa65.sigLen = 3309 := by decide

/-- **Bridge** (open): for calldata of at least `|pk| + |σ| = 5261` bytes, the
EIP-8355 verdict `MlDsa65.accepts` (FIPS 204 `ML-DSA.Verify` at
`Params.mldsa65`) is the bytecode's flag-and-hash result `optAccepts`. Proof
plan: mirror `MlDsaOpt44.Proofs.BridgeMain.accepts_eq_optAccepts`
(`verifyInternal` flattened, per-row convolution identity, `useHint` mod `q`,
flag order `((okZ ∧ okH) ∧ okA) ∧ okC`). -/
theorem accepts_eq_optAccepts (cd : ByteArray) (hcd : 5261 ≤ cd.size) :
    MlDsa65.accepts cd = optAccepts cd := by
  sorry

theorem simpleBitPack15_size (w : Fips204.Poly) : (Fips204.simpleBitPack w 15).size = 128 := by
  simp only [Fips204.simpleBitPack]
  simp [ByteArray.size, Fips204.bitlen]
  decide

theorem H_size (msg : ByteArray) (n : Nat) : (Fips204.H msg n).size = n :=
  MlDsaOpt44.Proofs.H_size msg n

/-- The final hash input `μ ‖ w1Encode(w1)` is 64 + 6 · 128 = 832 bytes. -/
theorem finBytes_size (cd : ByteArray) : (finBytes cd).size = 832 := by
  unfold finBytes Fips204.w1Encode
  rw [ByteArray.size_append, muOf, H_size,
    show (Fips204.q - 1) / (2 * P.gamma2) - 1 = 15 from rfl,
    show List.range P.k = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, ByteArray.size_append, simpleBitPack15_size]
  rfl

end MlDsaOpt65.Proofs
