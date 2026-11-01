import MlDsaOpt87.Layout
import MlDsaOpt44.Math.SpongeG234
import MlDsaOpt87.Math.M1.Verify
/-!
# The verification result in the optimised data flow (ML-DSA-87)

Pure lemmas, no EVM reasoning. `optAccepts` computes `w′` in the normal
domain as `NTT⁻¹(Â ∘ ẑ) − 2^13 · (c · t1)` (sparse negacyclic product)
instead of FIPS 204's `NTT⁻¹(Â ∘ ẑ − ĉ ∘ NTT(t1 · 2^d))`; the two agree modulo
`q` by linearity of `NTT⁻¹` and the convolution theorem, and `UseHint` only
sees its argument modulo `q`. The ML-DSA-44 proof
(`MlDsaOpt44/Math/{Ntt/*,BridgeRow,BridgeMain}.lean`) is the template; the
parameter-free parts (`ntt`, `nttInv`, the convolution theorem) carry over via
`MlDsa/Bridge44.lean`.
-/

namespace MlDsaOpt87.Proofs

open MlDsa

theorem pkLen_eq : MlDsa87.pkLen = 2592 := by decide

theorem sigLen_eq : MlDsa87.sigLen = 4627 := by decide

/-- **Bridge**: for calldata of at least `|pk| + |σ|` bytes, the EIP-8355
verdict is the bytecode's flag-and-hash result (`k = 8`, `ℓ = 7`: `Fips204.verify P`
flattened, the `‖z‖∞`, hint, `A` and `c` validity checks in `optAccepts`' order, `w′`
row by row by the convolution theorem, `H(μ ‖ w1Encode w1, 64)` compared with `c̃`;
proof in `MlDsaOpt87/Math/M1/Verify.lean`). -/
theorem accepts_eq_optAccepts (cd : ByteArray) (hcd : 7219 ≤ cd.size) :
    MlDsa87.accepts cd = optAccepts cd :=
  M1.accepts_eq_optAccepts cd hcd

theorem simpleBitPack15_size (w : Fips204.Poly) : (Fips204.simpleBitPack w 15).size = 128 := by
  simp only [Fips204.simpleBitPack]
  simp [ByteArray.size, Fips204.bitlen]
  decide

theorem H_size (msg : ByteArray) (n : Nat) : (Fips204.H msg n).size = n :=
  MlDsaOpt44.Proofs.H_size msg n

/-- The final hash input `μ ‖ w1Encode(w1)` is 64 + 8 · 128 = 1088 bytes. -/
theorem finBytes_size (cd : ByteArray) : (finBytes cd).size = 1088 := by
  unfold finBytes Fips204.w1Encode
  rw [ByteArray.size_append, muOf, H_size,
    show (Fips204.q - 1) / (2 * P.gamma2) - 1 = 15 from rfl,
    show List.range P.k = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, ByteArray.size_append, simpleBitPack15_size]
  rfl

end MlDsaOpt87.Proofs
