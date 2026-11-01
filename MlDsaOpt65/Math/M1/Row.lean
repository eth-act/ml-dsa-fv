import MlDsa.Bridge44
import MlDsaOpt44.Math.BridgeRow
/-!
# Parameter-generic row algebra for the verification bridge (work package M1)

The `MlDsaOpt44.Proofs.RowMath` facts (`toF` of `addNTT`/`multiplyNTT`, the
row identity `nttInv_row`) restated for the parametric `MlDsa.Fips204`
functions through `MlDsa/Bridge44.lean`, the `ℓ`-term `MatrixVectorNTT` fold
as a `Finset` sum, `ExpandA` for any `(k, ℓ)`, the z decoding of `sigDecode`,
and `UseHint`'s dependence on `r mod q` for any `γ2`. Shared by the
ML-DSA-65 and ML-DSA-87 proofs.
-/

namespace MlDsaOptM1

open MlDsa MlDsaOpt44.Proofs.NttConv MlDsaOpt44.Proofs.RowMath

/-! ## UseHint -/

theorem useHint_emod (P : Params) (h r : Int) :
    Fips204.useHint P h (r % (Fips204.q : Int)) = Fips204.useHint P h r := by
  unfold Fips204.useHint Fips204.decompose
  simp only [Int.emod_emod]

theorem useHint_congr (P : Params) (h : Int) {a b : Int} (hab : (a : F) = (b : F)) :
    Fips204.useHint P h a = Fips204.useHint P h b := by
  rw [← useHint_emod P h a, ← useHint_emod P h b]
  exact congrArg _ (eq_of_toF hab)

/-! ## NTT-domain arithmetic (parametric names) -/

theorem cast_emod' (x : Int) : (((x % (Fips204.q : Int) : Int)) : F) = (x : F) := cast_emod x

theorem toF_addNTT' (a b : Fips204.Poly) {j : Nat} (hj : j < 256) :
    toF (Fips204.addNTT a b) j = toF a j + toF b j := by
  rw [Bridge44.addNTT_eq]; exact toF_addNTT a b hj

theorem toF_mulNTT' (a b : Fips204.Poly) {j : Nat} (hj : j < 256) :
    toF (Fips204.multiplyNTT a b) j = toF a j * toF b j := by
  rw [Bridge44.multiplyNTT_eq]; exact toF_mulNTT a b hj

theorem toF_zero' (j : Nat) : toF Fips204.zeroPoly j = 0 := toF_zero j

theorem ntt_map_emod' (f : Fips204.Poly) (hf : f.size = 256) :
    Fips204.ntt (f.map (· % (Fips204.q : Int))) = Fips204.ntt f := by
  rw [Bridge44.ntt_eq]; exact MlDsa44.Proofs.Math.ntt_map_emod f hf

/-- **Row identity**: `X ≡ AZ − NTT(c) ∘ NTT(T)` gives `NTT⁻¹ X ≡ NTT⁻¹ AZ − c · T`. -/
theorem nttInv_row' (X AZ c T : Fips204.Poly) (hX : X.size = 256) (hAZ : AZ.size = 256)
    (hc : c.size = 256) (hT : T.size = 256)
    (h : ∀ j, j < 256 → toF X j = toF AZ j - toF (Fips204.ntt c) j * toF (Fips204.ntt T) j)
    {j : Nat} (hj : j < 256) :
    toF (Fips204.nttInv X) j = toF (Fips204.nttInv AZ) j - negF (toF c) (toF T) j := by
  rw [Bridge44.ntt_eq] at h
  rw [Bridge44.nttInv_eq]
  exact nttInv_row X AZ c T hX hAZ hc hT h hj

/-- `Â ∘ ẑ` row as `MatrixVectorNTT` folds it, for `ℓ` columns. -/
theorem toF_azFold (A zs : Array Fips204.Poly) {j : Nat} (hj : j < 256) : ∀ l,
    toF ((List.range l).foldl
      (fun acc s => Fips204.addNTT acc (Fips204.multiplyNTT A[s]! zs[s]!)) Fips204.zeroPoly) j =
      ∑ s ∈ Finset.range l, toF A[s]! j * toF zs[s]! j
  | 0 => by simp [toF_zero']
  | l + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, toF_addNTT' _ _ hj,
      toF_mulNTT' _ _ hj, toF_azFold A zs hj l, Finset.sum_range_succ]

/-! ## ExpandA -/

/-- `ExpandA` succeeds iff every entry does, and then holds the entries. -/
theorem expandA_eq (P : Params) (rho : ByteArray) :
    Fips204.expandA P rho =
      if (List.range P.k).all (fun r => (List.range P.l).all fun s =>
          (Fips204.rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) then
        some ((Array.range P.k).map fun r => (Array.range P.l).map fun s =>
          (Fips204.rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).getD
            Fips204.zeroPoly)
      else none := by
  unfold Fips204.expandA
  rw [MlDsa44.Proofs.Math.array_mapM_range_option P.k _ #[]]
  simp only [MlDsa44.Proofs.Math.array_mapM_range_option P.l _ Fips204.zeroPoly]
  by_cases hc : (List.range P.k).all (fun r => (List.range P.l).all fun s =>
          (Fips204.rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) = true
  · have hc' := hc
    simp only [List.all_eq_true] at hc'
    rw [if_pos hc]
    rw [if_pos (by simp only [List.all_eq_true]; intro r hr; rw [if_pos (hc' r hr)]; rfl)]
    congr 1
    apply Array.ext (by simp)
    intro i h1 h2
    simp at h1
    have hi := hc' i (by simpa using h1)
    simp only [List.mem_range] at hi
    simp
    rw [if_pos hi]
    rfl
  · rw [if_neg hc, if_neg]
    intro h
    apply hc
    simp only [List.all_eq_true] at h ⊢
    intro r hr
    have := h r hr
    split at this
    · assumption
    · simp at this

/-! ## z as `sigDecode` reads it -/

theorem sigDecode_z_size (P : Params) (sig : ByteArray) : (Fips204.sigDecode P sig).2.1.size = P.l := by
  simp [Fips204.sigDecode]

theorem sigDecode_z_get (P : Params) (sig : ByteArray) {i : Nat} (hi : i < P.l) :
    (Fips204.sigDecode P sig).2.1[i]! =
      Fips204.bitUnpack (sig.extract (P.lambda / 4 + 32 * (1 + Fips204.bitlen (P.gamma1 - 1)) * i)
        (P.lambda / 4 + 32 * (1 + Fips204.bitlen (P.gamma1 - 1)) * (i + 1))) (P.gamma1 - 1) P.gamma1 := by
  rw [getElem!_pos _ i (by rw [sigDecode_z_size]; exact hi)]
  simp only [Fips204.sigDecode, Array.getElem_map, Array.getElem_range]

theorem bitUnpack_size (v : ByteArray) (a b : Nat) : (Fips204.bitUnpack v a b).size = 256 := by
  simp [Fips204.bitUnpack]

theorem bitUnpack_get (v : ByteArray) (a b : Nat) {j : Nat} (hj : j < 256) :
    (Fips204.bitUnpack v a b)[j]! =
      (b : Int) - Fips204.bitsToInteger v (j * Fips204.bitlen (a + b)) (Fips204.bitlen (a + b)) := by
  rw [getElem!_pos _ j (by rw [bitUnpack_size]; exact hj)]
  simp only [Fips204.bitUnpack, Array.getElem_map, Array.getElem_range]

theorem bitsToInteger_lt (v : ByteArray) (p c : Nat) : Fips204.bitsToInteger v p c < 2 ^ c := by
  rw [Bridge44.bitsToInteger_eq]; exact MlDsa44.Proofs.Decode.bitsToInteger_lt v p c

/-! ## `verifyInternal` with the decodings named -/

/-- `Verify_internal` once `pkDecode` and `sigDecode` are named; stated for
an arbitrary parameter set so that no decoding is ever evaluated. -/
theorem verifyInternal_flat (P : Params) (pk M' sig rho cT : ByteArray) (t1 z : Array Fips204.Poly)
    (hint? : Option (Array Fips204.Poly)) (hp : Fips204.pkDecode P pk = (rho, t1))
    (hs : Fips204.sigDecode P sig = (cT, z, hint?)) :
    Fips204.verifyInternal P pk M' sig =
      match (generalizing := false) hint?, Fips204.expandA P rho, Fips204.sampleInBall P cT with
      | some h, some A, some c =>
        Fips204.normBelow z (P.gamma1 - P.beta) &&
          cT == Fips204.H (Fips204.H (Fips204.H pk 64 ++ M') 64 ++ Fips204.w1Encode P
            ((Array.range P.k).map fun i => (Array.range 256).map fun j =>
              Fips204.useHint P h[i]![j]! ((Array.range P.k).map fun i =>
                Fips204.nttInv ((Array.range 256).map fun j =>
                  ((Fips204.matrixVectorNTT P A (z.map Fips204.ntt))[i]![j]! -
                    (Fips204.multiplyNTT (Fips204.ntt c) ((t1.map fun p =>
                      Fips204.ntt (p.map (· * 2 ^ Fips204.d))))[i]!)[j]!) %
                        (Fips204.q : Int)))[i]![j]!)) (P.lambda / 4)
      | _, _, _ => false := by
  rw [Fips204.verifyInternal, hp, hs]
  dsimp only
  rcases hint? with _ | h <;> rcases Fips204.expandA P rho with _ | A <;>
    rcases Fips204.sampleInBall P cT with _ | c <;> rfl

end MlDsaOptM1
