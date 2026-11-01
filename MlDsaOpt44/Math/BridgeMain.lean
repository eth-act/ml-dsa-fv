import MlDsaOpt44.Math.BridgeRow
import MlDsa44.Proofs.Math.Hint.Pack
/-!
# The verification result in the optimised data flow (WP13)

Pure lemmas, no EVM reasoning. `optAccepts` computes `w′` in the normal
domain as `NTT⁻¹(Â ∘ ẑ) − 2^13 · (c · t1)` (sparse negacyclic product)
instead of FIPS 204's `NTT⁻¹(Â ∘ ẑ − ĉ ∘ NTT(t1 · 2^d))`; the two agree modulo
`q` by linearity of `NTT⁻¹` and the convolution theorem (`NTT⁻¹(ĉ ∘ t̂) = c · t`
in `Z_q[X]/(X^256 + 1)`, `MlDsaOpt44/Math/Ntt/Conv.lean`), and `UseHint` only
sees its argument modulo `q`. `verifyInternal_opt` flattens `verifyInternal`
into independent flags as the reference's `verifyInternal_eq_flat` does.
-/

namespace MlDsaOpt44.Proofs.BridgeMain

open MlDsa44 MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttConv MlDsaOpt44.Proofs.RowMath

theorem pkLen_eq : pkLen = 1312 := by
  simp only [pkLen, Fips204.pkLen, Fips204.bitlen, Fips204.k, Fips204.q, Fips204.d]; decide

theorem sigLen_eq : sigLen = 2420 := by
  simp only [sigLen, Fips204.sigLen, Fips204.bitlen, Fips204.k, Fips204.l, Fips204.lambda,
    Fips204.gamma1, Fips204.omega]; decide

/-- The `A` matrix `ExpandA` returns when every entry succeeds. -/
def aMat (cd : ByteArray) : Array (Array Fips204.Poly) :=
  (Array.range 4).map fun r => (Array.range 4).map fun s =>
    (Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).getD
      Fips204.zeroPoly

theorem t1_size (cd : ByteArray) {r : Nat} (hr : r < 4) : (t1Of cd r).size = 256 := by
  unfold t1Of pkOf Fips204.pkDecode
  rw [show Fips204.k = 4 from rfl, Proofs.Math.getElem!_map_range 4 r _ hr]
  simp [Fips204.simpleBitUnpack]

theorem zPolys_size (cd : ByteArray) : (zPolys cd).size = 4 := by
  simp [zPolys, Fips204.sigDecode, Fips204.l]

theorem zPolys_get_size (cd : ByteArray) {s : Nat} (hs : s < 4) : (zPolys cd)[s]!.size = 256 := by
  unfold zPolys sigOf
  rw [Proofs.Decode.sigDecode_z_get cd hs, Proofs.Decode.bitUnpack_size]

/-- **Row identity**: the spec's `w′Approx` row and `wRow` agree modulo `q`. -/
theorem wApprox_congr (cd : ByteArray) {c : Fips204.Poly} (hcs : c.size = 256) (hc : cD cd = c)
    {i : Nat} (hi : i < 4) {j : Nat} (hj : j < 256) :
    toF (Fips204.nttInv ((Array.range 256).map fun j =>
        ((Fips204.matrixVectorNTT (aMat cd) ((zPolys cd).map Fips204.ntt))[i]![j]! -
          (Fips204.multiplyNTT (Fips204.ntt c) (((Fips204.pkDecode (pkOf cd)).2.map fun p =>
            Fips204.ntt (p.map (· * 2 ^ Fips204.d))))[i]!)[j]!) % (Fips204.q : Int))) j =
      toF (wRow cd i) j := by
  have ht1s : (Fips204.pkDecode (pkOf cd)).2.size = 4 := by simp [Fips204.pkDecode, Fips204.k]
  have hT : ((t1Of cd i).map (· * 2 ^ Fips204.d)).size = 256 := by simp [t1_size cd hi]
  refine (nttInv_row _ (azRow cd i) c ((t1Of cd i).map (· * 2 ^ Fips204.d)) ?_ ?_ hcs hT ?_
    hj).trans ?_
  · simp
  · simp [azRow]
  rotate_left
  · unfold wRow
    rw [toF_map_range _ hj, cast_emod, Int.cast_sub, Int.cast_mul, negacyclic_cast, ← hc]
    have : negF (toF (cD cd)) (toF ((t1Of cd i).map (· * 2 ^ Fips204.d))) j =
        negF (toF (cD cd)) (fun k => (2 ^ 13 : F) * toF (t1Of cd i) k) j := by
      apply negF_congr _ _ hj
      intro k hk
      rw [toF_map _ _ (by rw [t1_size cd hi]; exact hk), Int.cast_mul, mul_comm]
      rfl
    rw [this, negF_smul]
    push_cast
    rfl
  · intro j hj
    rw [toF_map_range _ hj, cast_emod, Int.cast_sub]
    have hz : ∀ s, s < 4 → ((zPolys cd).map Fips204.ntt)[s]! = zHat cd s := by
      intro s hs
      rw [Proofs.Math.getElem!_map _ _ _ (by rw [zPolys_size]; exact hs), zHat,
        Proofs.Math.ntt_map_emod _ (zPolys_get_size cd hs)]
    have hA : ∀ s, s < 4 → (aMat cd)[i]![s]! = aD cd i s := by
      intro s hs
      rw [aMat, Proofs.Math.getElem!_map_range 4 i _ hi, Proofs.Math.getElem!_map_range 4 s _ hs]
      rfl
    have e1 : (Fips204.matrixVectorNTT (aMat cd) ((zPolys cd).map Fips204.ntt))[i]! =
        (List.range Fips204.l).foldl (fun acc s => Fips204.addNTT acc
          (Fips204.multiplyNTT (aMat cd)[i]![s]! ((zPolys cd).map Fips204.ntt)[s]!)) Fips204.zeroPoly := by
      unfold Fips204.matrixVectorNTT
      exact Proofs.Math.getElem!_map_range 4 i _ hi
    have e2 : ((Fips204.pkDecode (pkOf cd)).2.map fun p => Fips204.ntt (p.map (· * 2 ^ Fips204.d)))[i]! =
        Fips204.ntt ((t1Of cd i).map (· * 2 ^ Fips204.d)) :=
      Proofs.Math.getElem!_map _ _ _ (by rw [ht1s]; exact hi)
    have e3 : ((Fips204.matrixVectorNTT (aMat cd) ((zPolys cd).map Fips204.ntt))[i]![j]! : F) =
        toF ((Fips204.matrixVectorNTT (aMat cd) ((zPolys cd).map Fips204.ntt))[i]!) j := rfl
    have e4 : (((Fips204.multiplyNTT (Fips204.ntt c) ((Fips204.pkDecode (pkOf cd)).2.map fun p =>
        Fips204.ntt (p.map (· * 2 ^ Fips204.d)))[i]!)[j]! : Int) : F) =
        toF (Fips204.multiplyNTT (Fips204.ntt c) ((Fips204.pkDecode (pkOf cd)).2.map fun p =>
          Fips204.ntt (p.map (· * 2 ^ Fips204.d)))[i]!) j := rfl
    rw [e3, e4, toF_mulNTT _ _ hj, e2, e1, toF_azFold _ _ hj, toF_azRow cd i hj,
      hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
      hz 0 (by omega), hz 1 (by omega), hz 2 (by omega), hz 3 (by omega)]

/-- `verifyInternal` on the calldata split is `optAccepts`. -/
theorem verifyInternal_opt (cd : ByteArray) :
    Fips204.verifyInternal (cd.extract 0 1312) (ByteArray.mk #[0, 0] ++ cd.extract 3732 cd.size)
      (cd.extract 1312 3732) = optAccepts cd := by
  have hb : Fips204.bitlen (Fips204.gamma1 - 1) = 17 := by decide
  unfold Fips204.verifyInternal
  split
  rename_i rho t1 hp
  split
  rename_i cT z hint? hs
  have hrho : rho = rhoOf cd := by
    have := congrArg Prod.fst hp
    simp only [Fips204.pkDecode] at this
    rw [← this, ByteArray.extract_extract]; rfl
  have ht1 : t1 = (Fips204.pkDecode (pkOf cd)).2 := by
    have := congrArg Prod.snd hp
    exact this.symm
  have hct : cT = ctOf cd := by
    have := congrArg Prod.fst hs
    simp only [Fips204.sigDecode] at this
    rw [← this, ByteArray.extract_extract]; rfl
  have hhint : hint? = hintOf cd := by
    have := congrArg (fun x => x.2.2) hs
    simp only [Fips204.sigDecode] at this
    rw [← this, ByteArray.extract_extract, hb]; rfl
  have hz : z = zPolys cd := by
    have := congrArg (fun x => x.2.1) hs
    exact this.symm
  subst hrho ht1 hct hhint hz
  split
  · rename_i h A c hH hA hC
    rw [Proofs.Math.expandA_eq] at hA
    by_cases hok : ((List.range 4).all fun r => (List.range 4).all fun s =>
        (Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) = true
    · rw [if_pos hok] at hA
      cases hA
      have hcs : c.size = 256 := Proofs.Math.sampleInBallOf_size _ _ hC
      have hokA : okA cd = true := hok
      have hokH : okH cd = true := by simp [okH, hH]
      have hokC : okC cd = true := by simp [okC, cOf, hC]
      have hcD : cD cd = c := by simp [cD, cOf, hC]
      have hhD : hintD cd = h := by simp [hintD, hH]
      have hw1 : ((Array.range Fips204.k).map fun i => (Array.range 256).map fun j =>
          Fips204.useHint h[i]![j]! ((Array.range Fips204.k).map fun i =>
            Fips204.nttInv ((Array.range 256).map fun j =>
              ((Fips204.matrixVectorNTT (aMat cd) ((zPolys cd).map Fips204.ntt))[i]![j]! -
                (Fips204.multiplyNTT (Fips204.ntt c) (((Fips204.pkDecode (pkOf cd)).2.map fun p =>
                  Fips204.ntt (p.map (· * 2 ^ Fips204.d))))[i]!)[j]!) % (Fips204.q : Int)))[i]![j]!) =
          w1Of cd := by
        unfold w1Of
        rw [hhD]
        apply Proofs.Math.map_range_congr
        intro i hi
        apply Proofs.Math.map_range_congr
        intro j hj
        rw [Proofs.Math.getElem!_map_range Fips204.k i _ hi]
        exact useHint_congr _ (wApprox_congr cd hcs hcD hi hj)
      unfold optAccepts finBytes
      rw [hokA, hokH, hokC]
      simp only [Bool.and_true]
      rw [show (aMat cd) = (Array.range 4).map fun r => (Array.range 4).map fun s =>
        (Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).getD
          Fips204.zeroPoly from rfl] at hw1
      rw [hw1]
      rfl
    · rw [if_neg hok] at hA
      cases hA
  · rename_i hnone
    unfold optAccepts
    cases hH : hintOf cd with
    | none => simp [okH, hH]
    | some h =>
      cases hC : Fips204.sampleInBall (ctOf cd) with
      | none => simp [okC, cOf, hC]
      | some c =>
        by_cases hok : okA cd = true
        · exact (hnone h _ c hH (by rw [Proofs.Math.expandA_eq]; exact if_pos hok) hC).elim
        · simp only [Bool.not_eq_true] at hok
          simp [hok]

/-- **Bridge**: for calldata of at least `|pk| + |σ|` bytes, the EIP-8355
verdict is the bytecode's flag-and-hash result. -/
theorem accepts_eq_optAccepts (cd : ByteArray) (hcd : 3732 ≤ cd.size) :
    accepts cd = optAccepts cd := by
  have h1 : Fips204.pkLen = 1312 := pkLen_eq
  have h2 : Fips204.sigLen = 2420 := sigLen_eq
  unfold accepts Fips204.verify
  rw [show MlDsa44.pkLen = Fips204.pkLen from rfl, show MlDsa44.sigLen = Fips204.sigLen from rfl,
    h1, h2]
  have s1 : (cd.extract 0 1312).size = 1312 := by simp; omega
  have s2 : (cd.extract 1312 (1312 + 2420)).size = 2420 := by simp; omega
  simp only [s1, s2, beq_self_eq_true, Bool.true_and, show 1312 + 2420 = 3732 from rfl,
    decide_eq_true hcd]
  exact verifyInternal_opt cd

/-- The final hash input is 64 + 768 bytes. -/
theorem finBytes_size (cd : ByteArray) : (finBytes cd).size = 832 := by
  unfold finBytes Fips204.w1Encode
  rw [ByteArray.size_append, muOf, Facts.H_size,
    show (Fips204.q - 1) / (2 * Fips204.gamma2) - 1 = 43 from rfl,
    show List.range Fips204.k = [0, 1, 2, 3] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, ByteArray.size_append,
    Proofs.Hint.simpleBitPack43_size]
  rfl

end MlDsaOpt44.Proofs.BridgeMain
