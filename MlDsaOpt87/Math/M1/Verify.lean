import MlDsaOpt87.Layout
import MlDsaOpt65.Math.M1.Row
import MlDsaOpt65.Math.M1.Ball
/-!
# The verification bridge for ML-DSA-87 (work package M1)

`MlDsaOpt44/Math/{BridgeMain,SpecFacts}.lean` at `P = Params.mldsa87`
(`k = 8`, `ℓ = 7`, 20-bit z fields, 64-byte `c̃`): the z decoding
(`zPolys_coeff`, `ntt_zLane`), the per-row identity `wApprox_congr` between
FIPS 204's `w′Approx` and `wRow`, and `accepts_eq_optAccepts`.
-/

namespace MlDsaOpt87.Proofs.M1

open MlDsa MlDsaOpt87.Proofs MlDsaOpt44.Proofs.NttConv

theorem poly_ext (a b : Fips204.Poly) (ha : a.size = 256) (hb : b.size = 256)
    (h : ∀ t, t < 256 → a[t]! = b[t]!) : a = b := by
  apply Array.ext (by omega)
  intro t h1 h2
  have := h t (by omega)
  rwa [getElem!_pos a t h1, getElem!_pos b t h2] at this

theorem bitlen_z : Fips204.bitlen (P.gamma1 - 1) = 19 := by decide +kernel

theorem bitlen_zc : Fips204.bitlen (P.gamma1 - 1 + P.gamma1) = 20 := by decide +kernel

/-! ## z -/

theorem zPolys_size (cd : ByteArray) : (zPolys cd).size = 7 :=
  MlDsaOptM1.sigDecode_z_size P _

theorem zPolys_get (cd : ByteArray) {s : Nat} (hs : s < 7) :
    (zPolys cd)[s]! = Fips204.bitUnpack (cd.extract (Z0 + 640 * s) (Z0 + 640 * (s + 1)))
      (P.gamma1 - 1) P.gamma1 := by
  unfold zPolys sigOf
  rw [MlDsaOptM1.sigDecode_z_get P _ hs, bitlen_z, ByteArray.extract_extract,
    show P.lambda / 4 = 64 from rfl, Nat.min_eq_left (by unfold CTOFF HDR; omega)]
  unfold CTOFF Z0
  rw [show 2592 + (64 + 32 * (1 + 19) * s) = 2656 + 640 * s by omega,
    show 2592 + (64 + 32 * (1 + 19) * (s + 1)) = 2656 + 640 * (s + 1) by omega]

theorem zPolys_get_size (cd : ByteArray) {s : Nat} (hs : s < 7) : (zPolys cd)[s]!.size = 256 := by
  rw [zPolys_get cd hs, MlDsaOptM1.bitUnpack_size]

/-- Coefficient `t` of `z_s` is `γ1 − rawZ`. -/
theorem zPolys_coeff (cd : ByteArray) {s t : Nat} (hs : s < 7) (ht : t < 256) :
    (zPolys cd)[s]![t]! = (2 ^ 19 : Int) - rawZ cd s t := by
  rw [zPolys_get cd hs, MlDsaOptM1.bitUnpack_get _ _ _ ht, bitlen_zc, Nat.mul_comm t 20]
  rfl

theorem rawZ_lt (cd : ByteArray) (s t : Nat) : rawZ cd s t < 2 ^ 20 :=
  MlDsaOptM1.bitsToInteger_lt _ _ 20

/-- The `dz` lanes of a 20-bit `z_k` polynomial are `ẑ_k` after the NTT. -/
theorem ntt_zLane (cd : ByteArray) {k : Nat} (hk : k < 7) :
    Fips204.ntt ((Array.range 256).map fun t => (zLane cd k t : Int)) = zHat cd k := by
  have hA : ((Array.range 256).map fun t => (zLane cd k t : Int)).size = 256 := by
    rw [Array.size_map, Array.size_range]
  have hZ := zPolys_get_size cd hk
  have hA' : (((Array.range 256).map fun t => (zLane cd k t : Int)).map
      (· % (Fips204.q : Int))).size = 256 := by rw [Array.size_map, hA]
  have hZ' : ((zPolys cd)[k]!.map (· % (Fips204.q : Int))).size = 256 := by
    rw [Array.size_map, hZ]
  refine (MlDsaOptM1.ntt_map_emod' _ hA).symm.trans
    (congrArg Fips204.ntt (poly_ext _ _ hA' hZ' ?_))
  intro t ht
  rw [MlDsa44.Proofs.Math.getElem!_map ((Array.range 256).map fun t => (zLane cd k t : Int))
      (· % (Fips204.q : Int)) t (by rw [hA]; exact ht),
    MlDsa44.Proofs.Math.getElem!_map (zPolys cd)[k]! (· % (Fips204.q : Int)) t
      (by rw [hZ]; exact ht),
    MlDsa44.Proofs.Math.getElem!_map_range 256 t _ ht, zPolys_coeff cd hk ht]
  have hlt : rawZ cd k t < 1048576 := rawZ_lt cd k t
  unfold zLane
  generalize rawZ cd k t = r at hlt ⊢
  have e : ((2 ^ 19 + Fips204.q - r : Nat) : Int) = ((2 ^ 19 : Int) - r) + (Fips204.q : Int) := by
    rw [Nat.cast_sub (by unfold Fips204.q; omega)]
    push_cast
    ring
  rw [e, Int.add_emod_right]

/-! ## One row of `w′` -/

/-- The `A` matrix `ExpandA` returns when every entry succeeds. -/
def aMat (cd : ByteArray) : Array (Array Fips204.Poly) :=
  (Array.range 8).map fun r => (Array.range 7).map fun s =>
    (Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).getD
      Fips204.zeroPoly

theorem t1_size (cd : ByteArray) {r : Nat} (hr : r < 8) : (t1Of cd r).size = 256 := by
  unfold t1Of pkOf Fips204.pkDecode
  rw [show P.k = 8 from rfl, MlDsa44.Proofs.Math.getElem!_map_range 8 r _ hr]
  simp [Fips204.simpleBitUnpack]

theorem toF_azRow (cd : ByteArray) (r : Nat) {j : Nat} (hj : j < 256) :
    toF (azRow cd r) j = ∑ s ∈ Finset.range 7, toF (aD cd r s) j * toF (zHat cd s) j := by
  unfold azRow
  rw [MlDsaOpt44.Proofs.RowMath.toF_map_range _ hj, MlDsaOptM1.cast_emod',
    MlDsaOpt44.Proofs.RowMath.list_sum_cast]
  simp only [Int.cast_mul]
  rfl

/-- **Row identity**: the spec's `w′Approx` row and `wRow` agree modulo `q`. -/
theorem wApprox_congr (cd : ByteArray) {c : Fips204.Poly} (hcs : c.size = 256) (hc : cD cd = c)
    {i : Nat} (hi : i < 8) {j : Nat} (hj : j < 256) :
    toF (Fips204.nttInv ((Array.range 256).map fun j =>
        ((Fips204.matrixVectorNTT P (aMat cd) ((zPolys cd).map Fips204.ntt))[i]![j]! -
          (Fips204.multiplyNTT (Fips204.ntt c) (((Fips204.pkDecode P (pkOf cd)).2.map fun p =>
            Fips204.ntt (p.map (· * 2 ^ Fips204.d))))[i]!)[j]!) % (Fips204.q : Int))) j =
      toF (wRow cd i) j := by
  have ht1s : (Fips204.pkDecode P (pkOf cd)).2.size = 8 := by
    simp [Fips204.pkDecode, show P.k = 8 from rfl]
  have hT : ((t1Of cd i).map (· * 2 ^ Fips204.d)).size = 256 := by simp [t1_size cd hi]
  refine (MlDsaOptM1.nttInv_row' _ (azRow cd i) c ((t1Of cd i).map (· * 2 ^ Fips204.d)) ?_ ?_
    hcs hT ?_ hj).trans ?_
  · simp
  · simp [azRow]
  rotate_left
  · unfold wRow
    rw [MlDsaOpt44.Proofs.RowMath.toF_map_range _ hj, MlDsaOptM1.cast_emod', Int.cast_sub,
      Int.cast_mul,
      MlDsaOpt44.Proofs.RowMath.negacyclic_cast, ← hc]
    have : negF (toF (cD cd)) (toF ((t1Of cd i).map (· * 2 ^ Fips204.d))) j =
        negF (toF (cD cd)) (fun k => (2 ^ 13 : F) * toF (t1Of cd i) k) j := by
      apply MlDsaOpt44.Proofs.RowMath.negF_congr _ _ hj
      intro k hk
      rw [MlDsaOpt44.Proofs.RowMath.toF_map _ _ (by rw [t1_size cd hi]; exact hk), Int.cast_mul,
        mul_comm]
      rfl
    rw [this, MlDsaOpt44.Proofs.RowMath.negF_smul]
    push_cast
    rfl
  · intro j hj
    rw [MlDsaOpt44.Proofs.RowMath.toF_map_range _ hj, MlDsaOptM1.cast_emod', Int.cast_sub]
    have hz : ∀ s, s < 7 → ((zPolys cd).map Fips204.ntt)[s]! = zHat cd s := by
      intro s hs
      rw [MlDsa44.Proofs.Math.getElem!_map _ _ _ (by rw [zPolys_size]; exact hs), zHat,
        MlDsaOptM1.ntt_map_emod' _ (zPolys_get_size cd hs)]
    have hA : ∀ s, s < 7 → (aMat cd)[i]![s]! = aD cd i s := by
      intro s hs
      rw [aMat, MlDsa44.Proofs.Math.getElem!_map_range 8 i _ hi,
        MlDsa44.Proofs.Math.getElem!_map_range 7 s _ hs]
      rfl
    have e1 : (Fips204.matrixVectorNTT P (aMat cd) ((zPolys cd).map Fips204.ntt))[i]! =
        (List.range P.l).foldl (fun acc s => Fips204.addNTT acc
          (Fips204.multiplyNTT (aMat cd)[i]![s]! ((zPolys cd).map Fips204.ntt)[s]!))
          Fips204.zeroPoly := by
      unfold Fips204.matrixVectorNTT
      exact MlDsa44.Proofs.Math.getElem!_map_range 8 i _ hi
    have e2 : ((Fips204.pkDecode P (pkOf cd)).2.map fun p =>
        Fips204.ntt (p.map (· * 2 ^ Fips204.d)))[i]! =
        Fips204.ntt ((t1Of cd i).map (· * 2 ^ Fips204.d)) :=
      MlDsa44.Proofs.Math.getElem!_map _ _ _ (by rw [ht1s]; exact hi)
    have e3 : ((Fips204.matrixVectorNTT P (aMat cd) ((zPolys cd).map Fips204.ntt))[i]![j]! : F) =
        toF ((Fips204.matrixVectorNTT P (aMat cd) ((zPolys cd).map Fips204.ntt))[i]!) j := rfl
    have e4 : (((Fips204.multiplyNTT (Fips204.ntt c) ((Fips204.pkDecode P (pkOf cd)).2.map
        fun p => Fips204.ntt (p.map (· * 2 ^ Fips204.d)))[i]!)[j]! : Int) : F) =
        toF (Fips204.multiplyNTT (Fips204.ntt c) ((Fips204.pkDecode P (pkOf cd)).2.map fun p =>
          Fips204.ntt (p.map (· * 2 ^ Fips204.d)))[i]!) j := rfl
    rw [e3, e4, MlDsaOptM1.toF_mulNTT' _ _ hj, e2, e1, MlDsaOptM1.toF_azFold _ _ hj,
      toF_azRow cd i hj, show P.l = 7 from rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hA s hs, hz s hs]

/-! ## The verdict -/

/-- `verifyInternal` on the calldata split is `optAccepts`. -/
theorem verifyInternal_opt (cd : ByteArray) :
    Fips204.verifyInternal P (cd.extract 0 2592) (ByteArray.mk #[0, 0] ++ cd.extract 7219 cd.size)
      (cd.extract 2592 7219) = optAccepts cd := by
  have hp : Fips204.pkDecode P (cd.extract 0 2592) =
      (rhoOf cd, (Fips204.pkDecode P (pkOf cd)).2) := by
    have e1 : (Fips204.pkDecode P (cd.extract 0 2592)).1 = rhoOf cd := by
      simp only [Fips204.pkDecode]; rw [ByteArray.extract_extract]; rfl
    have e2 : (Fips204.pkDecode P (cd.extract 0 2592)).2 = (Fips204.pkDecode P (pkOf cd)).2 := by
      unfold pkOf CTOFF; rfl
    exact Prod.ext e1 e2
  have hs : Fips204.sigDecode P (cd.extract 2592 7219) = (ctOf cd, zPolys cd, hintOf cd) := by
    have e1 : (Fips204.sigDecode P (cd.extract 2592 7219)).1 = ctOf cd := by
      simp only [Fips204.sigDecode]; rw [ByteArray.extract_extract]; rfl
    have e2 : (Fips204.sigDecode P (cd.extract 2592 7219)).2.1 = zPolys cd := by
      unfold zPolys sigOf CTOFF HDR; rfl
    have e3 : (Fips204.sigDecode P (cd.extract 2592 7219)).2.2 = hintOf cd := by
      simp only [Fips204.sigDecode]; rw [ByteArray.extract_extract, bitlen_z]; rfl
    exact Prod.ext e1 (Prod.ext e2 e3)
  rw [MlDsaOptM1.verifyInternal_flat P _ _ _ _ _ _ _ _ hp hs]
  generalize hH : hintOf cd = hg
  generalize hAg : Fips204.expandA P (rhoOf cd) = Ag
  generalize hC : Fips204.sampleInBall P (ctOf cd) = Cg
  rw [MlDsaOptM1.expandA_eq] at hAg
  have hokA_iff : okA cd = true ↔ ∃ A, Ag = some A := by
    rw [← hAg]
    constructor
    · intro h; exact ⟨_, if_pos h⟩
    · rintro ⟨A, hA⟩
      split at hA
      · rename_i hc; exact hc
      · cases hA
  rcases hg with _ | h <;> rcases Ag with _ | A <;> rcases Cg with _ | c <;> dsimp only
  · simp [optAccepts, okH, hH]
  · simp [optAccepts, okH, hH]
  · simp [optAccepts, okH, hH]
  · simp [optAccepts, okH, hH]
  · have hok : okA cd = false := by
      cases h' : okA cd
      · rfl
      · obtain ⟨_, h''⟩ := hokA_iff.1 h'; cases h''
    simp [optAccepts, hok]
  · have hok : okA cd = false := by
      cases h' : okA cd
      · rfl
      · obtain ⟨_, h''⟩ := hokA_iff.1 h'; cases h''
    simp [optAccepts, hok]
  · simp [optAccepts, okC, cOf, hC]
  · by_cases hok : ((List.range P.k).all fun r => (List.range P.l).all fun s =>
        (Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) = true
    · rw [if_pos hok] at hAg
      cases hAg
      have hcs : c.size = 256 := (MlDsaOptM1.sampleInBallOf_inv P (by decide) hC).1
      have hokA : okA cd = true := hok
      have hokH : okH cd = true := by simp [okH, hH]
      have hokC : okC cd = true := by simp [okC, cOf, hC]
      have hcD : cD cd = c := by simp [cD, cOf, hC]
      have hhD : hintD cd = h := by simp [hintD, hH]
      have hw1 : ((Array.range P.k).map fun i => (Array.range 256).map fun j =>
          Fips204.useHint P h[i]![j]! ((Array.range P.k).map fun i =>
            Fips204.nttInv ((Array.range 256).map fun j =>
              ((Fips204.matrixVectorNTT P (aMat cd) ((zPolys cd).map Fips204.ntt))[i]![j]! -
                (Fips204.multiplyNTT (Fips204.ntt c) (((Fips204.pkDecode P (pkOf cd)).2.map
                  fun p => Fips204.ntt (p.map (· * 2 ^ Fips204.d))))[i]!)[j]!) %
                    (Fips204.q : Int)))[i]![j]!) =
          w1Of cd := by
        unfold w1Of
        rw [hhD]
        apply MlDsa44.Proofs.Math.map_range_congr
        intro i hi
        apply MlDsa44.Proofs.Math.map_range_congr
        intro j hj
        rw [MlDsa44.Proofs.Math.getElem!_map_range P.k i _ hi]
        exact MlDsaOptM1.useHint_congr P _ (wApprox_congr cd hcs hcD hi hj)
      unfold optAccepts finBytes
      rw [hokA, hokH, hokC]
      simp only [Bool.and_true]
      rw [show (aMat cd) = (Array.range P.k).map fun r => (Array.range P.l).map fun s =>
        (Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).getD
          Fips204.zeroPoly from rfl] at hw1
      rw [hw1]
      rfl
    · rw [if_neg hok] at hAg
      cases hAg

/-- **Bridge**: for calldata of at least `|pk| + |σ|` bytes, the EIP-8355
verdict is the bytecode's flag-and-hash result. -/
theorem accepts_eq_optAccepts (cd : ByteArray) (hcd : 7219 ≤ cd.size) :
    MlDsa87.accepts cd = optAccepts cd := by
  have h1 : Fips204.pkLen P = 2592 := by decide
  have h2 : Fips204.sigLen P = 4627 := by decide
  unfold MlDsa87.accepts Interface.accepts Fips204.verify
  rw [show MlDsa87.params = P from rfl, h1, h2]
  have s1 : (cd.extract 0 2592).size = 2592 := by simp; omega
  have s2 : (cd.extract 2592 (2592 + 4627)).size = 4627 := by simp; omega
  simp only [s1, s2, beq_self_eq_true, Bool.true_and, show 2592 + 4627 = 7219 from rfl,
    decide_eq_true hcd]
  exact verifyInternal_opt cd

end MlDsaOpt87.Proofs.M1
