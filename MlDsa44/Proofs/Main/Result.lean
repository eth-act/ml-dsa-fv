import MlDsa44.Proofs.Main.Final
set_option warningAsError true
/-!
# The returned flag is `accepts`

Pure bridge from the flags and memory facts of the trace to
`MlDsa44.accepts`, through `verifyInternal_eq_flat`.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.Infra

theorem pkLen_eq : pkLen = 1312 := by
  simp only [pkLen, Fips204.pkLen, Fips204.bitlen, Fips204.k, Fips204.q, Fips204.d]; decide

theorem sigLen_eq : sigLen = 2420 := by
  simp only [sigLen, Fips204.sigLen, Fips204.bitlen, Fips204.k, Fips204.l, Fips204.lambda,
    Fips204.gamma1, Fips204.omega]; decide

theorem accepts_eq_flat {cd : ByteArray} (hcd : 3732 ≤ cd.size) :
    accepts cd = flatAccepts (pkOf cd) (ByteArray.mk #[0, 0] ++ msgOf cd) (sigOf cd) := by
  unfold accepts
  rw [pkLen_eq, sigLen_eq, decide_eq_true (by omega), Bool.true_and, Fips204.verify]
  have h1 : ((cd.extract 0 1312).size == Fips204.pkLen) = true := by
    rw [beq_iff_eq]; show _ = pkLen; rw [pkLen_eq]; simp [ByteArray.size_extract]; omega
  have h2 : ((cd.extract 1312 (1312 + 2420)).size == Fips204.sigLen) = true := by
    rw [beq_iff_eq]; show _ = sigLen; rw [sigLen_eq]; simp [ByteArray.size_extract]; omega
  rw [h1, h2, Bool.true_and, Bool.true_and]
  exact verifyInternal_eq_flat _ _ _ (by simp [ByteArray.size_extract]; omega)
    (by simp [ByteArray.size_extract]; omega)

theorem bytesAt_extract_self (cd : ByteArray) (a n : Nat) (h : a + n ≤ cd.size) :
    BytesAt cd a (cd.extract a (a + n)) := by
  intro i hi
  have hi2 := hi
  rw [ByteArray.size_extract] at hi2
  rw [byteAt_eq_toNat_getElem!, getElem!_pos cd (a + i) (by omega),
    getElem!_pos (cd.extract a (a + n)) i hi, ByteArray.getElem_extract]

/-- Concatenated rows stored one after another. -/
theorem bytesAt_rows {M : ByteArray} {p : Nat} {W : Array Fips204.Poly} :
    ∀ n, (∀ j, j < n → BytesAt M (p + 192 * j) (Fips204.simpleBitPack W[j]! b1)) →
      BytesAt M p ((List.range n).foldl (fun out i => out ++ Fips204.simpleBitPack W[i]! b1) .empty) ∧
      ((List.range n).foldl (fun out i => out ++ Fips204.simpleBitPack W[i]! b1) .empty).size = 192 * n
  | 0, _ => ⟨fun i hi => absurd hi (by simp), by simp⟩
  | n + 1, h => by
    obtain ⟨ih, hs⟩ := bytesAt_rows n (fun j hj => h j (by omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨bytesAt_append.mpr ⟨ih, ?_⟩, ?_⟩
    · rw [hs]; exact h n (by omega)
    · rw [ByteArray.size_append, hs, simpleBitPack_size]; ring

theorem hash_eq {cd M Mx : ByteArray} (hcd : 3732 ≤ cd.size)
    (hx : BytesAt Mx XOF (Fips204.H (MachineState.readPadded M W1 832) 32))
    (hmu : BytesAt M W1 (muOf cd)) (W : Array Fips204.Poly)
    (hrows : ∀ j, j < 4 → BytesAt M (W1 + 64 + 192 * j) (Fips204.simpleBitPack W[j]! b1)) :
    decide (word Mx XOF = word cd 1312) =
      (cTildeOf cd == Fips204.H (muOf cd ++ Fips204.w1Encode W) (Fips204.lambda / 4)) := by
  obtain ⟨hb, hs⟩ := bytesAt_rows (M := M) (p := W1 + 64) (W := W) 4 hrows
  have hall : BytesAt M W1 (muOf cd ++ Fips204.w1Encode W) := by
    rw [bytesAt_append, muOf_size]
    exact ⟨hmu, hb⟩
  have hr := readPadded_of_bytesAt hall
  rw [ByteArray.size_append, muOf_size, show Fips204.w1Encode W =
    (List.range 4).foldl (fun out i => out ++ Fips204.simpleBitPack W[i]! b1) .empty from rfl, hs] at hr
  rw [hr] at hx
  have hiff := word_eq_word_iff_of_bytesAt hx (bytesAt_extract_self cd 1312 32 (by omega))
    (H_size _ _) (by simp [ByteArray.size_extract]; omega)
  rw [show Fips204.lambda / 4 = 32 from rfl]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, byteArray_beq_iff, hiff, eq_comm]
  rfl

theorem okA_eq (cd : ByteArray) :
    ((List.range 4).all fun i => (List.range 4).all fun j =>
      (aEntry ((pkOf cd).extract 0 32) i j).isSome) =
      (((fAOf cd 0 && fAOf cd 1) && fAOf cd 2) && fAOf cd 3) := by
  simp [fAOf, List.range_succ, Bool.and_assoc]

theorem result_bool {cd M Mx : ByteArray} {cH : Fips204.Poly} (hcd : 3732 ≤ cd.size)
    (hI : Inv cd M cH)
    (hc : ∀ c, Fips204.sampleInBallOf (Fips204.H (cTildeOf cd) Fips204.sampleInBallLimit) = some c →
      cH = Fips204.ntt (c.map (· % (Fips204.q : Int))))
    (hD : RowsDone cd M cH 4)
    (hx : BytesAt Mx XOF (Fips204.H (MachineState.readPadded M W1 832) 32)) :
    (fAllOf cd ((fzOf cd && fhOf cd) && fcOf cd) && decide (word Mx XOF = word cd 1312)) =
      accepts cd := by
  rw [accepts_eq_flat hcd]
  have hhint : (sigOf cd).extract 2336 2420 = hintBytesOf cd := by
    simp [sigOf, hintBytesOf, ByteArray.extract_extract]
  have hct : (sigOf cd).extract 0 32 = cTildeOf cd := by
    simp [sigOf, cTildeOf, ByteArray.extract_extract]
  simp only [flatAccepts, hhint, hct, Fips204.sampleInBall, okA_eq]
  change (fAllOf cd ((fzOf cd && fhOf cd) && fcOf cd) && decide (word Mx XOF = word cd 1312)) =
    ((fzOf cd && fhOf cd && fcOf cd && _) && _)
  unfold fAllOf
  cases hfh : fhOf cd
  · simp
  cases hfc : fcOf cd
  · simp
  cases hA0 : fAOf cd 0
  · simp
  cases hA1 : fAOf cd 1
  · simp
  cases hA2 : fAOf cd 2
  · simp
  cases hA3 : fAOf cd 3
  · simp
  simp only [Bool.and_true]
  cases fzOf cd
  · simp only [Bool.false_and]
  simp only [Bool.true_and]
  obtain ⟨h, hH⟩ := Option.isSome_iff_exists.mp hfh
  obtain ⟨c, hC⟩ := Option.isSome_iff_exists.mp hfc
  rw [hH, hC, Option.getD_some, Option.getD_some]
  have hcH := hc c hC
  refine hash_eq hcd hx hI.mu _ (fun j hj => ?_)
  rw [Math.getElem!_map_range 4 j _ hj, Math.getElem!_map_range 4 j _ hj]
  obtain ⟨f, hf, hrow⟩ := hD j hj
  have hAj : fAOf cd j = true := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · exact hA0
    · exact hA1
    · exact hA2
    · exact hA3
  have := hrow h hH
  rw [hf hAj, hcH] at this
  exact this

end MlDsa44.Proofs.Main
