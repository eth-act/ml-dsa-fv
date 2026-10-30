import MlDsa44.Proofs.Main.Sig
set_option warningAsError true
/-!
# The row loop

`for i < 4 { ok &= computeRow(i); encodeRow(i) }`: row `i` of
`w'Approx` is accumulated in `ACC`, then `w1Encode` row `i` is written at
`W1 + 64 + 192 i`.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.Infra

/-- The `w1Encode` coefficient bound `(q − 1)/(2γ₂) − 1`. -/
abbrev b1 : Nat := (Fips204.q - 1) / (2 * Fips204.gamma2) - 1

/-- Row `i` of `Â` succeeds (`RejNTTPoly` within the Appendix C limit). -/
def fAOf (cd : ByteArray) (i : Nat) : Bool :=
  (List.range 4).all fun j => (aEntry ((pkOf cd).extract 0 32) i j).isSome

/-- Row `i` of `Â`, defaulted. -/
def aRowOf (cd : ByteArray) (i : Nat) : Array Fips204.Poly :=
  (Array.range 4).map fun j => (aEntry ((pkOf cd).extract 0 32) i j).getD Fips204.zeroPoly

/-- `ẑ` as an array. -/
def zHatArr (cd : ByteArray) : Array Fips204.Poly := (Array.range 4).map (zHatOf cd)

/-- Row `j` of `UseHint(h, ·)` applied to `f`. -/
def w1RowH (h : Array Fips204.Poly) (j : Nat) (f : Fips204.Poly) : Fips204.Poly :=
  (Array.range 256).map fun t => Fips204.useHint h[j]![t]! f[t]!

/-- Row `j` of the `w1Encode` input is stored, for the decoded hint. -/
def RowOK (cd M : ByteArray) (j : Nat) (f : Fips204.Poly) : Prop :=
  ∀ h, Fips204.hintBitUnpack (hintBytesOf cd) = some h →
    BytesAt M (W1 + 64 + 192 * j) (Fips204.simpleBitPack (w1RowH h j f) b1)

/-- The first `n` rows are done; each holds the row computed from `ACC`,
which is `w'Approx` row `j` whenever row `j` of `Â` succeeded. -/
def RowsDone (cd M : ByteArray) (cH : Fips204.Poly) (n : Nat) : Prop :=
  ∀ j, j < n → ∃ f, (fAOf cd j = true →
      f = rowApprox (aRowOf cd j) (zHatArr cd) cH (t1Hat (pkOf cd) j)) ∧ RowOK cd M j f

theorem simpleBitPack_size (w : Fips204.Poly) : (Fips204.simpleBitPack w b1).size = 192 := by
  simp only [Fips204.simpleBitPack]
  simp [ByteArray.size, Fips204.bitlen]
  decide

theorem w1Row_eq {m : ByteArray} {h : Array Fips204.Poly} (hH : HintAt m h) {i : Nat} (hi : i < 4)
    (f : Fips204.Poly) : w1Row m i f = w1RowH h i f := by
  unfold w1Row w1RowH
  apply Array.ext (by simp)
  intro t h1 _
  simp only [Array.size_map, Array.size_range] at h1
  simp only [Array.getElem_map, Array.getElem_range]
  rw [hH i hi t h1]

theorem RowOK.frame {cd M M' : ByteArray} {j : Nat} {f : Fips204.Poly} {rs : List (Nat × Nat)}
    (h : RowOK cd M j f) (hf : FrameExcept M M' rs) (ha : Avoids rs (W1 + 64 + 192 * j) (W1 + 64 + 192 * j + 192)) :
    RowOK cd M' j f := fun hv hhv =>
  BytesAt.frame (h hv hhv) hf (by rw [simpleBitPack_size]; exact ha)

/-- Cost of one loop iteration. -/
def rowCost : Nat := 45 + Gas.computeRow + 29 + Gas.encodeRow + 26

section blocks
variable {s : State} (hs : Ctx s)
include hs

theorem row_block1 (mlen : Nat) (i : Nat) (hi : i < 4) (a : Bool) (M : ByteArray) :
    Reach (callState s 5200 [wd i, flag a, wd mlen] M)
      (callState s 4415 [wd i, wd 0, wd 5219, wd i, flag a, wd mlen] M) 45 := by
  evm_reach [3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331] with [flag]

theorem row_block2 (mlen : Nat) (i : Nat) (a b : Bool) (M : ByteArray) :
    Reach (callState s 5219 [flag b, wd i, flag a, wd mlen] M)
      (callState s 4260 [wd i, wd 5232, wd i, flag (a && b), wd mlen] M) 29 := by
  evm_reach [3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340] with [flag, ite_land]

theorem row_block3 (mlen : Nat) (i : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5232 [wd i, flag a, wd mlen] M)
      (callState s 5200 [wd (i + 1), flag a, wd mlen] M) 26 := by
  evm_reach [3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348] with [flag]

end blocks

theorem row_step {s : State} (hs : Ctx s) {mlen : Nat}
    (hmlen : mlen + 3732 = s.executionEnv.calldata.size) {i : Nat} (hi : i < 4) (ok : Bool)
    {M : ByteArray} {cH : Fips204.Poly} (hI : Inv s.executionEnv.calldata M cH)
    (hD : RowsDone s.executionEnv.calldata M cH i) :
    ∃ M', Inv s.executionEnv.calldata M' cH ∧ RowsDone s.executionEnv.calldata M' cH (i + 1) ∧
      Reach (callState s 5200 [wd i, flag ok, wd mlen] M)
        (callState s 5200 [wd (i + 1), flag (ok && fAOf s.executionEnv.calldata i), wd mlen] M')
        rowCost := by
  have hcd : 3732 ≤ s.executionEnv.calldata.size := by omega
  have hzs : (zHatArr s.executionEnv.calldata).size = 4 := by simp [zHatArr]
  obtain ⟨M1, ⟨f, hf, hfred⟩, hrow, hf1, hC1⟩ := computeRow_call hs
    (retOK_top (ret := 5219) (tail := [wd i, flag ok, wd mlen]) (by simp only [isValidJumpDest_lit])
      (by norm_num) (by simp [Stack.computeRow, Stack.shake, Stack.keccakF, Stack.xorBlock,
        Stack.loadLE64, Stack.storeLE64, Stack.bswap64, Stack.rejSample, Stack.zeroPoly, Stack.unpack,
        Stack.ntt, Stack.nttInv, Stack.leaf]))
    hi hcd hI.rc hI.zeta hzs
    (fun j hj => by
      rw [zHatArr, Math.getElem!_map_range 4 j _ hj]
      exact hI.zh j hj)
    hI.ch hI.chRed hI.seed
  have hR1 : Reach (callState s 4415 [wd i, wd 0, wd 5219, wd i, flag ok, wd mlen] M)
      (callState s 5219 [flag (fAOf s.executionEnv.calldata i), wd i, flag ok, wd mlen] M1)
      Gas.computeRow :=
    (Infra.call_iff.mp hC1).of_eq (by simp [Entry.computeRow]) (by simp [fAOf])
  have hI1 : Inv s.executionEnv.calldata M1 cH :=
    hI.frame hf1 hcd (by avoid) (by avoid) (by avoid) (by avoid) (by avoid) (by avoid) (by avoid)
  obtain ⟨M2, hbytes, hf2, hC2⟩ := encodeRow_call hs
    (retOK_top (ret := 5232) (tail := [wd i, flag (ok && fAOf s.executionEnv.calldata i), wd mlen])
      (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.encodeRow, Stack.useHint, Stack.leaf]))
    hi hf hfred (hI1.bits i hi)
  have hR2 : Reach (callState s 4260 [wd i, wd 5232, wd i, flag (ok && fAOf s.executionEnv.calldata i),
        wd mlen] M1)
      (callState s 5232 [wd i, flag (ok && fAOf s.executionEnv.calldata i), wd mlen] M2)
      Gas.encodeRow :=
    (Infra.call_iff.mp hC2).of_eq (by simp [Entry.encodeRow]) (by simp)
  refine ⟨M2, hI1.frame hf2 hcd (by avoid) (by avoid) (by avoid) (by avoid) (by avoid) (by avoid)
    (by avoid), fun j hj => ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji
      refine ⟨f, fun hA => ?_, fun hv hhv => ?_⟩
      · have hA' := hA
        simp only [fAOf, List.all_eq_true, List.mem_range, Option.isSome_iff_exists] at hA'
        refine PolyAt.unique hf ((hrow (aRowOf s.executionEnv.calldata j) (by simp [aRowOf])
          (fun t ht => ?_)).1)
        obtain ⟨a, ha⟩ := hA' t ht
        rw [aRowOf, Math.getElem!_map_range 4 t _ ht, ha]
        rfl
      · rw [← w1Row_eq (hI1.hint hv hhv) hi]
        exact hbytes
    · obtain ⟨g, hg, hok⟩ := hD j (by omega)
      refine ⟨g, hg, ?_⟩
      have hjlt : j < i := by omega
      exact (hok.frame hf1 (by avoid)).frame hf2 (by avoid)
  · have h := (row_block1 hs mlen i hi ok M).trans hR1
    have h := h.trans (row_block2 hs mlen i _ _ M1)
    have h := h.trans hR2
    have h := h.trans (row_block3 hs mlen i _ M2)
    exact h.mono (le_of_eq (by unfold rowCost; omega))

end MlDsa44.Proofs.Main
