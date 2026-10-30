import MlDsa44.Proofs.Fn.Decode.HintBlocks
import MlDsa44.Proofs.Math.Decode.Hint
set_option warningAsError true
/-!
# The loops of `decodeHint`

`Inv m₀ M H`: the hint bytes in memory `M` are the polynomials `H` (four rows of
`0`/`1` coefficients) and `M` differs from `m₀` only inside `HB`. The inner,
outer and final loops are proved by induction on the iteration count, against
the model `outerStep` of `Math/Decode/Hint.lean`.
-/

namespace MlDsa44.Proofs.Decode

open EvmSemantics
open EvmSemantics.EVM

def Inv (m₀ M : ByteArray) (H : Array Fips204.Poly) : Prop :=
  WF H ∧ HintAt M H ∧ FrameExcept m₀ M [(HB, HB + 0x400)]

theorem byteAt_one : byteAt { data := #[UInt8.ofNat 1] } 0 = 1 := rfl

theorem inv_put {m₀ M : ByteArray} {H : Array Fips204.Poly} (h : Inv m₀ M H) {i v : Nat}
    (hi : i < 4) (hv : v < 256) :
    Inv m₀ (MachineState.writeBytes M { data := #[UInt8.ofNat 1] } (76256 + (i * 256 + v)))
      (setH H i v) := by
  obtain ⟨hwf, hat, hfr⟩ := h
  have hsz : ({ data := #[UInt8.ofNat 1] } : ByteArray).size = 1 := rfl
  refine ⟨WF_setH hwf hi, fun i' hi' j hj => ?_, ?_⟩
  · have hHB : HB = 76256 := rfl
    have hat' := hat i' hi' j hj
    rw [hHB] at hat'
    rw [hHB, Infra.byteAt_writeBytes, hsz, setH_get hwf hi hi' hj]
    split_ifs with h1 h2 h2
    · rw [show 76256 + 256 * i' + j - (76256 + (i * 256 + v)) = 0 by omega, byteAt_one]; rfl
    · exfalso; omega
    · exfalso; omega
    · exact hat'
  · refine Infra.FrameExcept.mono (Infra.FrameExcept.trans hfr (Infra.FrameExcept.writeBytes M _ _)) ?_
    intro r hr
    refine ⟨(HB, HB + 0x400), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsz] at hr
    rcases hr with rfl | rfl <;> simp only [HB] <;> omega

theorem beNat_zero {m : ByteArray} {a : Nat} :
    ∀ w, Infra.beNat m a w = 0 → ∀ k, k < w → byteAt m (a + k) = 0
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | w + 1, h, k, hk => by
    simp only [Infra.beNat] at h
    have h1 : Infra.beNat m a w = 0 := by omega
    have h2 : byteAt m (a + w) = 0 := by omega
    by_cases hkw : k = w
    · subst hkw; exact h2
    · exact beNat_zero w h1 k (by omega)

/-- Memory after zeroing `HB`. -/
def zeroHB (m : ByteArray) : ByteArray := Infra.storeWords m 76256 (fun _ => 0) 32

theorem inv_zero (m : ByteArray) : Inv m (zeroHB m) hs0.H := by
  refine ⟨WF_hs0, fun i hi j hj => ?_, Infra.FrameExcept.storeWords m 76256 (fun _ => 0) 32⟩
  have hw := Infra.word_storeWords (m := m) (base := 76256) (v := fun _ => 0)
    (i := 8 * i + j / 32) (by norm_num) 32 (by omega)
  rw [Infra.word_eq_beNat] at hw
  have hb := beNat_zero 32 hw (j % 32) (Nat.mod_lt _ (by norm_num))
  rw [show 76256 + 32 * (8 * i + j / 32) + j % 32 = HB + 256 * i + j by simp only [HB]; omega] at hb
  unfold zeroHB
  rw [hb]
  have h1 : hs0.H[i]! = Fips204.zeroPoly := by
    rw [getElem!_pos hs0.H i (by simp [hs0]; omega)]; simp [hs0]
  rw [h1, getElem!_pos Fips204.zeroPoly j (by simp [Fips204.zeroPoly]; omega)]
  simp [Fips204.zeroPoly]

/-- The cost bound of the whole run (indices `0 ≤ a₁ ≤ … ≤ a₄ ≤ 80`). -/
theorem hint_cost {a1 a2 a3 a4 : Nat} (h1 : 0 ≤ a1) (h2 : a1 ≤ a2) (h3 : a2 ≤ a3)
    (h4 : a3 ≤ a4) (h5 : a4 ≤ 80) :
    8 + 32 * 71 + 33 + (if a1 = 0 then 163 else 104 + 167 * (a1 - 0)) +
      (if a2 = a1 then 163 else 104 + 167 * (a2 - a1)) +
      (if a3 = a2 then 163 else 104 + 167 * (a3 - a2)) +
      (if a4 = a3 then 163 else 104 + 167 * (a4 - a3)) + 32 + (92 * (80 - a4) + 42) ≤ 16340 := by
  split_ifs <;> omega

section
variable {s : State} {ret : Nat} {tail : List UInt256}

/-- The hint bytes as the bytecode reads them. -/
@[irreducible] def yOf (s : State) : Nat → Nat := fun j => (s.executionEnv.calldata.extract 3648 3732)[j]!.toNat

theorem yOf_lt (s : State) (j : Nat) : yOf s j < 256 := by
  unfold yOf; exact Nat.lt_of_lt_of_le (UInt8.toNat_lt _) (by norm_num)

theorem byteAt_hint (hcd : 3732 ≤ s.executionEnv.calldata.size) {j : Nat} (hj : j < 84) :
    byteAt s.executionEnv.calldata (3648 + j) = yOf s j := by
  have hsz : (s.executionEnv.calldata.extract 3648 3732).size = 84 := by
    simp only [ByteArray.size_extract]; omega
  have h1 : (s.executionEnv.calldata.extract 3648 3732)[j]! =
      (s.executionEnv.calldata.extract 3648 3732)[j]'(by omega) :=
    getElem!_pos (s.executionEnv.calldata.extract 3648 3732) j (by omega)
  rw [ByteArray.getElem_extract] at h1
  unfold yOf
  rw [h1, byteAt, dif_pos (by omega)]

/-- The inner loop: `k` iterations from `idx = a`. -/
theorem hint_inner (hs : Ctx s) (htl : tail.length ≤ 960)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 77280 ≤ 32 * s.activeWords.toNat)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) {m₀ M : ByteArray} {H : Array Fips204.Poly}
    (hinv : Inv m₀ M H) {i a b : Nat} (g : Bool) (hi : i < 4) (hb : b ≤ 80) :
    ∀ k, a + k ≤ b → ∃ M', Inv m₀ M' (fillH (yOf s) i H (List.range' a k)) ∧
      Infra.Reach (callState s 3865 (wd a :: wd b :: wd i :: wd a :: flag g :: wd ret :: tail) M)
        (callState s 3865 (wd (a + k) :: wd b :: wd i :: wd a ::
          flag (g && (List.range' a k).all (okIdx (yOf s) a)) :: wd ret :: tail) M')
        (if k = 0 then 0 else 167 * k - 44)
  | 0, _ => ⟨M, by simpa [fillH] using hinv, (Infra.Reach.refl _).of_eq rfl (by simp)⟩
  | k + 1, hk => by
    obtain ⟨M', hinv', hreach⟩ := hint_inner hs htl haw hmem hcd hinv (a := a) (b := b) g hi hb k (by omega)
    have hY := byteAt_hint hcd (s := s) (j := a + k) (by omega)
    have hinv'' := inv_put hinv' hi (yOf_lt s (a + k))
    have hfill : fillH (yOf s) i H (List.range' a (k + 1)) =
        setH (fillH (yOf s) i H (List.range' a k)) i (yOf s (a + k)) := by
      simp [fillH, List.range'_concat, List.foldl_append]
    rw [hfill]
    refine ⟨_, hinv'', ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hblk := hint_innerFirst (ret := ret) (a := a) (b := b) hs htl M' (flag g) hi (by omega) hb hY (yOf_lt s _) haw hmem
      simp only [Nat.add_zero, List.range'_zero, List.all_nil, Bool.and_true] at hreach hblk
      refine ((hreach.trans hblk).mono (by simp)).of_eq rfl ?_
      simp [okIdx]
    · have hP := byteAt_hint hcd (s := s) (j := a + k - 1) (by omega)
      rw [show 3648 + (a + k - 1) = 3647 + (a + k) by omega] at hP
      have hcost : (if k = 0 then 0 else 167 * k - 44) = 167 * k - 44 := if_neg (by omega)
      rw [hcost] at hreach
      by_cases hPY : yOf s (a + k - 1) < yOf s (a + k)
      · have hblk := hint_innerOK (ret := ret) (a := a) (b := b) (idx := a + k) hs htl M'
          (flag (g && (List.range' a k).all (okIdx (yOf s) a))) hi (by omega) (by omega) hb hY
          (yOf_lt s _) hP hPY haw hmem
        refine ((hreach.trans hblk).mono (by simp; omega)).of_eq rfl ?_
        have : okIdx (yOf s) a (a + k) = true := by simp [okIdx, hPY]
        simp [List.range'_concat, List.all_append, this, Nat.add_assoc]
      · have hblk := hint_innerBad (ret := ret) (a := a) (b := b) (idx := a + k) hs htl M'
          (flag (g && (List.range' a k).all (okIdx (yOf s) a))) hi (by omega) (by omega) hb hY
          (yOf_lt s _) hP (yOf_lt s _) (by omega) haw hmem
        refine ((hreach.trans hblk).mono (by simp; omega)).of_eq rfl ?_
        have : okIdx (yOf s) a (a + k) = false := by simp [okIdx, hPY]; omega
        simp [List.range'_concat, List.all_append, this, Nat.add_assoc, flag]

/-- One outer iteration `i`, against `outerStep`. -/
theorem hint_outer (hs : Ctx s) (htl : tail.length ≤ 960)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 77280 ≤ 32 * s.activeWords.toNat)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) {m₀ M : ByteArray} (st : HS)
    (hinv : Inv m₀ M st.H) (ha : st.index ≤ 80) {i : Nat} (hi : i < 4) :
    ∃ M', Inv m₀ M' (outerStep (yOf s) st i).H ∧ st.index ≤ (outerStep (yOf s) st i).index ∧
      (outerStep (yOf s) st i).index ≤ 80 ∧
      Infra.Reach (callState s 3826 (wd i :: wd st.index :: flag st.good :: wd ret :: tail) M)
        (callState s 3826 (wd (i + 1) :: wd (outerStep (yOf s) st i).index ::
          flag (outerStep (yOf s) st i).good :: wd ret :: tail) M')
        (if (outerStep (yOf s) st i).index = st.index then 163
          else 104 + 167 * ((outerStep (yOf s) st i).index - st.index)) := by
  have hB := byteAt_hint hcd (s := s) (j := 80 + i) (by omega)
  rw [show 3648 + (80 + i) = 3728 + i by omega] at hB
  by_cases hbad : yOf s (80 + i) < st.index ∨ 80 < yOf s (80 + i)
  · have hstep : outerStep (yOf s) st i = ⟨st.index, false, st.H⟩ := by
      unfold outerStep; dsimp only; rw [if_pos hbad]
    rw [hstep]
    refine ⟨M, hinv, le_rfl, ha, ?_⟩
    have h1 := hint_outerBad (ret := ret) hs htl M (flag st.good) hi ha hB (yOf_lt s _) hbad
    have h2 := hint_innerExit (ret := ret) (i := i) (a := st.index) (b := st.index) hs htl M
      (wd 0) ha
    exact ((h1.trans h2).mono (by simp)).of_eq rfl (by simp [flag])
  · have hstep : outerStep (yOf s) st i = ⟨yOf s (80 + i),
        st.good && (List.range' st.index (yOf s (80 + i) - st.index)).all (okIdx (yOf s) st.index),
        fillH (yOf s) i st.H (List.range' st.index (yOf s (80 + i) - st.index))⟩ := by
      unfold outerStep; dsimp only; rw [if_neg hbad]
    rw [hstep]
    have hB80 : yOf s (80 + i) ≤ 80 := by omega
    obtain ⟨M', hinv', hreach⟩ := hint_inner (ret := ret) hs htl haw hmem hcd hinv
      (a := st.index) (b := yOf s (80 + i)) st.good hi hB80 (yOf s (80 + i) - st.index) (by omega)
    have h1 := hint_outerOK (ret := ret) (a := st.index) hs htl M (flag st.good) hi hB (by omega) hB80
    rw [show st.index + (yOf s (80 + i) - st.index) = yOf s (80 + i) by omega] at hreach
    have h2 := hint_innerExit (ret := ret) (i := i) (a := st.index) (b := yOf s (80 + i)) hs htl M'
      (flag (st.good && (List.range' st.index (yOf s (80 + i) - st.index)).all
        (okIdx (yOf s) st.index))) hB80
    refine ⟨M', ?_, ?_, ?_, ?_⟩
    · exact hinv'
    · show st.index ≤ yOf s (80 + i)
      omega
    · exact hB80
    refine ((h1.trans (hreach.trans h2)).mono ?_).of_eq rfl rfl
    show 84 + ((if yOf s (80 + i) - st.index = 0 then 0 else 167 * (yOf s (80 + i) - st.index) - 44) + 64) ≤
      (if yOf s (80 + i) = st.index then 163 else 104 + 167 * (yOf s (80 + i) - st.index))
    split_ifs <;> omega

/-- The final scan: `k` iterations from `idx = a`. -/
theorem hint_final (hs : Ctx s) (htl : tail.length ≤ 960)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (M : ByteArray) {a : Nat} (g : Bool) :
    ∀ k, a + k ≤ 80 →
      Infra.Reach (callState s 3953 (wd a :: wd a :: flag g :: wd ret :: tail) M)
        (callState s 3953 (wd (a + k) :: wd a ::
          flag (g && (List.range' a k).all (fun idx => yOf s idx == 0)) :: wd ret :: tail) M)
        (92 * k)
  | 0, _ => (Infra.Reach.refl _).of_eq rfl (by simp)
  | k + 1, hk => by
    have hreach := hint_final hs htl hcd M (a := a) g k (by omega)
    have hY := byteAt_hint hcd (s := s) (j := a + k) (by omega)
    by_cases hz : yOf s (a + k) = 0
    · rw [hz] at hY
      have hblk := hint_finZero (ret := ret) (a := a) (idx := a + k) hs htl M
        (flag (g && (List.range' a k).all (fun idx => yOf s idx == 0))) (by omega) hY
      refine ((hreach.trans hblk).mono (by omega)).of_eq rfl ?_
      simp [List.range'_concat, List.all_append, hz, Nat.add_assoc]
    · have hblk := hint_finNZ (ret := ret) (a := a) (idx := a + k) hs htl M
        (flag (g && (List.range' a k).all (fun idx => yOf s idx == 0))) (by omega) hY
        (yOf_lt s _) hz
      refine ((hreach.trans hblk).mono (by omega)).of_eq rfl ?_
      simp [List.range'_concat, List.all_append, hz, Nat.add_assoc, flag]

end

end MlDsa44.Proofs.Decode
