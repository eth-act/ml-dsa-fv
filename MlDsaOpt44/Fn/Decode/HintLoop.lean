import MlDsaOpt44.Fn.Decode.HintBlocks
import MlDsaOpt44.Fn.Decode.ZMath
import MlDsaOpt44.Budget
import MlDsa44.Proofs.Math.Decode.Hint
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The loops of `dhint` (WP8)

The bytecode runs FIPS 204 Algorithm 21 exactly as the reference model
`MlDsa44.Proofs.Decode.outerStep` (every `return ⊥` turned into `good := 0`,
the count clamped to `index`), one unrolled row per `outerStep`, followed by
the trailing-zero scan. `HInv m₀ M H`: word `HP + 32 t` holds the four bits
`H[r][t]` as lanes, and `M` differs from `m₀` only inside `HP`.
-/

namespace MlDsaOpt44.Proofs.DecodeH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsa44.Proofs.Decode (HS outerStep hs0 outerAll hintGood fillH setH okIdx WF WF_setH setH_get
  WF_hs0 hintBitUnpack_eq)

/-- The hint bytes as `hintBitUnpack` reads them. -/
def yv (cd : ByteArray) : Nat → Nat := fun j => (cd.extract H0 HDR)[j]!.toNat

theorem byteAt_hint {cd : ByteArray} (hcd : HDR ≤ cd.size) {j : Nat} (hj : j < 84) :
    byteAt cd (3648 + j) = yv cd j := by
  have h := DecodeZ.byteAt_extract (cd := cd) (a := H0) (n := 84) (j := j) (by simp only [HDR] at hcd; simp only [H0]; omega) hj
  unfold yv
  rw [show HDR = H0 + 84 from rfl, h]
  rfl

theorem yv_lt (cd : ByteArray) (j : Nat) : yv cd j < 256 := by
  unfold yv; exact Nat.lt_of_lt_of_le (UInt8.toNat_lt _) (by norm_num)

/-- One bitmap update: `HP[y] |= 2^(64 r)`. -/
def upd (M : ByteArray) (lit y : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lit ||| word M (51456 + y * 32)) 32) (51456 + y * 32)

/-- The bit lanes of the hint polynomials. -/
def bits (H : Array Fips204.Poly) (t : Nat) : Nat → Nat := fun r => (H[r]![t]!).toNat

def HInv (m₀ M : ByteArray) (H : Array Fips204.Poly) : Prop :=
  WF H ∧ (∀ t, t < 256 → word M (HP + 32 * t) = pack4 (bits H t)) ∧ FrameExcept m₀ M [(HP, HP + 8192)]

theorem bits_le {H : Array Fips204.Poly} (hH : WF H) {t r : Nat} (ht : t < 256) (hr : r < 4) :
    bits H t r ≤ 1 := by
  unfold bits
  rcases (hH.2 r hr).2 t ht with h | h <;> rw [h] <;> decide

theorem pack4_congr' {a b : Nat → Nat} (h : ∀ k, k < 4 → a k = b k) : pack4 a = pack4 b := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem lane_pack4' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow] <;> omega

theorem or_bit {b : Nat → Nat} (hb : ∀ k, k < 4 → b k ≤ 1) {r : Nat} (hr : r < 4) :
    2 ^ (64 * r) ||| pack4 b = pack4 (fun k => if k = r then 1 else b k) := by
  have hi : 2 ^ (64 * r) = pack4 (fun k => if k = r then 1 else 0) := by
    unfold pack4; interval_cases r <;> simp
  rw [hi, DecodeZ.pack4_or (fun k _ => by split <;> norm_num) (fun k hk => by have := hb k hk; omega)]
  refine pack4_congr' fun k hk => ?_
  split
  · have := hb k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> rfl
  · exact Nat.zero_or _

theorem inv_upd {m₀ M : ByteArray} {H : Array Fips204.Poly} (h : HInv m₀ M H) {r y lit : Nat}
    (hr : r < 4) (hy : y < 256) (hlit : lit = 2 ^ (64 * r)) :
    HInv m₀ (upd M lit y) (setH H r y) := by
  obtain ⟨hwf, hw, hfr⟩ := h
  have hHP : HP = 51456 := rfl
  refine ⟨WF_setH hwf hr, fun t ht => ?_, ?_⟩
  · unfold upd
    by_cases hty : t = y
    · subst hty
      rw [show HP + 32 * t = 51456 + t * 32 by rw [hHP]; omega, word_mstore _ _ _
        (Nat.or_lt_two_pow (by rw [hlit]; exact Nat.pow_lt_pow_right (by omega) (by omega)) (word_lt _ _)),
        show 51456 + t * 32 = HP + 32 * t by rw [hHP]; omega, hw t ht, hlit,
        or_bit (fun k hk => bits_le hwf ht hk) hr]
      refine pack4_congr' fun k hk => ?_
      unfold bits
      rw [setH_get hwf hr hk ht]
      by_cases hk' : k = r
      · rw [if_pos hk', if_pos ⟨hk', rfl⟩]; rfl
      · rw [if_neg hk', if_neg (fun h => hk' h.1)]
    · rw [word_mstore_disjoint _ _ (by rw [hHP]; omega), hw t ht]
      refine pack4_congr' fun k hk => ?_
      unfold bits
      rw [setH_get hwf hr hk ht, if_neg (fun h => hty h.2)]
  · unfold upd
    refine FrameExcept.mono (FrameExcept.trans hfr (FrameExcept.mstore _ _ _)) ?_
    intro q hq
    refine ⟨(HP, HP + 8192), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> dsimp only <;> rw [hHP] <;> omega

theorem beNat_zero {m : ByteArray} {a : Nat} :
    ∀ w, (∀ k, k < w → byteAt m (a + k) = 0) → beNat m a w = 0
  | 0, _ => rfl
  | w + 1, h => by
    rw [beNat, beNat_zero w (fun k hk => h k (by omega)), h w (by omega)]

theorem inv_zero {m : ByteArray} (hz : ZeroOn m HP (HP + 8192)) : HInv m m hs0.H := by
  refine ⟨WF_hs0, fun t ht => ?_, FrameExcept.refl _ _⟩
  rw [word_eq_beNat, beNat_zero 32 (fun k hk => hz _ (by omega) (by simp only [HP] at *; omega))]
  have e : ∀ r, r < 4 → bits hs0.H t r = 0 := by
    intro r hr
    unfold bits
    have h1 : hs0.H[r]! = Fips204.zeroPoly := by
      rw [getElem!_pos hs0.H r (by simp [hs0]; omega)]; simp [hs0]
    rw [h1, getElem!_pos Fips204.zeroPoly t (by simp [Fips204.zeroPoly]; omega)]
    simp [Fips204.zeroPoly]
  rw [pack4_congr' e]
  simp [pack4]

/-! ## One unrolled row, from its block lemmas -/

section
variable {s : State} {ret : Nat} {tail : List UInt256}

/-- The block lemmas of one row (instantiated per row in `dhint_main`). -/
structure RowBlocks (s : State) (ret : Nat) (tail : List UInt256) (r lit pcH pcI pcN : Nat) : Prop where
  hok : ∀ (M : ByteArray) (G : UInt256) (a B : Nat), byteAt s.executionEnv.calldata (3728 + r) = B →
    a ≤ B → B ≤ 80 →
    Reach (callState s pcH (wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53
  hbad : ∀ (M : ByteArray) (G : UInt256) (a B : Nat), a ≤ 80 →
    byteAt s.executionEnv.calldata (3728 + r) = B → B < 256 → (B < a ∨ 80 < B) →
    Reach (callState s pcH (wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65
  iexit : ∀ (M : ByteArray) (G : UInt256) (a b0 : Nat), b0 ≤ 80 →
    Reach (callState s pcI (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcN (wd b0 :: G :: wd ret :: tail) M) 34
  ifirst : ∀ (M : ByteArray) (G : UInt256) (a b0 Y : Nat), a < b0 → b0 ≤ 80 →
    byteAt s.executionEnv.calldata (3648 + a) = Y → Y < 256 →
    Reach (callState s pcI (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (upd M lit Y)) 117
  iok : ∀ (M : ByteArray) (G : UInt256) (a b0 idx P Y : Nat), a < idx → idx < b0 → b0 ≤ 80 →
    byteAt s.executionEnv.calldata (3648 + idx) = Y → Y < 256 →
    byteAt s.executionEnv.calldata (3647 + idx) = P → P < Y →
    Reach (callState s pcI (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (upd M lit Y)) 154
  ibad : ∀ (M : ByteArray) (G : UInt256) (a b0 idx P Y : Nat), a < idx → idx < b0 → b0 ≤ 80 →
    byteAt s.executionEnv.calldata (3648 + idx) = Y → Y < 256 →
    byteAt s.executionEnv.calldata (3647 + idx) = P → P < 256 → Y ≤ P →
    Reach (callState s pcI (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (upd M lit Y)) 161

theorem flag_false : flag false = wd 0 := rfl

theorem row_inner {r lit pcH pcI pcN : Nat} (B : RowBlocks s ret tail r lit pcH pcI pcN)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hr : r < 4) (hlit : lit = 2 ^ (64 * r))
    {m₀ M : ByteArray} {H : Array Fips204.Poly} (hinv : HInv m₀ M H) {a b0 : Nat} (g : Bool)
    (hb : b0 ≤ 80) :
    ∀ k, a + k ≤ b0 → ∃ M', HInv m₀ M' (fillH (yv s.executionEnv.calldata) r H (List.range' a k)) ∧
      Reach (callState s pcI (wd a :: wd b0 :: wd a :: flag g :: wd ret :: tail) M)
        (callState s pcI (wd (a + k) :: wd b0 :: wd a ::
          flag (g && (List.range' a k).all (okIdx (yv s.executionEnv.calldata) a)) :: wd ret :: tail) M')
        (161 * k)
  | 0, _ => ⟨M, by simpa [fillH] using hinv, (Reach.refl _).of_eq rfl (by simp)⟩
  | k + 1, hk => by
    obtain ⟨M', hinv', hreach⟩ := row_inner B hcd hr hlit hinv (a := a) (b0 := b0) g hb k (by omega)
    have hY := byteAt_hint hcd (j := a + k) (by omega)
    have hinv'' := inv_upd hinv' hr (yv_lt s.executionEnv.calldata (a + k)) hlit
    have hfill : fillH (yv s.executionEnv.calldata) r H (List.range' a (k + 1)) =
        setH (fillH (yv s.executionEnv.calldata) r H (List.range' a k)) r (yv s.executionEnv.calldata (a + k)) := by
      simp [fillH, List.range'_concat, List.foldl_append]
    rw [hfill]
    refine ⟨_, hinv'', ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hblk := B.ifirst M' (flag g) a b0 _ (by omega) hb (by simpa using hY) (yv_lt _ _)
      simp only [Nat.add_zero, List.range'_zero, List.all_nil, Bool.and_true] at hreach hblk ⊢
      refine ((hreach.trans hblk).mono (by simp)).of_eq rfl ?_
      simp [okIdx, Nat.add_comm]
    · have hP := byteAt_hint hcd (j := a + k - 1) (by omega)
      rw [show 3648 + (a + k - 1) = 3647 + (a + k) by omega] at hP
      by_cases hPY : yv s.executionEnv.calldata (a + k - 1) < yv s.executionEnv.calldata (a + k)
      · have hblk := B.iok M' (flag (g && (List.range' a k).all (okIdx (yv s.executionEnv.calldata) a)))
          a b0 (a + k) _ _ (by omega) (by omega) hb hY (yv_lt _ _) hP hPY
        refine ((hreach.trans hblk).mono (by omega)).of_eq rfl ?_
        have : okIdx (yv s.executionEnv.calldata) a (a + k) = true := by simp [okIdx, hPY]
        simp [List.range'_concat, List.all_append, this, Nat.add_assoc, Nat.add_comm 1]
      · have hblk := B.ibad M' (flag (g && (List.range' a k).all (okIdx (yv s.executionEnv.calldata) a)))
          a b0 (a + k) _ _ (by omega) (by omega) hb hY (yv_lt _ _) hP (yv_lt _ _) (by omega)
        refine ((hreach.trans hblk).mono (by omega)).of_eq rfl ?_
        have : okIdx (yv s.executionEnv.calldata) a (a + k) = false := by simp [okIdx, hPY]; omega
        simp [List.range'_concat, List.all_append, this, Nat.add_assoc, Nat.add_comm 1, flag]

theorem row_step {r lit pcH pcI pcN : Nat} (B : RowBlocks s ret tail r lit pcH pcI pcN)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hr : r < 4) (hlit : lit = 2 ^ (64 * r))
    {m₀ M : ByteArray} (st : HS) (hinv : HInv m₀ M st.H) (ha : st.index ≤ 80) :
    ∃ M', HInv m₀ M' (outerStep (yv s.executionEnv.calldata) st r).H ∧
      st.index ≤ (outerStep (yv s.executionEnv.calldata) st r).index ∧
      (outerStep (yv s.executionEnv.calldata) st r).index ≤ 80 ∧
      Reach (callState s pcH (wd st.index :: flag st.good :: wd ret :: tail) M)
        (callState s pcN (wd (outerStep (yv s.executionEnv.calldata) st r).index ::
          flag (outerStep (yv s.executionEnv.calldata) st r).good :: wd ret :: tail) M')
        (99 + 161 * ((outerStep (yv s.executionEnv.calldata) st r).index - st.index)) := by
  have hB := byteAt_hint hcd (j := 80 + r) (by omega)
  rw [show 3648 + (80 + r) = 3728 + r by omega] at hB
  by_cases hbad : yv s.executionEnv.calldata (80 + r) < st.index ∨ 80 < yv s.executionEnv.calldata (80 + r)
  · have hstep : outerStep (yv s.executionEnv.calldata) st r = ⟨st.index, false, st.H⟩ := by
      unfold outerStep; dsimp only; rw [if_pos hbad]
    rw [hstep]; clear hstep
    refine ⟨M, hinv, le_rfl, ha, ?_⟩
    have h1 := B.hbad M (flag st.good) st.index _ ha hB (yv_lt _ _) hbad
    have h2 := B.iexit M (wd 0) st.index st.index ha
    exact ((h1.trans h2).mono (by simp)).of_eq rfl (by simp [flag])
  · have hstep : outerStep (yv s.executionEnv.calldata) st r = ⟨yv s.executionEnv.calldata (80 + r),
        st.good && (List.range' st.index (yv s.executionEnv.calldata (80 + r) - st.index)).all
          (okIdx (yv s.executionEnv.calldata) st.index),
        fillH (yv s.executionEnv.calldata) r st.H
          (List.range' st.index (yv s.executionEnv.calldata (80 + r) - st.index))⟩ := by
      unfold outerStep; dsimp only; rw [if_neg hbad]
    rw [hstep]; clear hstep
    have hB80 : yv s.executionEnv.calldata (80 + r) ≤ 80 := by omega
    obtain ⟨M', hinv', hreach⟩ := row_inner B hcd hr hlit hinv (a := st.index)
      (b0 := yv s.executionEnv.calldata (80 + r)) st.good hB80
      (yv s.executionEnv.calldata (80 + r) - st.index) (by omega)
    have h1 := B.hok M (flag st.good) st.index _ hB (by omega) hB80
    rw [show st.index + (yv s.executionEnv.calldata (80 + r) - st.index) =
      yv s.executionEnv.calldata (80 + r) by omega] at hreach
    have h2 := B.iexit M' (flag (st.good && (List.range' st.index
      (yv s.executionEnv.calldata (80 + r) - st.index)).all (okIdx (yv s.executionEnv.calldata) st.index)))
      st.index _ hB80
    refine ⟨M', hinv', ?_, ?_, ?_⟩
    · dsimp only; exact Nat.le_of_not_lt (fun h => hbad (Or.inl h))
    · dsimp only; exact hB80
    dsimp only
    exact (h1.trans (hreach.trans h2)).mono (by omega)

/-- The trailing scan: `k` iterations from `idx = a`. -/
theorem tscan (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (M : ByteArray) {a : Nat} (g : Bool) :
    ∀ k, a + k ≤ 80 →
      Reach (callState s 7970 (wd a :: flag g :: wd ret :: tail) M)
        (callState s 7970 (wd (a + k) ::
          flag (g && (List.range' a k).all (fun idx => yv s.executionEnv.calldata idx == 0)) ::
          wd ret :: tail) M) (85 * k)
  | 0, _ => (Reach.refl _).of_eq rfl (by simp)
  | k + 1, hk => by
    have hreach := tscan hs htl hcd M (a := a) g k (by omega)
    have hY := byteAt_hint hcd (j := a + k) (by omega)
    by_cases hz : yv s.executionEnv.calldata (a + k) = 0
    · rw [hz] at hY
      have hblk := h_tzero (ret := ret) (tail := tail) hs htl M
        (flag (g && (List.range' a k).all (fun idx => yv s.executionEnv.calldata idx == 0))) (by omega) hY
      refine ((hreach.trans hblk).mono (by omega)).of_eq rfl ?_
      simp [List.range'_concat, List.all_append, hz, Nat.add_assoc, Nat.add_comm 1]
    · have hblk := h_tnz (ret := ret) (tail := tail) hs htl M
        (flag (g && (List.range' a k).all (fun idx => yv s.executionEnv.calldata idx == 0))) (by omega) hY
        (yv_lt _ _) hz
      refine ((hreach.trans hblk).mono (by omega)).of_eq rfl ?_
      simp [List.range'_concat, List.all_append, hz, Nat.add_assoc, Nat.add_comm 1, flag]

theorem hint_cost {a1 a2 a3 a4 : Nat} (h1 : 0 ≤ a1) (h2 : a1 ≤ a2) (h3 : a2 ≤ a3) (h4 : a3 ≤ a4)
    (h5 : a4 ≤ 80) :
    6 + ((99 + 161 * (a1 - 0)) + ((99 + 161 * (a2 - a1)) + ((99 + 161 * (a3 - a2)) +
      ((99 + 161 * (a4 - a3)) + (85 * (80 - a4) + 40))))) ≤ 312 + 85 * 161 := by
  omega

end

end MlDsaOpt44.Proofs.DecodeH
