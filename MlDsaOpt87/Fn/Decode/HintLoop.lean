import MlDsaOpt87.Fn.Decode.HintBlocks
import MlDsaOpt87.Fn.Decode.HintModel
import MlDsaOpt87.Fn.Decode.ZMath
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The loops of `dhint` (ML-DSA-87, WP G2)

Twin of `MlDsaOpt44/Fn/Decode/HintLoop.lean` for `k = 8`, `ω = 75` and two bitmap row
groups: the bytecode runs Algorithm 21 exactly as `outerStep 75` (one unrolled row per
step), followed by the trailing-zero scan. `HInv m₀ M H`: word `HP + 0x2000 g + 32 t`
holds the four bits `H[4 g + j][t]` as lanes (every row is written), and `M` differs
from `m₀` only inside `[HP, HP + 0x4000)`.
-/

namespace MlDsaOpt87.Proofs.DecodeH

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- The hint bytes as `hintBitUnpack` reads them. -/
def yv (cd : ByteArray) : Nat → Nat := fun j => (cd.extract H0 HDR)[j]!.toNat

theorem byteAt_hint (cd : ByteArray) {j : Nat} (hj : j < 83) :
    byteAt cd (7136 + j) = yv cd j := by
  unfold yv
  rw [show H0 = 7136 from rfl, show HDR = 7219 from rfl, DecodeZ.byteAt_extract' (by omega)]

theorem yv_lt (cd : ByteArray) (j : Nat) : yv cd j < 256 := by
  unfold yv; exact Nat.lt_of_lt_of_le (UInt8.toNat_lt _) (by norm_num)

/-- One bitmap update: `[base + 32 y] |= lit`. -/
def upd (M : ByteArray) (lit base y : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lit ||| word M (base + y * 32)) 32) (base + y * 32)

/-- The bit lanes of the hint polynomials. -/
def bits (H : Array Fips204.Poly) (t : Nat) : Nat → Nat := fun r => (H[r]![t]!).toNat

def HInv (m₀ M : ByteArray) (H : Array Fips204.Poly) : Prop :=
  WF 8 H ∧ (∀ g, g < 2 → ∀ t, t < 256 → word M (HP + 0x2000 * g + 32 * t) = pack4 (fun j => bits H t (4 * g + j))) ∧
    FrameExcept m₀ M [(HP, HP + 0x4000)]

theorem bits_le {H : Array Fips204.Poly} (hH : WF 8 H) {t : Nat} (ht : t < 256) (r : Nat) :
    bits H t r ≤ 1 := by
  unfold bits
  by_cases hr : r < 8
  · rcases (hH.2 r hr).2 t ht with h | h <;> rw [h] <;> decide
  · rw [WF_get_out hH (by omega)]; decide

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

theorem inv_upd {m₀ M : ByteArray} {H : Array Fips204.Poly} (h : HInv m₀ M H) {r y lit base : Nat}
    (hr : r < 8) (hy : y < 256) (hlit : lit = 2 ^ (64 * (r % 4))) (hbase : base = HP + 0x2000 * (r / 4)) :
    HInv m₀ (upd M lit base y) (setH H r y) := by
  obtain ⟨hwf, hw, hfr⟩ := h
  have hHP : HP = 67840 := rfl
  refine ⟨WF_setH hwf hr, fun g hg t ht => ?_, ?_⟩
  · unfold upd
    by_cases hty : g = r / 4 ∧ t = y
    · obtain ⟨rfl, rfl⟩ := hty
      rw [show HP + 0x2000 * (r / 4) + 32 * t = base + t * 32 by rw [hbase]; omega, word_mstore _ _ _
        (Nat.or_lt_two_pow (by rw [hlit]; exact Nat.pow_lt_pow_right (by omega) (by omega)) (word_lt _ _)),
        show base + t * 32 = HP + 0x2000 * (r / 4) + 32 * t by rw [hbase]; omega, hw _ hg t ht, hlit,
        or_bit (fun k _ => bits_le hwf ht _) (Nat.mod_lt _ (by omega))]
      refine pack4_congr' fun k hk => ?_
      unfold bits
      rw [setH_get hwf hr ht]
      by_cases hk' : k = r % 4
      · rw [if_pos hk', if_pos ⟨by omega, rfl⟩]; rfl
      · rw [if_neg hk', if_neg (fun h => hk' (by omega))]
    · rw [word_mstore_disjoint _ _ (by rw [hbase, hHP]; omega), hw g hg t ht]
      refine pack4_congr' fun k hk => ?_
      unfold bits
      rw [setH_get hwf hr ht, if_neg (fun h => hty ⟨by omega, h.2⟩)]
  · unfold upd
    refine FrameExcept.mono (FrameExcept.trans hfr (FrameExcept.mstore _ _ _)) ?_
    intro q hq
    refine ⟨(HP, HP + 0x4000), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> dsimp only <;> subst hbase <;> rw [hHP] <;> omega

theorem beNat_zero {m : ByteArray} {a : Nat} :
    ∀ w, (∀ k, k < w → byteAt m (a + k) = 0) → beNat m a w = 0
  | 0, _ => rfl
  | w + 1, h => by
    rw [beNat, beNat_zero w (fun k hk => h k (by omega)), h w (by omega)]

theorem inv_zero {m : ByteArray} (hz : ZeroOn m HP (HP + 0x4000)) : HInv m m (hs0 8).H := by
  refine ⟨WF_hs0 8, fun g hg t ht => ?_, FrameExcept.refl _ _⟩
  rw [word_eq_beNat, beNat_zero 32 (fun k hk => hz _ (by omega) (by simp only [HP] at *; omega))]
  have e : ∀ j, j < 4 → bits (hs0 8).H t (4 * g + j) = 0 := by
    intro j _
    unfold bits
    by_cases hr : 4 * g + j < 8
    · have h1 : (hs0 8).H[4 * g + j]! = Fips204.zeroPoly := by
        rw [getElem!_pos (hs0 8).H (4 * g + j) (by simp [hs0]; omega)]; simp [hs0]
      rw [h1, getElem!_pos Fips204.zeroPoly t (by simp [Fips204.zeroPoly]; omega)]
      simp [Fips204.zeroPoly]
    · rw [WF_get_out (WF_hs0 8) (by omega)]; rfl
  rw [pack4_congr' e]
  simp [pack4]

/-! ## One unrolled row, from its block lemmas -/

section
variable {s : State} {ret : Nat} {tail : List UInt256}

/-- The block lemmas of one row (instantiated per row in `dhint_main`). -/
structure RowBlocks (s : State) (ret : Nat) (tail : List UInt256) (r lit base pcH pcI pcN : Nat) : Prop where
  hok : ∀ (M : ByteArray) (G : UInt256) (a B : Nat), byteAt s.executionEnv.calldata (7211 + r) = B →
    a ≤ B → B ≤ 75 →
    Reach (callState s pcH (wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53
  hbad : ∀ (M : ByteArray) (G : UInt256) (a B : Nat), a ≤ 75 →
    byteAt s.executionEnv.calldata (7211 + r) = B → B < 256 → (B < a ∨ 75 < B) →
    Reach (callState s pcH (wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65
  iexit : ∀ (M : ByteArray) (G : UInt256) (a b0 : Nat), b0 ≤ 75 →
    Reach (callState s pcI (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcN (wd b0 :: G :: wd ret :: tail) M) 34
  ifirst : ∀ (M : ByteArray) (G : UInt256) (a b0 Y : Nat), a < b0 → b0 ≤ 75 →
    byteAt s.executionEnv.calldata (7136 + a) = Y → Y < 256 →
    Reach (callState s pcI (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (upd M lit base Y)) 117
  iok : ∀ (M : ByteArray) (G : UInt256) (a b0 idx P Y : Nat), a < idx → idx < b0 → b0 ≤ 75 →
    byteAt s.executionEnv.calldata (7136 + idx) = Y → Y < 256 →
    byteAt s.executionEnv.calldata (7135 + idx) = P → P < Y →
    Reach (callState s pcI (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (upd M lit base Y)) 154
  ibad : ∀ (M : ByteArray) (G : UInt256) (a b0 idx P Y : Nat), a < idx → idx < b0 → b0 ≤ 75 →
    byteAt s.executionEnv.calldata (7136 + idx) = Y → Y < 256 →
    byteAt s.executionEnv.calldata (7135 + idx) = P → P < 256 → Y ≤ P →
    Reach (callState s pcI (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M)
      (callState s pcI (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (upd M lit base Y)) 161

theorem flag_false : flag false = wd 0 := rfl

theorem row_inner {r lit base pcH pcI pcN : Nat} (B : RowBlocks s ret tail r lit base pcH pcI pcN)
    (hr : r < 8) (hlit : lit = 2 ^ (64 * (r % 4))) (hbase : base = HP + 0x2000 * (r / 4))
    {m₀ M : ByteArray} {H : Array Fips204.Poly} (hinv : HInv m₀ M H) {a b0 : Nat} (g : Bool)
    (hb : b0 ≤ 75) :
    ∀ k, a + k ≤ b0 → ∃ M', HInv m₀ M' (fillH (yv s.executionEnv.calldata) r H (List.range' a k)) ∧
      Reach (callState s pcI (wd a :: wd b0 :: wd a :: flag g :: wd ret :: tail) M)
        (callState s pcI (wd (a + k) :: wd b0 :: wd a ::
          flag (g && (List.range' a k).all (okIdx (yv s.executionEnv.calldata) a)) :: wd ret :: tail) M')
        (161 * k)
  | 0, _ => ⟨M, by simpa [fillH] using hinv, (Reach.refl _).of_eq rfl (by simp)⟩
  | k + 1, hk => by
    obtain ⟨M', hinv', hreach⟩ := row_inner B hr hlit hbase hinv (a := a) (b0 := b0) g hb k (by omega)
    have hY := byteAt_hint s.executionEnv.calldata (j := a + k) (by omega)
    have hinv'' := inv_upd hinv' hr (yv_lt s.executionEnv.calldata (a + k)) hlit hbase
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
    · have hP := byteAt_hint s.executionEnv.calldata (j := a + k - 1) (by omega)
      rw [show 7136 + (a + k - 1) = 7135 + (a + k) by omega] at hP
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

theorem row_step {r lit base pcH pcI pcN : Nat} (B : RowBlocks s ret tail r lit base pcH pcI pcN)
    (hr : r < 8) (hlit : lit = 2 ^ (64 * (r % 4))) (hbase : base = HP + 0x2000 * (r / 4))
    {m₀ M : ByteArray} (st : HS) (hinv : HInv m₀ M st.H) (ha : st.index ≤ 75) :
    ∃ M', HInv m₀ M' (outerStep 75 (yv s.executionEnv.calldata) st r).H ∧
      st.index ≤ (outerStep 75 (yv s.executionEnv.calldata) st r).index ∧
      (outerStep 75 (yv s.executionEnv.calldata) st r).index ≤ 75 ∧
      Reach (callState s pcH (wd st.index :: flag st.good :: wd ret :: tail) M)
        (callState s pcN (wd (outerStep 75 (yv s.executionEnv.calldata) st r).index ::
          flag (outerStep 75 (yv s.executionEnv.calldata) st r).good :: wd ret :: tail) M')
        (99 + 161 * ((outerStep 75 (yv s.executionEnv.calldata) st r).index - st.index)) := by
  have hB := byteAt_hint s.executionEnv.calldata (j := 75 + r) (by omega)
  rw [show 7136 + (75 + r) = 7211 + r by omega] at hB
  by_cases hbad : yv s.executionEnv.calldata (75 + r) < st.index ∨ 75 < yv s.executionEnv.calldata (75 + r)
  · have hstep : outerStep 75 (yv s.executionEnv.calldata) st r = ⟨st.index, false, st.H⟩ := by
      unfold outerStep; dsimp only; rw [if_pos hbad]
    rw [hstep]; clear hstep
    refine ⟨M, hinv, le_rfl, ha, ?_⟩
    have h1 := B.hbad M (flag st.good) st.index _ ha hB (yv_lt _ _) hbad
    have h2 := B.iexit M (wd 0) st.index st.index ha
    exact ((h1.trans h2).mono (by simp)).of_eq rfl (by simp [flag])
  · have hstep : outerStep 75 (yv s.executionEnv.calldata) st r = ⟨yv s.executionEnv.calldata (75 + r),
        st.good && (List.range' st.index (yv s.executionEnv.calldata (75 + r) - st.index)).all
          (okIdx (yv s.executionEnv.calldata) st.index),
        fillH (yv s.executionEnv.calldata) r st.H
          (List.range' st.index (yv s.executionEnv.calldata (75 + r) - st.index))⟩ := by
      unfold outerStep; dsimp only; rw [if_neg hbad]
    rw [hstep]; clear hstep
    have hB55 : yv s.executionEnv.calldata (75 + r) ≤ 75 := by omega
    obtain ⟨M', hinv', hreach⟩ := row_inner B hr hlit hbase hinv (a := st.index)
      (b0 := yv s.executionEnv.calldata (75 + r)) st.good hB55
      (yv s.executionEnv.calldata (75 + r) - st.index) (by omega)
    have h1 := B.hok M (flag st.good) st.index _ hB (by omega) hB55
    rw [show st.index + (yv s.executionEnv.calldata (75 + r) - st.index) =
      yv s.executionEnv.calldata (75 + r) by omega] at hreach
    have h2 := B.iexit M' (flag (st.good && (List.range' st.index
      (yv s.executionEnv.calldata (75 + r) - st.index)).all (okIdx (yv s.executionEnv.calldata) st.index)))
      st.index _ hB55
    refine ⟨M', hinv', ?_, ?_, ?_⟩
    · dsimp only; exact Nat.le_of_not_lt (fun h => hbad (Or.inl h))
    · dsimp only; exact hB55
    dsimp only
    exact (h1.trans (hreach.trans h2)).mono (by omega)

/-- The trailing scan: `k` iterations from `idx = a`. -/
theorem tscan (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {a : Nat} (g : Bool) :
    ∀ k, a + k ≤ 75 →
      Reach (callState s 9851 (wd a :: flag g :: wd ret :: tail) M)
        (callState s 9851 (wd (a + k) ::
          flag (g && (List.range' a k).all (fun idx => yv s.executionEnv.calldata idx == 0)) ::
          wd ret :: tail) M) (85 * k)
  | 0, _ => (Reach.refl _).of_eq rfl (by simp)
  | k + 1, hk => by
    have hreach := tscan hs htl M (a := a) g k (by omega)
    have hY := byteAt_hint s.executionEnv.calldata (j := a + k) (by omega)
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

end

end MlDsaOpt87.Proofs.DecodeH
