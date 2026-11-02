import MlDsaOptGlam44.Main.Alt.Inv
import MlDsaOpt44.Math
import MlDsaOpt44.Math.Facts
set_option warningAsError true
/-!
# `pass3f4b`'s word is `Â ẑ` lane-wise (`accAt_alt`)

The long-message schedule's layout: columns 0, 1 aligned in `CW`, `HP`; rows
`0 … 2` of columns 2, 3 in lanes `0 … 2` of `SB`, `SB + 8192` (`Col3Lo`; lane 3
masked off by `altWord`); the Kronecker pair `(A[3][3], A[3][2])` in lanes 2, 3
of `ABUF`: lane 3 of `(ABUF & top128) · (ẑ >> 128)` is `A33 ẑ3 + A32 ẑ2`, the
masked lanes `0 … 2` vanish. As `accAt_of_acc4` (`MlDsaOpt44/Main/Win/Math.lean`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa44

private theorem okA_get {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 4) (hs : s < 4) :
    (aOf cd r s).isSome = true := by
  unfold okA at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at this
  exact this s (List.mem_range.mpr hs)

private theorem okCol_of_okA {cd : ByteArray} (h : okA cd = true) {s : Nat} (hs : s < 4) :
    okCol cd s = true := by
  unfold okCol
  rw [List.all_eq_true]
  intro r hr
  exact okA_get h (List.mem_range.mp hr) hs

private theorem okCol3_of_okA {cd : ByteArray} (h : okA cd = true) {s : Nat} (hs : s < 4) :
    okCol3 cd s = true := by
  unfold okCol3
  rw [List.all_eq_true]
  intro r hr
  exact okA_get h (by have := List.mem_range.mp hr; omega) hs

private theorem aD_lt23 {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 4) (hs : s < 4)
    {t : Nat} (ht : t < 256) : ((aD cd r s)[t]!).toNat < 2 ^ 23 := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (okA_get h hr hs)
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  have := ((rejNTTPoly_range _ a ha).2 t ht)
  have hq : (Fips204.q : Int) < 2 ^ 23 := by norm_num [Fips204.q]
  omega

private theorem sum_range4 (f : Nat → Int) : ((List.range 4).map f).sum = f 0 + f 1 + f 2 + f 3 := by
  simp [List.range_succ]; ring

private theorem and_top {y n : Nat} (hy : y < 2 ^ 256) (hn : n ≤ 256) :
    y &&& (2 ^ 256 - 2 ^ n) = y / 2 ^ n * 2 ^ n := by
  have e : 2 ^ 256 - 2 ^ n = (2 ^ (256 - n) - 1) * 2 ^ n := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hn]
  rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h : n ≤ i
  · have e1 : i - n + n = i := by omega
    by_cases h2 : i < 256
    · simp [h, e1, show i - n < 256 - n by omega]
    · have : y < 2 ^ i := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [h, e1, Nat.testBit_lt_two_pow this]
  · simp [h]

private theorem mul_lt51 {a b : Nat} (ha : a < 2 ^ 23) (hb : b < 2 ^ 28) : a * b < 2 ^ 51 :=
  lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by norm_num)

/-- Lanes `0 … 2` of `w` (lane 3 masked off). -/
private theorem low192 {w : Nat} (a0 a1 a2 : Nat) (h0 : lane w 0 = a0) (h1 : lane w 1 = a1)
    (h2 : lane w 2 = a2) : w &&& (2 ^ 192 - 1) = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, ← h0, ← h1, ← h2]
  unfold lane; norm_num; omega

/-- The arithmetic of `altWord`: no carries between lanes. -/
private theorem alt_core {w0 w1 w2 w3 w4 z : Nat} (A : Nat → Nat → Nat)
    (hA : ∀ r s, r < 4 → s < 4 → A r s < 2 ^ 23)
    (hz : ∀ k, k < 4 → lane z k < 2 ^ 28) (hzlt : z < 2 ^ 256)
    (h0 : w0 = pack4 fun r => A r 0) (h1 : w1 = pack4 fun r => A r 1)
    (h2 : ∀ r, r < 3 → lane w2 r = A r 2) (h3 : ∀ r, r < 3 → lane w3 r = A r 3)
    (h4 : lane w4 2 = A 3 3) (h4' : lane w4 3 = A 3 2) (hw4 : w4 < 2 ^ 256) :
    (w0 * lane z 0 + w1 * lane z 1 + (w2 &&& (2 ^ 192 - 1)) * lane z 2 +
      (w3 &&& (2 ^ 192 - 1)) * lane z 3 +
      ((w4 &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192))) % 2 ^ 256 =
    pack4 fun r => A r 0 * lane z 0 + A r 1 * lane z 1 + A r 2 * lane z 2 + A r 3 * lane z 3 := by
  have ez : z / 2 ^ 128 = lane z 2 + 2 ^ 64 * lane z 3 := by
    unfold lane; norm_num; omega
  have e2 := low192 (A 0 2) (A 1 2) (A 2 2) (h2 0 (by omega)) (h2 1 (by omega)) (h2 2 (by omega))
  have e3 := low192 (A 0 3) (A 1 3) (A 2 3) (h3 0 (by omega)) (h3 1 (by omega)) (h3 2 (by omega))
  have e4 : w4 / 2 ^ 128 = A 3 3 + 2 ^ 64 * A 3 2 := by
    rw [← h4, ← h4']
    unfold lane; norm_num; omega
  have hk : (w4 &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192) =
      2 ^ 192 * (A 3 3 * lane z 3 + A 3 2 * lane z 2) := by
    rw [show M64 * 2 ^ 192 = 2 ^ 256 - 2 ^ 192 by unfold M64; norm_num, and_top hw4 (by norm_num),
      and_top (Nat.mod_lt _ (by norm_num)) (by norm_num), e4, ez]
    have ex : (A 3 3 + 2 ^ 64 * A 3 2) * 2 ^ 128 * (lane z 2 + 2 ^ 64 * lane z 3) =
        2 ^ 128 * (A 3 3 * lane z 2) + 2 ^ 192 * (A 3 3 * lane z 3 + A 3 2 * lane z 2) +
          2 ^ 256 * (A 3 2 * lane z 3) := by ring
    have b1 := mul_lt51 (hA 3 3 (by omega) (by omega)) (hz 2 (by omega))
    have b2 := mul_lt51 (hA 3 3 (by omega) (by omega)) (hz 3 (by omega))
    have b3 := mul_lt51 (hA 3 2 (by omega) (by omega)) (hz 2 (by omega))
    rw [ex]
    generalize A 3 3 * lane z 2 = p at *
    generalize A 3 3 * lane z 3 = c1 at *
    generalize A 3 2 * lane z 2 = c2 at *
    generalize A 3 2 * lane z 3 = d at *
    omega
  have hlt : (pack4 fun r => A r 0 * lane z 0 + A r 1 * lane z 1 + A r 2 * lane z 2 + A r 3 * lane z 3) <
      2 ^ 256 := pack4_lt fun r hr => by
    have := mul_lt51 (hA r 0 hr (by omega)) (hz 0 (by omega))
    have := mul_lt51 (hA r 1 hr (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA r 2 hr (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA r 3 hr (by omega)) (hz 3 (by omega))
    omega
  refine (congrArg (· % 2 ^ 256) ?_).trans (Nat.mod_eq_of_lt hlt)
  rw [hk, h0, h1, e2, e3]
  unfold pack4
  ring

/-- `pass3f4b`'s words are `Â ẑ` (bounded representatives mod `q`) when `A` exists. -/
theorem accAt_alt {cd m m' : ByteArray} (hzh : ZHatAt m cd)
    (hcw : ColAt m CW cd 0) (hhp : ColAt m HP cd 1) (hsb : Col3Lo m SB cd 2)
    (hsb2 : Col3Lo m (SB + 8192) cd 3)
    (hab : okA cd = true → ∀ t, t < 256 →
      lane (word m (ABUF + 32 * t)) 2 = ((aD cd 3 3)[t]!).toNat ∧
      lane (word m (ABUF + 32 * t)) 3 = ((aD cd 3 2)[t]!).toNat)
    (hacc : ∀ t, t < 256 → word m' (ACC + 32 * t) = altWord m t) :
    AccAt m' cd := by
  intro hok r hr t ht
  have hz : ∀ k, k < 4 → lane (word m (ZH + 32 * t)) k < 2 ^ 28 := fun k hk => (hzh k hk t ht).1
  have hA : ∀ r s, r < 4 → s < 4 → ((aD cd r s)[t]!).toNat < 2 ^ 23 := fun r s hr hs =>
    aD_lt23 hok hr hs ht
  obtain ⟨hE2, hE3⟩ := hab hok t ht
  have hw : word m' (ACC + 32 * t) = pack4 fun r =>
      ((aD cd r 0)[t]!).toNat * lane (word m (ZH + 32 * t)) 0 +
        ((aD cd r 1)[t]!).toNat * lane (word m (ZH + 32 * t)) 1 +
        ((aD cd r 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2 +
        ((aD cd r 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 := by
    rw [hacc t ht]
    exact alt_core (fun r s => ((aD cd r s)[t]!).toNat) hA hz (word_lt _ _)
      (hcw (okCol_of_okA hok (by omega)) t ht) (hhp (okCol_of_okA hok (by omega)) t ht)
      (hsb (okCol3_of_okA hok (by omega)) t ht) (hsb2 (okCol3_of_okA hok (by omega)) t ht)
      hE2 hE3 (word_lt _ _)
  have hle : ∀ r, r < 4 → ((aD cd r 0)[t]!).toNat * lane (word m (ZH + 32 * t)) 0 +
        ((aD cd r 1)[t]!).toNat * lane (word m (ZH + 32 * t)) 1 +
        ((aD cd r 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2 +
        ((aD cd r 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 < 2 ^ 57 := fun r hr => by
    have := mul_lt51 (hA r 0 hr (by omega)) (hz 0 (by omega))
    have := mul_lt51 (hA r 1 hr (by omega)) (hz 1 (by omega))
    have := mul_lt51 (hA r 2 hr (by omega)) (hz 2 (by omega))
    have := mul_lt51 (hA r 3 hr (by omega)) (hz 3 (by omega))
    omega
  rw [hw, lane_pack4 (fun r hr => by have := hle r hr; omega) hr]
  refine ⟨hle r hr, ?_⟩
  have hnn : ∀ s, s < 4 → (((aD cd r s)[t]!).toNat : Int) = (aD cd r s)[t]! := fun s hs => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (okA_get hok hr hs)
    have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
    rw [hD]
    exact Int.toNat_of_nonneg ((rejNTTPoly_range _ a ha).2 t ht).1
  have hm : ∀ s, s < 4 → (lane (word m (ZH + 32 * t)) s : Int) % (Fips204.q : Int) =
      (zHat cd s)[t]! % (Fips204.q : Int) := fun s hs =>
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (hzh s hs t ht).2
  have hrow : (azRow cd r)[t]! = ((List.range 4).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum %
      (Fips204.q : Int) := by
    unfold azRow; exact getElem!_map_range 256 t _ ht
  rw [hrow, sum_range4]
  push_cast
  rw [hnn 0 (by omega), hnn 1 (by omega), hnn 2 (by omega), hnn 3 (by omega)]
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  have m0 := hm 0 (by omega)
  have m1 := hm 1 (by omega)
  have m2 := hm 2 (by omega)
  have m3 := hm 3 (by omega)
  exact Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.mul_left _ m0) (Int.ModEq.mul_left _ m1))
    (Int.ModEq.mul_left _ m2)) (Int.ModEq.mul_left _ m3)

end MlDsaOptGlam44.Proofs
