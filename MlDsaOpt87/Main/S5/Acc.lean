import MlDsaOpt87.Main.S5.Round
set_option warningAsError true
/-!
# Accumulator facts for the Kronecker group 14 of ML-DSA-87 (WP S5)

* `s5_okA_get`, `s5_okUpTo_of_okA`, `s5_okMid_of_okA`: `okA` gives every guard.
* `s5_kron`: lane 3 of the Kronecker product `ABUF[t] · ((ZH[t] >> 192) | (ZH2[t] << 64))`.
* `s5_acc7`: adding a lane-3 term to a packed accumulator word.
* `s5_accAt_of`: `AccAt` from the exact lane sums over all seven columns.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa
open MlDsaOpt44.Proofs

theorem s5_okA_get {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 8) (hs : s < 7) :
    (aOf cd r s).isSome = true := by
  unfold okA at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at this
  exact this s (List.mem_range.mpr hs)

theorem s5_okCol_of_okA {cd : ByteArray} (h : okA cd = true) {rb s nr : Nat} (hrb : rb < 2)
    (hnr : nr ≤ 4) (hs : s < 7) : okCol cd rb s nr = true := by
  unfold okCol
  rw [List.all_eq_true]
  intro r hr
  exact s5_okA_get h (by have := List.mem_range.mp hr; omega) hs

theorem s5_okUpTo_of_okA {cd : ByteArray} (h : okA cd = true) {rb nr : Nat} (hrb : rb < 2) (hnr : nr ≤ 4) :
    ∀ n, n ≤ 7 → okUpTo cd rb nr n = true
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [okUpTo, Bool.and_eq_true]
    exact ⟨s5_okUpTo_of_okA h hrb hnr n (by omega), s5_okCol_of_okA h hrb hnr (by omega)⟩

theorem s5_okMid_of_okA {cd : ByteArray} (h : okA cd = true) : ∀ n, n ≤ 7 → okMid cd n = true
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [okMid, Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨s5_okMid_of_okA h n (by omega),
      Or.inr (s5_okCol_of_okA h (by norm_num) (by norm_num) (by omega))⟩

theorem s5_okRow7_of_okA {cd : ByteArray} (h : okA cd = true) : okRow7 cd = true := by
  unfold okRow7
  rw [List.all_eq_true]
  intro i hi
  exact s5_okA_get h (by norm_num) (by have := List.mem_range.mp hi; omega)

/-! ## The Kronecker word -/

theorem s5_and_high {w n k : Nat} (hw : w < 2 ^ n) (hk : k ≤ n) :
    w &&& (2 ^ n - 2 ^ k) = 2 ^ k * (w / 2 ^ k) := by
  have e : 2 ^ n - 2 ^ k = 2 ^ k * (2 ^ (n - k) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hj : j ≥ k
  · rw [show j - k + k = j by omega]
    by_cases hjn : j < n
    · simp [hj, show j - k < n - k by omega]
    · have : w.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this]
  · simp [hj]

theorem s5_or_eq_add {a : Nat} (c : Nat) (h : a < 2 ^ 64) : a ||| 2 ^ 64 * c = a + 2 ^ 64 * c := by
  rw [Nat.or_comm, show 2 ^ 64 * c = c <<< 64 by rw [Nat.shiftLeft_eq, Nat.mul_comm],
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  omega

/-- Lane 3 of the Kronecker product of group 14: `Σ_i w_i · y_{3 − i}` with
`y = (lane 3 of zl, lanes 0–2 of zh)`. -/
theorem s5_kron {w zl zh : Nat} (hw : w < 2 ^ 256) (hzl : zl < 2 ^ 256)
    (ha : ∀ k, k < 4 → lane w k < 2 ^ 23) (hz3 : lane zl 3 < 2 ^ 28)
    (hz : ∀ k, k < 3 → lane zh k < 2 ^ 28) :
    w * (zl / 2 ^ 192 ||| zh * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&& (M64 * 2 ^ 192) =
      2 ^ 192 * (lane w 0 * lane zh 2 + lane w 1 * lane zh 1 + lane w 2 * lane zh 0 +
        lane w 3 * lane zl 3) := by
  have hw' : w = lane w 0 + 2 ^ 64 * lane w 1 + 2 ^ 128 * lane w 2 + 2 ^ 192 * lane w 3 := by
    unfold lane; norm_num at hw ⊢; omega
  have hzl' : zl / 2 ^ 192 = lane zl 3 := by
    unfold lane; norm_num at hzl ⊢; omega
  have hzh' : zh * 2 ^ 64 % 2 ^ 256 = 2 ^ 64 * (lane zh 0 + 2 ^ 64 * lane zh 1 + 2 ^ 128 * lane zh 2) := by
    have e : zh * 2 ^ 64 % 2 ^ 256 = 2 ^ 64 * (zh % 2 ^ 192) := by
      rw [Nat.mul_comm, show (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 192 by norm_num, Nat.mul_mod_mul_left]
    rw [e]
    congr 1
    unfold lane; norm_num; omega
  have h3 : lane zl 3 < 2 ^ 64 := Nat.lt_trans hz3 (by norm_num)
  rw [hzl', hzh', s5_or_eq_add _ h3]
  have hw0 := ha 0 (by omega); have hw1 := ha 1 (by omega)
  have hw2 := ha 2 (by omega); have hw3 := ha 3 (by omega)
  have hz0 := hz 0 (by omega); have hz1 := hz 1 (by omega); have hz2 := hz 2 (by omega)
  generalize lane w 0 = a0 at *
  generalize lane w 1 = a1 at *
  generalize lane w 2 = a2 at *
  generalize lane w 3 = a3 at *
  generalize lane zh 0 = y1 at *
  generalize lane zh 1 = y2 at *
  generalize lane zh 2 = y3 at *
  generalize lane zl 3 = y0 at *
  subst hw'
  have m00 : a0 * y0 < 2 ^ 51 := by
    calc a0 * y0 < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' hw0 hz3
      _ = 2 ^ 51 := by norm_num
  have p : ∀ a y : Nat, a < 2 ^ 23 → y < 2 ^ 28 → a * y < 2 ^ 51 := fun a y ha hy => by
    calc a * y < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' ha hy
      _ = 2 ^ 51 := by norm_num
  have q01 := p a0 y1 hw0 hz0; have q10 := p a1 y0 hw1 hz3
  have q02 := p a0 y2 hw0 hz1; have q11 := p a1 y1 hw1 hz0; have q20 := p a2 y0 hw2 hz3
  have q03 := p a0 y3 hw0 hz2; have q12 := p a1 y2 hw1 hz1; have q21 := p a2 y1 hw2 hz0
  have q30 := p a3 y0 hw3 hz3
  generalize hL : a0 * y0 + 2 ^ 64 * (a0 * y1 + a1 * y0) + 2 ^ 128 * (a0 * y2 + a1 * y1 + a2 * y0) = L
  generalize hK : a0 * y3 + a1 * y2 + a2 * y1 + a3 * y0 = K
  have e : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) * (y0 + 2 ^ 64 * (y1 + 2 ^ 64 * y2 +
      2 ^ 128 * y3)) = (L + 2 ^ 192 * K) + 2 ^ 256 * (a1 * y3 + a2 * y2 + a3 * y1 +
        2 ^ 64 * (a2 * y3 + a3 * y2) + 2 ^ 128 * (a3 * y3)) := by
    rw [← hL, ← hK]; ring
  have hLlt : L < 2 ^ 192 := by rw [← hL]; norm_num at m00 q01 q10 q02 q11 q20 ⊢; omega
  have hKlt : K < 2 ^ 64 := by rw [← hK]; norm_num at q03 q12 q21 q30 ⊢; omega
  have hlt : L + 2 ^ 192 * K < 2 ^ 256 := by norm_num at hLlt hKlt ⊢; omega
  rw [show y0 + 2 ^ 64 * (y1 + 2 ^ 64 * y2 + 2 ^ 128 * y3) = y0 + 2 ^ 64 * (y1 + 2 ^ 64 * y2 + 2 ^ 128 * y3)
    from rfl, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
    show M64 * 2 ^ 192 = 2 ^ 256 - 2 ^ 192 by unfold M64; norm_num, s5_and_high hlt (by norm_num)]
  congr 1
  norm_num at hLlt ⊢
  omega

/-- Adding a lane-3 term to a packed word. -/
theorem s5_acc7 (v : Nat → Nat) (K : Nat) (hv : ∀ j, j < 4 → v j + (if j = 3 then K else 0) < 2 ^ 64) :
    (pack4 v + 2 ^ 192 * K) % 2 ^ 256 = pack4 fun j => v j + if j = 3 then K else 0 := by
  have e : pack4 v + 2 ^ 192 * K = pack4 fun j => v j + if j = 3 then K else 0 := by
    unfold pack4
    simp only [show (0 : Nat) ≠ 3 by decide, show (1 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 3 by decide,
      if_false, if_true, Nat.add_zero]
    ring
  rw [e, Nat.mod_eq_of_lt (pack4_lt hv)]

/-! ## `AccAt` -/

theorem s5_sum_range7 (f : Nat → Int) :
    ((List.range 7).map f).sum = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [List.range_succ]; ring

/-- `AccAt` from the exact lane sums over all seven columns. -/
theorem s5_accAt_of {cd m m' : ByteArray} (hzh : ZHatAt m cd)
    (hfin : okA cd = true → ∀ g, g < 2 → ∀ t, t < 256 →
      word m' (ACC + 0x2000 * g + 32 * t) = pack4 fun j => accSum cd m (4 * g + j) t 7) :
    AccAt m' cd := by
  intro hok
  have hle : ∀ r t, t < 256 → accSum cd m r t 7 ≤ 7 * 2 ^ 51 := fun r t ht =>
    s5_accSum_le ht (fun k hk => (hzh k hk t ht).1) 7 le_rfl
  have hlt : ∀ g t, t < 256 → ∀ j, j < 4 → accSum cd m (4 * g + j) t 7 < 2 ^ 64 := fun g t ht j _ => by
    have := hle (4 * g + j) t ht; omega
  refine ⟨fun g hg k hk t ht => ?_, fun r hr t ht => ?_⟩
  · rw [hfin hok g hg t ht, lane_pack4 (hlt g t ht) hk]
    have := hle (4 * g + k) t ht; omega
  · have ha : accAddr r t = ACC + 0x2000 * (r / 4) + 32 * t := rfl
    rw [ha, hfin hok (r / 4) (by omega) t ht, lane_pack4 (hlt (r / 4) t ht) (Nat.mod_lt _ (by norm_num)),
      show 4 * (r / 4) + r % 4 = r by omega]
    have hnn : ∀ s, s < 7 → (((aD cd r s)[t]!).toNat : Int) = (aD cd r s)[t]! := fun s hs => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (s5_okA_get hok hr hs)
      have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
      rw [hD]
      exact Int.toNat_of_nonneg ((MlDsaOpt87.Proofs.rejNTTPoly_range _ a ha).2 t ht).1
    have hm : ∀ s, s < 7 → (zhLane m s t : Int) % (Fips204.q : Int) =
        (zHat cd s)[t]! % (Fips204.q : Int) := fun s hs =>
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (hzh s hs t ht).2
    have hrow : (azRow cd r)[t]! = ((List.range 7).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum %
        (Fips204.q : Int) := by
      unfold azRow; exact getElem!_map_range 256 t _ ht
    rw [hrow, s5_sum_range7]
    have hsum : (accSum cd m r t 7 : Int) =
        (aD cd r 0)[t]! * (zhLane m 0 t : Int) + (aD cd r 1)[t]! * (zhLane m 1 t : Int) +
        (aD cd r 2)[t]! * (zhLane m 2 t : Int) + (aD cd r 3)[t]! * (zhLane m 3 t : Int) +
        (aD cd r 4)[t]! * (zhLane m 4 t : Int) + (aD cd r 5)[t]! * (zhLane m 5 t : Int) +
        (aD cd r 6)[t]! * (zhLane m 6 t : Int) := by
      rw [← hnn 0 (by omega), ← hnn 1 (by omega), ← hnn 2 (by omega), ← hnn 3 (by omega),
        ← hnn 4 (by omega), ← hnn 5 (by omega), ← hnn 6 (by omega)]
      show ((0 + _ + _ + _ + _ + _ + _ + _ : Nat) : Int) = _
      push_cast; ring
    rw [hsum]
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    exact Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add
      (Int.ModEq.mul_left _ (hm 0 (by omega))) (Int.ModEq.mul_left _ (hm 1 (by omega))))
      (Int.ModEq.mul_left _ (hm 2 (by omega)))) (Int.ModEq.mul_left _ (hm 3 (by omega))))
      (Int.ModEq.mul_left _ (hm 4 (by omega)))) (Int.ModEq.mul_left _ (hm 5 (by omega))))
      (Int.ModEq.mul_left _ (hm 6 (by omega)))

end MlDsaOpt87.Proofs
