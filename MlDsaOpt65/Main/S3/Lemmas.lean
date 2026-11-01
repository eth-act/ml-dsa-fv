import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Group
import MlDsaOpt65.Math
set_option warningAsError true
/-!
# Pure lemmas of the ExpandA group segments (ML-DSA-65, WP S3)

Accumulator steps for `group [15, s, 0]` (`AccCols0`) and `group [3, 4, 1]`
(`AccCols1`), the flags of the two call shapes, and `AccAt` / `SibFresh` at the
end of the ExpandA phase (`Inv5`). Mirrors `MlDsaOpt44/Main/SegGroups.lean` and
`MlDsaOpt44/Main/SegG234/Proof.lean` (`accAt_of`) with the two row groups.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-! ## Lanes -/

theorem s3_pack4_lane {w : Nat} (hw : w < 2 ^ 256) : pack4 (fun j => lane w j) = w := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.reducePow]
  omega

theorem s3_pack4_ite {amask : Nat} {v w : Nat → Nat} (hv : ∀ r, r < 4 → amask.testBit r = true) :
    pack4 (fun r => if amask.testBit r then v r else w r) = pack4 v := by
  unfold pack4
  simp only [hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega), if_true]

/-! ## Matrix entries and flags -/

theorem s3_aD_lt {cd : ByteArray} {r s : Nat} (h : (aOf cd r s).isSome = true) {t : Nat}
    (ht : t < 256) : ((aD cd r s)[t]!).toNat < 2 ^ 23 := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  have := ((rejNTTPoly_range _ a ha).2 t ht).2
  unfold Fips204.q at this
  omega

theorem s3_aD_cast {cd : ByteArray} {r s : Nat} (h : (aOf cd r s).isSome = true) {t : Nat}
    (ht : t < 256) : (((aD cd r s)[t]!).toNat : Int) = (aD cd r s)[t]! := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  exact Int.toNat_of_nonneg ((rejNTTPoly_range _ a ha).2 t ht).1

theorem s3_gOk_g0 (cd : ByteArray) (s : Nat) : gOk cd 15 s 0 = okCol0 cd s := by
  simp only [gOk, okCol0, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show Nat.testBit 15 0 = true by decide, show Nat.testBit 15 1 = true by decide,
    show Nat.testBit 15 2 = true by decide, show Nat.testBit 15 3 = true by decide,
    Bool.not_true, Bool.false_or, Bool.and_true, Nat.mul_zero, Nat.zero_add, Bool.and_assoc]

theorem s3_gOk_g9 (cd : ByteArray) : gOk cd 3 4 1 = okCol1 cd 4 := by
  simp only [gOk, okCol1, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show Nat.testBit 3 0 = true by decide, show Nat.testBit 3 1 = true by decide,
    show Nat.testBit 3 2 = false by decide, show Nat.testBit 3 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, Nat.mul_one,
    Nat.add_zero]

theorem s3_okUpTo0_get {cd : ByteArray} :
    ∀ {n : Nat}, okUpTo0 cd n = true → ∀ s, s < n → ∀ r, r < 4 → (aOf cd r s).isSome = true
  | 0, _, s, hs, _, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, h, s, hs, r, hr => by
    simp only [okUpTo0, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact s3_okUpTo0_get h.1 s hs r hr
    · have h2 := h.2
      simp only [okCol0, Bool.and_eq_true] at h2
      interval_cases r
      · exact h2.1.1.1
      · exact h2.1.1.2
      · exact h2.1.2
      · exact h2.2

theorem s3_okUpTo1_get {cd : ByteArray} :
    ∀ {n : Nat}, okUpTo1 cd n = true → ∀ s, s < n → ∀ j, j < 2 → (aOf cd (4 + j) s).isSome = true
  | 0, _, s, hs, _, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, h, s, hs, j, hj => by
    simp only [okUpTo1, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact s3_okUpTo1_get h.1 s hs j hj
    · have h2 := h.2
      simp only [okCol1, Bool.and_eq_true] at h2
      interval_cases j
      · exact h2.1
      · exact h2.2

theorem s3_okA_get {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 6) (hs : s < 5) :
    (aOf cd r s).isSome = true := by
  unfold okA at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at this
  exact this s (List.mem_range.mpr hs)

theorem s3_okUpTo0_of_okA {cd : ByteArray} (h : okA cd = true) : ∀ n, n ≤ 5 → okUpTo0 cd n = true
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [okUpTo0, okCol0, Bool.and_eq_true]
    exact ⟨s3_okUpTo0_of_okA h n (by omega),
      ⟨⟨s3_okA_get h (by omega) (by omega), s3_okA_get h (by omega) (by omega)⟩,
        s3_okA_get h (by omega) (by omega)⟩, s3_okA_get h (by omega) (by omega)⟩

theorem s3_okUpTo1_of_okA {cd : ByteArray} (h : okA cd = true) : ∀ n, n ≤ 5 → okUpTo1 cd n = true
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [okUpTo1, okCol1, Bool.and_eq_true]
    exact ⟨s3_okUpTo1_of_okA h n (by omega), s3_okA_get h (by omega) (by omega),
      s3_okA_get h (by omega) (by omega)⟩

/-! ## Accumulator sums -/

theorem s3_accSum_le {cd m : ByteArray} {r t : Nat} (ht : t < 256)
    (hz : ∀ k, k < 5 → zhLane m k t < 2 ^ 28) :
    ∀ n, n ≤ 5 → (∀ s, s < n → (aOf cd r s).isSome = true) → accSum cd m r t n ≤ n * 2 ^ 51
  | 0, _, _ => Nat.le_refl _
  | n + 1, hn, ha => by
    have ih := s3_accSum_le ht hz n (by omega) (fun s hs => ha s (by omega))
    have h1 := s3_aD_lt (ha n (by omega)) ht
    have h2 := hz n (by omega)
    have h3 : ((aD cd r n)[t]!).toNat * zhLane m n t < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' h1 h2
    have e : (n + 1) * 2 ^ 51 = n * 2 ^ 51 + 2 ^ 51 := by ring
    show accSum cd m r t n + _ ≤ _
    omega

theorem s3_accSum_congr {cd m m' : ByteArray} {r t : Nat} :
    ∀ n, (∀ k, k < n → zhLane m' k t = zhLane m k t) → accSum cd m' r t n = accSum cd m r t n
  | 0, _ => rfl
  | n + 1, h => by
    show accSum cd m' r t n + _ * zhLane m' n t = accSum cd m r t n + _ * zhLane m n t
    rw [s3_accSum_congr n (fun k hk => h k (by omega)), h n (by omega)]

/-- `accSum` is the row sum of `A ∘ ẑ` modulo `q`. -/
theorem s3_accSum_mod {cd m : ByteArray} {r t : Nat} (ht : t < 256) (hz : ZHatAt m cd) :
    ∀ n, n ≤ 5 → (∀ s, s < n → (aOf cd r s).isSome = true) →
      (Fips204.q : Int) ∣ ((accSum cd m r t n : Nat) : Int) -
        ((List.range n).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum
  | 0, _, _ => by simp [accSum]
  | n + 1, hn, ha => by
    have ih := s3_accSum_mod ht hz n (by omega) (fun s hs => ha s (by omega))
    have hzn : (Fips204.q : Int) ∣ (zhLane m n t : Int) - (zHat cd n)[t]! :=
      Int.dvd_of_emod_eq_zero (hz n (by omega) t ht).2
    have hc := s3_aD_cast (ha n (by omega)) ht
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have e : ((accSum cd m r t (n + 1) : Nat) : Int) =
        (accSum cd m r t n : Int) + (((aD cd r n)[t]!).toNat : Int) * (zhLane m n t : Int) := by
      show ((accSum cd m r t n + _ * _ : Nat) : Int) = _
      push_cast; ring
    rw [e, hc]
    have e2 : (accSum cd m r t n : Int) + (aD cd r n)[t]! * (zhLane m n t : Int) -
        (((List.range n).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum +
          (aD cd r n)[t]! * (zHat cd n)[t]!) =
        ((accSum cd m r t n : Int) -
          ((List.range n).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum) +
        (aD cd r n)[t]! * ((zhLane m n t : Int) - (zHat cd n)[t]!) := by ring
    rw [e2]
    exact dvd_add ih (Dvd.dvd.mul_left hzn _)

/-! ## Accumulator steps -/

/-- `group [15, n, 0]`: column `n` of rows `0 … 3` added to `ACC`. -/
theorem s3_accCols0_step {cd m m' : ByteArray} {n : Nat} (hn : n < 5)
    (hacc : AccCols0 m cd n) (hz : ZHatAt m cd)
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t)
    (hpost : gOk cd 15 n 0 = true → ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ACC + 8192 * 0 + 32 * t) =
          (word m (ACC + 8192 * 0 + 32 * t) +
            pack4 (fun r => if (15 : Nat).testBit r then
                ((aD cd (4 * 0 + r) n)[t]!).toNat else junk r t) *
              lane (word m (ZH + 8192 * (n / 4) + 32 * t)) (n % 4)) % 2 ^ 256) :
    AccCols0 m' cd (n + 1) := by
  intro hok t ht
  have hok' := hok
  simp only [okUpTo0, Bool.and_eq_true] at hok'
  obtain ⟨junk, -, hw⟩ := hpost (by rw [s3_gOk_g0]; exact hok'.2)
  have hA := s3_okUpTo0_get hok
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hw
  have e2 : lane (word m (ZH + 8192 * (n / 4) + 32 * t)) (n % 4) = zhLane m n t := rfl
  rw [hw t ht, e2, hacc hok'.1 t ht,
    s3_pack4_ite (fun r hr => by interval_cases r <;> decide), MlDsaOpt44.Proofs.pack4_add_mul,
    Nat.mod_eq_of_lt (MlDsaOpt44.Proofs.pack4_lt fun r hr => by
      have := s3_accSum_le ht (fun k hk => (hz k hk t ht).1) (n + 1) (by omega)
        (fun s hs => hA s hs r hr)
      show accSum cd m r t (n + 1) < 2 ^ 64
      have h5 : (n + 1) * 2 ^ 51 ≤ 5 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
      omega)]
  exact congrArg pack4
    (funext fun r => (s3_accSum_congr (n + 1) (fun k hk => hzh k (by omega) t ht)).symm)

/-- `group [3, 4, 1]`: column `4` of rows `4, 5` added to lanes 0, 1 of `ACC + 0x2000`;
lanes 2, 3 gain a 23-bit candidate times `ẑ_4`. -/
theorem s3_accCols1_step {cd m m' : ByteArray}
    (hacc : AccCols1 m cd 4) (hz : ZHatAt m cd)
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t)
    (hpost : gOk cd 3 4 1 = true → ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ACC + 8192 * 1 + 32 * t) =
          (word m (ACC + 8192 * 1 + 32 * t) +
            pack4 (fun r => if (3 : Nat).testBit r then
                ((aD cd (4 * 1 + r) 4)[t]!).toNat else junk r t) *
              lane (word m (ZH + 8192 * (4 / 4) + 32 * t)) (4 % 4)) % 2 ^ 256) :
    AccCols1 m' cd 5 := by
  intro hok t ht
  have hok' : okUpTo1 cd 4 = true ∧ okCol1 cd 4 = true := by
    rw [← Bool.and_eq_true]; exact hok
  obtain ⟨junk, hj, hw⟩ := hpost (by rw [s3_gOk_g9]; exact hok'.2)
  have hA := s3_okUpTo1_get hok
  have hz4 : lane (word m (ZH + 8192 * (4 / 4) + 32 * t)) (4 % 4) = zhLane m 4 t := rfl
  have hw := hw t ht
  rw [hz4] at hw
  simp only [Nat.mul_one] at hw
  have hW := s3_pack4_lane (word_lt m (ACC + 0x2000 + 32 * t))
  obtain ⟨hl01, hl23⟩ := hacc hok'.1 t ht
  have hzl := (hz 4 (by omega) t ht).1
  -- the added lanes
  set X : Nat → Nat := fun r => if (3 : Nat).testBit r then ((aD cd (4 + r) 4)[t]!).toNat
    else junk r t with hX
  have hXlt : ∀ r, r < 4 → X r < 2 ^ 23 := fun r hr => by
    simp only [hX]
    split
    · interval_cases r
      · exact s3_aD_lt (hA 4 (by omega) 0 (by omega)) ht
      · exact s3_aD_lt (hA 4 (by omega) 1 (by omega)) ht
      · exact absurd ‹_› (by decide)
      · exact absurd ‹_› (by decide)
    · exact hj r t
  have hLle : ∀ j, j < 4 → lane (word m (ACC + 0x2000 + 32 * t)) j ≤ 4 * 2 ^ 51 := fun j hj' => by
    by_cases h2 : j < 2
    · rw [hl01 j h2]
      exact s3_accSum_le ht (fun k hk => (hz k hk t ht).1) 4 (by omega)
        (fun s hs => hA s (by omega) j h2)
    · exact hl23 j (by omega) hj'
  have hvlt : ∀ r, r < 4 →
      lane (word m (ACC + 0x2000 + 32 * t)) r + X r * zhLane m 4 t < 2 ^ 64 := fun r hr => by
    have h1 := hLle r hr
    have h2 : X r * zhLane m 4 t < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' (hXlt r hr) hzl
    omega
  have hw' : word m' (ACC + 0x2000 + 32 * t) =
      pack4 fun r => lane (word m (ACC + 0x2000 + 32 * t)) r + X r * zhLane m 4 t := by
    rw [hw]
    conv => lhs; rw [← hW]
    rw [MlDsaOpt44.Proofs.pack4_add_mul, Nat.mod_eq_of_lt (MlDsaOpt44.Proofs.pack4_lt hvlt)]
  rw [hw']
  refine ⟨fun j hj2 => ?_, fun j hj2 hj4 => ?_⟩
  · rw [MlDsaOpt44.Proofs.lane_pack4 hvlt (by omega), hl01 j hj2,
      s3_accSum_congr 5 (fun k hk => hzh k hk t ht)]
    have hb : (3 : Nat).testBit j = true := by interval_cases j <;> decide
    simp only [hX, hb, if_true]
    rfl
  · rw [MlDsaOpt44.Proofs.lane_pack4 hvlt hj4]
    have h1 := hl23 j hj2 hj4
    have h2 : X j * zhLane m 4 t < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' (hXlt j hj4) hzl
    omega

/-! ## End of ExpandA -/

theorem s3_accAt {cd m : ByteArray} (hz : ZHatAt m cd) (h0 : AccCols0 m cd 5)
    (h1 : AccCols1 m cd 5) : AccAt m cd := by
  intro hok
  have hu0 := s3_okUpTo0_of_okA hok 5 le_rfl
  have hu1 := s3_okUpTo1_of_okA hok 5 le_rfl
  have hle : ∀ r, r < 6 → ∀ t, t < 256 → accSum cd m r t 5 ≤ 5 * 2 ^ 51 := fun r hr t ht =>
    s3_accSum_le ht (fun k hk => (hz k hk t ht).1) 5 le_rfl
      (fun s hs => s3_okA_get hok hr hs)
  have hlt0 : ∀ t, t < 256 → ∀ r, r < 4 → accSum cd m r t 5 < 2 ^ 64 := fun t ht r hr => by
    have := hle r (by omega) t ht; omega
  -- every lane of row `r` is `accSum`
  have hlane : ∀ r, r < 6 → ∀ t, t < 256 →
      lane (word m (accAddr r t)) (r % 4) = accSum cd m r t 5 := by
    intro r hr t ht
    by_cases h4 : r < 4
    · have ea : accAddr r t = ACC + 32 * t := by
        unfold accAddr; rw [Nat.div_eq_of_lt h4]; omega
      rw [ea, h0 hu0 t ht, Nat.mod_eq_of_lt h4, MlDsaOpt44.Proofs.lane_pack4 (hlt0 t ht) h4]
    · have ea : accAddr r t = ACC + 0x2000 + 32 * t := by
        unfold accAddr; rw [show r / 4 = 1 by omega]
      have hj := ((h1 hu1 t ht).1 (r % 4) (by omega))
      rw [ea, hj, show 4 + r % 4 = r by omega]
  refine ⟨fun g hg k hk t ht => ?_, fun r hr t ht => ?_⟩
  · interval_cases g
    · rw [show ACC + 0x2000 * 0 + 32 * t = ACC + 32 * t by omega, h0 hu0 t ht,
        MlDsaOpt44.Proofs.lane_pack4 (hlt0 t ht) hk]
      have := hle k (by omega) t ht; omega
    · rw [show ACC + 0x2000 * 1 + 32 * t = ACC + 0x2000 + 32 * t by omega]
      by_cases h2 : k < 2
      · rw [(h1 hu1 t ht).1 k h2]
        have := hle (4 + k) (by omega) t ht; omega
      · have := (h1 hu1 t ht).2 k (by omega) hk; omega
  · rw [hlane r hr t ht]
    have hrow : (azRow cd r)[t]! =
        ((List.range 5).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum % (Fips204.q : Int) := by
      unfold azRow; exact MlDsaOpt44.Proofs.getElem!_map_range 256 t _ ht
    rw [hrow]
    apply Int.emod_eq_zero_of_dvd
    have hd := s3_accSum_mod (r := r) ht hz 5 le_rfl (fun s hs => s3_okA_get hok hr hs)
    generalize ((List.range 5).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum = S at hd ⊢
    rw [Int.emod_def]
    have e : ((accSum cd m r t 5 : Nat) : Int) - (S - (Fips204.q : Int) * (S / (Fips204.q : Int))) =
        (((accSum cd m r t 5 : Nat) : Int) - S) + (Fips204.q : Int) * (S / (Fips204.q : Int)) := by
      ring
    rw [e]
    exact dvd_add hd (dvd_mul_right _ _)

end MlDsaOpt65.Proofs
