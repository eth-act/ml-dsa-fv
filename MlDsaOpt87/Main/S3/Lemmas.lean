import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Group
import MlDsaOpt87.Math
set_option warningAsError true
/-!
# Pure lemmas of the ExpandA group segments (ML-DSA-87, WP S3)

The accumulator step of `group [15, n, rb]` (`AccCols`), its flag, and the
transport of `InvE` / `AccCols` across a `group` call. Mirrors
`MlDsaOpt44/Main/SegGroups.lean` with the two row groups.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

theorem s3_pack4_ite {amask : Nat} {v w : Nat → Nat} (hv : ∀ r, r < 4 → amask.testBit r = true) :
    pack4 (fun r => if amask.testBit r then v r else w r) = pack4 v := by
  unfold pack4
  simp only [hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega), if_true]

theorem s3_aD_lt {cd : ByteArray} {r s : Nat} (h : (aOf cd r s).isSome = true) {t : Nat}
    (ht : t < 256) : ((aD cd r s)[t]!).toNat < 2 ^ 23 := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  have := ((rejNTTPoly_range _ a ha).2 t ht).2
  unfold Fips204.q at this
  omega

/-- The flag of `group [15, s, rb]`. -/
theorem s3_gOk_15 (cd : ByteArray) (s rb : Nat) : gOk cd 15 s rb = okCol cd rb s 4 := by
  simp only [gOk, okCol, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show Nat.testBit 15 0 = true by decide, show Nat.testBit 15 1 = true by decide,
    show Nat.testBit 15 2 = true by decide, show Nat.testBit 15 3 = true by decide,
    Bool.not_true, Bool.false_or]

theorem s3_okUpTo_get {cd : ByteArray} {rb : Nat} :
    ∀ {n : Nat}, okUpTo cd rb 4 n = true → ∀ s, s < n → ∀ r, r < 4 →
      (aOf cd (4 * rb + r) s).isSome = true
  | 0, _, s, hs, _, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, h, s, hs, r, hr => by
    simp only [okUpTo, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact s3_okUpTo_get h.1 s hs r hr
    · have h2 := h.2
      unfold okCol at h2
      rw [List.all_eq_true] at h2
      exact h2 r (List.mem_range.mpr hr)

theorem s3_accSum_le {cd m : ByteArray} {r t : Nat} (ht : t < 256)
    (hz : ∀ k, k < 7 → zhLane m k t < 2 ^ 28) :
    ∀ n, n ≤ 7 → (∀ s, s < n → (aOf cd r s).isSome = true) → accSum cd m r t n ≤ n * 2 ^ 51
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

/-- A zeroed accumulator table holds the empty sums. -/
theorem s3_accCols_zero {cd m : ByteArray} {rb : Nat}
    (hz : ZeroOn m (ACC + 0x2000 * rb) (ACC + 0x2000 * rb + 8192)) : AccCols m cd rb 0 :=
  fun _ t ht => by
    rw [MlDsaOpt44.Proofs.word_zero_of_zeroOn hz (by omega) (by omega)]
    rfl

/-- `AccCols` survives a call that keeps the table and the `ẑ` lanes. -/
theorem s3_accCols_frame {cd m m' : ByteArray} {rb n : Nat} (hacc : AccCols m cd rb n)
    (hw : ∀ t, t < 256 → word m' (ACC + 0x2000 * rb + 32 * t) = word m (ACC + 0x2000 * rb + 32 * t))
    (hzh : ∀ k, k < n → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : AccCols m' cd rb n :=
  fun hok t ht => by
    rw [hw t ht, hacc hok t ht]
    exact congrArg pack4 (funext fun j => (s3_accSum_congr n (fun k hk => hzh k hk t ht)).symm)

/-- `group [15, n, rb]`: column `n` of rows `4 rb … 4 rb + 3` added to table `rb`. -/
theorem s3_accCols_step {cd m m' : ByteArray} {rb n : Nat} (hn : n < 7)
    (hacc : AccCols m cd rb n) (hz : ZHatAt m cd)
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t)
    (hpost : gOk cd 15 n rb = true → ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ACC + 8192 * rb + 32 * t) =
          (word m (ACC + 8192 * rb + 32 * t) +
            pack4 (fun r => if (15 : Nat).testBit r then
                ((aD cd (4 * rb + r) n)[t]!).toNat else junk r t) *
              lane (word m (ZH + 8192 * (n / 4) + 32 * t)) (n % 4)) % 2 ^ 256) :
    AccCols m' cd rb (n + 1) := by
  intro hok t ht
  have hok' := hok
  simp only [okUpTo, Bool.and_eq_true] at hok'
  obtain ⟨junk, -, hw⟩ := hpost (by rw [s3_gOk_15]; exact hok'.2)
  have hA := s3_okUpTo_get hok
  have e2 : lane (word m (ZH + 8192 * (n / 4) + 32 * t)) (n % 4) = zhLane m n t := rfl
  rw [hw t ht, e2, hacc hok'.1 t ht,
    s3_pack4_ite (fun r hr => by interval_cases r <;> decide), MlDsaOpt44.Proofs.pack4_add_mul,
    Nat.mod_eq_of_lt (MlDsaOpt44.Proofs.pack4_lt fun r hr => by
      have := s3_accSum_le ht (fun k hk => (hz k hk t ht).1) (n + 1) (by omega)
        (fun s hs => hA s hs r hr)
      show accSum cd m (4 * rb + r) t (n + 1) < 2 ^ 64
      have h7 : (n + 1) * 2 ^ 51 ≤ 7 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
      omega)]
  exact congrArg pack4
    (funext fun r => (s3_accSum_congr (n + 1) (fun k hk => hzh k (by omega) t ht)).symm)

/-- What every ExpandA boundary keeps survives `group [·, ·, rb]`. -/
theorem s3_invE_frame {cd m m' : ByteArray} {rb : Nat} (hrb : rb < 2) (hI : InvE cd m)
    (hfr : FrameExcept m m' (groupFrame rb)) : InvE cd m' :=
  ⟨RC4Table.frame hI.rc4 hfr (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfr (by unfold groupFrame; avoids_tac),
    TblAt.frame hI.tbl hfr (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfr (by unfold groupFrame; avoids_tac),
    HPAt.frame hI.hp hfr (by unfold groupFrame; avoids_tac),
    CAt.frame hI.c hfr (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac)
      (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfr (by unfold groupFrame; avoids_tac)⟩

end MlDsaOpt87.Proofs
