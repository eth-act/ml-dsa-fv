import MlDsaOpt44.Main.SegG234.G3
import MlDsaOpt44.Main.SegG234.G4
import MlDsaOpt44.Main.SegGroups
set_option warningAsError true
/-!
# `seg_g234`: composition of the three mixed groups

`ACC` after the groups is `pack4 (accSum · 4)` (columns 2 and 3 added row-wise
by `pass3m`, `A[3][2] ẑ_2 + A[3][3] ẑ_3` by the Kronecker lane), which is `Â ẑ`
modulo `q`; `TRL`, `CB`, `MU` come from the riders.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem okA_get {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 4) (hs : s < 4) :
    (aOf cd r s).isSome = true := by
  unfold okA at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at this
  exact this s (List.mem_range.mpr hs)

theorem okCol_of_okA {cd : ByteArray} (h : okA cd = true) {s : Nat} (hs : s < 4) : okCol cd s = true := by
  unfold okCol
  rw [List.all_eq_true]
  intro r hr
  exact okA_get h (List.mem_range.mp hr) hs

theorem okUpTo_of_okA {cd : ByteArray} (h : okA cd = true) : ∀ n, n ≤ 4 → okUpTo cd n = true
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [okUpTo, Bool.and_eq_true]
    exact ⟨okUpTo_of_okA h n (by omega), okCol_of_okA h (by omega)⟩

theorem sum_range4 (f : Nat → Int) : ((List.range 4).map f).sum = f 0 + f 1 + f 2 + f 3 := by
  simp [List.range_succ]; ring

theorem ite_mul_le (p : Prop) [Decidable p] (a z : Nat) : (if p then a else 0) * z ≤ a * z := by
  split <;> simp

/-- `ACC` after the three groups, from `AccCols 2`. -/
theorem acc_final {cd m : ByteArray} {t : Nat} (ht : t < 256) (hok : okA cd = true)
    (hz : ∀ k, k < 4 → lane (word m (ZH + 32 * t)) k < 2 ^ 28)
    (h0 : word m (ACC + 32 * t) = pack4 fun r => accSum cd m r t 2) :
    ((((word m (ACC + 32 * t) +
        pack4 (fun r => if r < 3 then ((aD cd r 2)[t]!).toNat else 0) * lane (word m (ZH + 32 * t)) 2) %
          2 ^ 256 +
        pack4 (fun r => if r < 3 then ((aD cd r 3)[t]!).toNat else 0) * lane (word m (ZH + 32 * t)) 3) %
          2 ^ 256 +
        2 ^ 192 * (((aD cd 3 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 +
          ((aD cd 3 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2)) % 2 ^ 256) =
      pack4 fun r => accSum cd m r t 4 := by
  have hle : ∀ r, r < 4 → accSum cd m r t 4 < 2 ^ 64 := fun r hr => by
    have := accSum_le ht hz hr 4 le_rfl (okUpTo_of_okA hok 4 le_rfl)
    omega
  have e4 : ∀ r, accSum cd m r t 4 = accSum cd m r t 2 + ((aD cd r 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2 +
      ((aD cd r 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 := fun r => rfl
  generalize hz2 : lane (word m (ZH + 32 * t)) 2 = z2 at e4 ⊢
  generalize hz3 : lane (word m (ZH + 32 * t)) 3 = z3 at e4 ⊢
  have s1 := pack4_add_mul (fun r => accSum cd m r t 2)
    (fun r => if r < 3 then ((aD cd r 2)[t]!).toNat else 0) z2
  have b1 : (pack4 fun r => accSum cd m r t 2 + (if r < 3 then ((aD cd r 2)[t]!).toNat else 0) * z2) <
      2 ^ 256 := pack4_lt fun r hr => by
    have := hle r hr; rw [e4] at this
    have h1 := ite_mul_le (r < 3) ((aD cd r 2)[t]!).toNat z2
    omega
  rw [h0, s1, Nat.mod_eq_of_lt b1]
  have s2 := pack4_add_mul
    (fun r => accSum cd m r t 2 + (if r < 3 then ((aD cd r 2)[t]!).toNat else 0) * z2)
    (fun r => if r < 3 then ((aD cd r 3)[t]!).toNat else 0) z3
  have b2 : (pack4 fun r => accSum cd m r t 2 + (if r < 3 then ((aD cd r 2)[t]!).toNat else 0) * z2 +
      (if r < 3 then ((aD cd r 3)[t]!).toNat else 0) * z3) < 2 ^ 256 := pack4_lt fun r hr => by
    have := hle r hr; rw [e4] at this
    have h1 := ite_mul_le (r < 3) ((aD cd r 2)[t]!).toNat z2
    have h2 := ite_mul_le (r < 3) ((aD cd r 3)[t]!).toNat z3
    omega
  rw [s2, Nat.mod_eq_of_lt b2]
  have e : ∀ (v : Nat → Nat) (K : Nat), pack4 v + 2 ^ 192 * K = pack4 fun r => v r + if r = 3 then K else 0 := by
    intro v K; unfold pack4
    simp only [show (0 : Nat) ≠ 3 by decide, show (1 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 3 by decide,
      if_false, if_true, Nat.add_zero]
    ring
  rw [e]
  have hv : ∀ r, r < 4 → (accSum cd m r t 2 + (if r < 3 then ((aD cd r 2)[t]!).toNat else 0) * z2 +
      (if r < 3 then ((aD cd r 3)[t]!).toNat else 0) * z3 + if r = 3 then ((aD cd 3 3)[t]!).toNat * z3 +
        ((aD cd 3 2)[t]!).toNat * z2 else 0) = accSum cd m r t 4 := by
    intro r hr
    rw [e4]
    by_cases h3 : r < 3
    · rw [if_pos h3, if_pos h3, if_neg (by omega), Nat.add_zero]
    · have : r = 3 := by omega
      subst this
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, Nat.zero_mul, Nat.add_zero, Nat.zero_mul,
        Nat.add_zero]
      omega
  rw [pack4_congr hv, Nat.mod_eq_of_lt (pack4_lt hle)]

/-- `AccAt` from the exact lane sums over all four columns. -/
theorem accAt_of {cd m m' : ByteArray} (hzh : ZHatAt m cd)
    (hfin : okA cd = true → ∀ t, t < 256 → word m' (ACC + 32 * t) = pack4 fun r => accSum cd m r t 4) :
    AccAt m' cd := by
  intro hok r hr t ht
  have hz : ∀ k, k < 4 → lane (word m (ZH + 32 * t)) k < 2 ^ 28 := fun k hk => (hzh k hk t ht).1
  have hle : ∀ r, r < 4 → accSum cd m r t 4 ≤ 4 * 2 ^ 51 := fun r hr =>
    accSum_le ht hz hr 4 le_rfl (okUpTo_of_okA hok 4 le_rfl)
  rw [hfin hok t ht, lane_pack4 (fun r hr => by have := hle r hr; omega) hr]
  refine ⟨by have := hle r hr; omega, ?_⟩
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
  have hsum : (accSum cd m r t 4 : Int) =
      (aD cd r 0)[t]! * (lane (word m (ZH + 32 * t)) 0 : Int) +
      (aD cd r 1)[t]! * (lane (word m (ZH + 32 * t)) 1 : Int) +
      (aD cd r 2)[t]! * (lane (word m (ZH + 32 * t)) 2 : Int) +
      (aD cd r 3)[t]! * (lane (word m (ZH + 32 * t)) 3 : Int) := by
    rw [← hnn 0 (by omega), ← hnn 1 (by omega), ← hnn 2 (by omega), ← hnn 3 (by omega)]
    show ((0 + _ + _ + _ + _ : Nat) : Int) = _
    push_cast; ring
  rw [hsum]
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  have m0 := hm 0 (by omega)
  have m1 := hm 1 (by omega)
  have m2 := hm 2 (by omega)
  have m3 := hm 3 (by omega)
  exact Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.mul_left _ m0) (Int.ModEq.mul_left _ m1))
    (Int.ModEq.mul_left _ m2)) (Int.ModEq.mul_left _ m3)

theorem g234_flag (cd : ByteArray) (b : Bool) :
    (b && rows3 cd 2 && rows3 cd 3 && ((aOf cd 3 3).isSome && (aOf cd 3 2).isSome)) =
      (b && (okCol cd 2 && okCol cd 3)) := by
  simp only [rows3, okCol, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    Bool.and_true]
  generalize (aOf cd 0 2).isSome = a02
  generalize (aOf cd 1 2).isSome = a12
  generalize (aOf cd 2 2).isSome = a22
  generalize (aOf cd 3 2).isSome = a32
  generalize (aOf cd 0 3).isSome = a03
  generalize (aOf cd 1 3).isSome = a13
  generalize (aOf cd 2 3).isSome = a23
  generalize (aOf cd 3 3).isSome = a33
  revert a02 a12 a22 a32 a03 a13 a23 a33 b
  decide

theorem seg_g234_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvG s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', Inv5 s.executionEnv.calldata m' ∧
      Reach (callState s 3466 [flag b] m)
        (callState s 4648
          [flag (b && (okCol s.executionEnv.calldata 2 && okCol s.executionEnv.calldata 3))] m')
        Gas.pG234 := by
  obtain ⟨m2, hks2, hrc2, hacc2, hf2, hR2⟩ := seg_g2 hs hcd hI.rc4 hI.rho b
  have hrho2 := hI.rho.frame hf2 (by unfold groupFrame; frame_tac)
  obtain ⟨m3, htrl3, hrc3, hacc3, hf3, hR3⟩ := seg_g3 hs hcd hrc2 hrho2 hks2
    (b && rows3 s.executionEnv.calldata 2)
  have hrho3 := hrho2.frame hf3 (by unfold groupFrame; frame_tac)
  have hf23 := FrameExcept.trans hf2 hf3
  have hzh3 : ∀ t, t < 256 → word m3 (ZH + 32 * t) = word m (ZH + 32 * t) := fun t ht =>
    word_frame hf23 (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by unfold groupFrame; frame_tac)
      (by omega) (by omega)
  have hz : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ZH + 32 * t)) k < 2 ^ 28 :=
    fun k hk t ht => (hI.zhat k hk t ht).1
  obtain ⟨m4, hcb, hmu, hacc4, hf4, hR4⟩ := seg_g4 hs hcd hrc3 hrho3 htrl3
    (fun k hk t ht => by rw [hzh3 t ht]; exact hz k hk t ht)
    (b && rows3 s.executionEnv.calldata 2 && rows3 s.executionEnv.calldata 3)
  have hfA := FrameExcept.trans hf23 hf4
  have hR := (hR2.trans hR3).trans hR4
  rw [g234_flag] at hR
  refine ⟨m4, ⟨hI.rc1.frame hfA (by unfold groupFrame; frame_tac),
    hI.tbl.frame hfA (by unfold groupFrame; frame_tac), hI.hp.frame hfA (by unfold groupFrame; frame_tac),
    accAt_of hI.zhat fun hok t ht => ?_,
    fun x hx => by
      rw [word_frame hf4 (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by unfold groupFrame; frame_tac)
        (by omega) (by omega)]
      exact htrl3 x hx,
    hmu, hcb,
    ⟨(hI.zCw.mono le_rfl (by unfold CW ABUF; omega)).frame hfA (by unfold groupFrame; frame_tac),
      (hI.zIdx.mono le_rfl (by unfold IDX ACC; omega)).frame hfA (by unfold groupFrame; frame_tac),
      (hI.zMisc.mono (by unfold NNEG MISC; omega) (by unfold NNEG MISC; omega)).frame hfA
        (by unfold groupFrame; frame_tac)⟩⟩,
    hR.mono (by unfold costG2 costG3 costG4 Gas.pG234; omega)⟩
  -- ACC
  have hzh2 : word m2 (ZH + 32 * t) = word m (ZH + 32 * t) :=
    word_frame hf2 (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by unfold groupFrame; frame_tac)
      (by omega) (by omega)
  have hr2 : rows3 s.executionEnv.calldata 2 = true := by
    simp only [rows3, Bool.and_eq_true]
    exact ⟨⟨okA_get hok (by omega) (by omega), okA_get hok (by omega) (by omega)⟩,
      okA_get hok (by omega) (by omega)⟩
  have hr3 : rows3 s.executionEnv.calldata 3 = true := by
    simp only [rows3, Bool.and_eq_true]
    exact ⟨⟨okA_get hok (by omega) (by omega), okA_get hok (by omega) (by omega)⟩,
      okA_get hok (by omega) (by omega)⟩
  have h4 : ((aOf s.executionEnv.calldata 3 3).isSome && (aOf s.executionEnv.calldata 3 2).isSome) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨okA_get hok (by omega) (by omega), okA_get hok (by omega) (by omega)⟩
  rw [hacc4 h4 t ht, hacc3 hr3 t ht, acc3, hacc2 hr2 t ht, acc3, hzh3 t ht, hzh2]
  exact acc_final ht hok (fun k hk => hz k hk t ht) (hI.acc (okUpTo_of_okA hok 2 (by omega)) t ht)

end MlDsaOpt44.Proofs
