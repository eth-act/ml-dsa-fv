import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Group
set_option warningAsError true
/-! # Segment `3439 … 3466`: the two pure ExpandA groups (`group`, columns 0 and 1). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem aD_lt {cd : ByteArray} {s : Nat} (h : okCol cd s = true) {r : Nat} (hr : r < 4) {t : Nat}
    (ht : t < 256) : ((aD cd r s)[t]!).toNat < Fips204.q := by
  unfold okCol at h
  rw [List.all_eq_true] at h
  have hsome := h r (List.mem_range.mpr hr)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  obtain ⟨-, hrange⟩ := rejNTTPoly_range _ a ha
  have := hrange t ht
  omega

theorem group_glue {s : State} (hs : Ctx s) {m : ByteArray} {b : Bool} {col : Nat}
    {pc ret : Nat} (cost : Nat)
    (hblk : Reach (callState s pc [flag b] m) (callState s 13659 [wd 15, wd col, wd 0, wd ret, flag b] m)
      cost)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) (hcol : col < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (okCol s.executionEnv.calldata col = true →
        ∀ t, t < 256 → word m' (ACC + 32 * t) =
          (word m (ACC + 32 * t) +
            pack4 (fun r => ((aD s.executionEnv.calldata r col)[t]!).toNat) *
              lane (word m (ZH + 32 * t)) col) % 2 ^ 256) ∧
      FrameExcept m m' groupFrame ∧
      Reach (callState s pc [flag b] m)
        (callState s ret [flag (okCol s.executionEnv.calldata col), flag b] m') (cost + Gas.group) := by
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := ret) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hret) m hrc hrho hcol hcd
  exact ⟨m', hpost, hfr, hblk.trans hc⟩

theorem accSum_congr {cd m m' : ByteArray} {t : Nat}
    (hzh : word m' (ZH + 32 * t) = word m (ZH + 32 * t)) (r : Nat) :
    ∀ n, accSum cd m' r t n = accSum cd m r t n
  | 0 => rfl
  | n + 1 => by
    show accSum cd m' r t n + _ * lane (word m' (ZH + 32 * t)) n =
      accSum cd m r t n + _ * lane (word m (ZH + 32 * t)) n
    rw [accSum_congr hzh r n, hzh]

theorem accSum_le {cd m : ByteArray} {t : Nat} (ht : t < 256)
    (hz : ∀ k, k < 4 → lane (word m (ZH + 32 * t)) k < 2 ^ 28) {r : Nat} (hr : r < 4) :
    ∀ n, n ≤ 4 → okUpTo cd n = true → accSum cd m r t n ≤ n * 2 ^ 51
  | 0, _, _ => Nat.le_refl _
  | n + 1, hn, hok => by
    simp only [okUpTo, Bool.and_eq_true] at hok
    have ih := accSum_le ht hz hr n (by omega) hok.1
    have h1 := aD_lt hok.2 hr ht
    have h2 := hz n (by omega)
    have h3 : ((aD cd r n)[t]!).toNat * lane (word m (ZH + 32 * t)) n < 2 ^ 23 * 2 ^ 28 :=
      Nat.mul_lt_mul'' (by unfold Fips204.q at h1; omega) h2
    have e : (n + 1) * 2 ^ 51 = n * 2 ^ 51 + 2 ^ 51 := by ring
    show accSum cd m r t n + _ ≤ _
    omega

/-- One more column: `ACC[t] += A[·][n][t] · ẑ_n[t]`. -/
theorem accCols_step {m m' : ByteArray} {cd : ByteArray} {n : Nat} (hn : n < 4)
    (hacc : AccCols m cd n) (hz : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ZH + 32 * t)) k < 2 ^ 28)
    (hzh : ∀ t, t < 256 → word m' (ZH + 32 * t) = word m (ZH + 32 * t))
    (hpost : okCol cd n = true → ∀ t, t < 256 → word m' (ACC + 32 * t) =
      (word m (ACC + 32 * t) + pack4 (fun r => ((aD cd r n)[t]!).toNat) *
        lane (word m (ZH + 32 * t)) n) % 2 ^ 256) :
    AccCols m' cd (n + 1) := by
  intro hok t ht
  have hok' := hok
  simp only [okUpTo, Bool.and_eq_true] at hok'
  rw [hpost hok'.2 t ht, hacc hok'.1 t ht, pack4_add_mul]
  rw [Nat.mod_eq_of_lt (pack4_lt fun r hr => by
    have := accSum_le ht (fun k hk => hz k hk t ht) hr (n + 1) (by omega) hok
    show accSum cd m r t n + _ < _
    have h' : (n + 1) * 2 ^ 51 < 2 ^ 64 := by
      have : n + 1 ≤ 4 := by omega
      calc (n + 1) * 2 ^ 51 ≤ 4 * 2 ^ 51 := Nat.mul_le_mul_right _ this
        _ < 2 ^ 64 := by norm_num
    exact Nat.lt_of_le_of_lt this h')]
  exact congrArg pack4 (funext fun r => (accSum_congr (hzh t ht) r (n + 1)).symm)

theorem seg_g0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3439 [flag b] m)
        (callState s 3452 [flag (b && okCol s.executionEnv.calldata 0)] m') Gas.pG0 := by
  have hb1 : Reach (callState s 3439 [flag b] m) (callState s 13659 [wd 15, wd 0, wd 0, wd 3450, flag b] m)
      21 := by
    opt44_reach [1139, 1140, 1141, 1142, 1143, 1144]
  obtain ⟨m', hpost, hfr, hR⟩ := group_glue hs 21 hb1 (by simp only [isValidJumpDest_lit])
    (by norm_num) hI.rc4 hI.rho (by norm_num : (0 : Nat) < 4) hcd
  have hb2 : Reach (callState s 3450 [flag (okCol s.executionEnv.calldata 0), flag b] m')
      (callState s 3452 [flag (b && okCol s.executionEnv.calldata 0)] m') 4 := by
    opt44_reach [1145, 1146] with [flag, ite01_land]
  have hzh : ∀ t, t < 256 → word m' (ZH + 32 * t) = word m (ZH + 32 * t) := fun t ht =>
    word_frame hfr (lo := ZH) (hi := ZH + 8192) (by unfold groupFrame; avoids_tac) (by omega) (by omega)
  have hacc0 : AccCols m s.executionEnv.calldata 0 := fun _ t _ => by
    rw [word_zero_of_zeroOn hI.zHigh (by unfold BASES ACC; omega) (by unfold ACC HP; omega)]
    rfl
  refine ⟨m', ⟨hI.rc4.frame hfr (by unfold groupFrame; avoids_tac),
    hI.rc1.frame hfr (by unfold groupFrame; avoids_tac), hI.tbl.frame hfr (by unfold groupFrame; avoids_tac),
    hI.zhat.frame hfr (by unfold groupFrame; avoids_tac), hI.hp.frame hfr (by unfold groupFrame; avoids_tac),
    hI.rho.frame hfr (by unfold groupFrame; avoids_tac),
    accCols_step (by norm_num) hacc0 (fun k hk t ht => (hI.zhat k hk t ht).1) hzh hpost,
    (hI.zMisc.mono (le_refl _) (by unfold MISC TBL; omega)).frame hfr (by unfold groupFrame; avoids_tac),
    hI.zCw.frame hfr (by unfold groupFrame; avoids_tac),
    (hI.zHigh.mono (le_refl _) (by unfold ACC HP; omega)).frame hfr
      (by unfold groupFrame; avoids_tac)⟩,
    (hR.trans hb2).mono (by unfold Gas.pG0; omega)⟩

theorem seg_g1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3452 [flag b] m)
        (callState s 3466 [flag (b && okCol s.executionEnv.calldata 1)] m') Gas.pG1 := by
  have hb1 : Reach (callState s 3452 [flag b] m) (callState s 13659 [wd 15, wd 1, wd 0, wd 3464, flag b] m)
      22 := by
    opt44_reach [1147, 1148, 1149, 1150, 1151, 1152]
  obtain ⟨m', hpost, hfr, hR⟩ := group_glue hs 22 hb1 (by simp only [isValidJumpDest_lit])
    (by norm_num) hI.rc4 hI.rho (by norm_num : (1 : Nat) < 4) hcd
  have hb2 : Reach (callState s 3464 [flag (okCol s.executionEnv.calldata 1), flag b] m')
      (callState s 3466 [flag (b && okCol s.executionEnv.calldata 1)] m') 4 := by
    opt44_reach [1153, 1154] with [flag, ite01_land]
  have hzh : ∀ t, t < 256 → word m' (ZH + 32 * t) = word m (ZH + 32 * t) := fun t ht =>
    word_frame hfr (lo := ZH) (hi := ZH + 8192) (by unfold groupFrame; avoids_tac) (by omega) (by omega)
  refine ⟨m', ⟨hI.rc4.frame hfr (by unfold groupFrame; avoids_tac),
    hI.rc1.frame hfr (by unfold groupFrame; avoids_tac), hI.tbl.frame hfr (by unfold groupFrame; avoids_tac),
    hI.zhat.frame hfr (by unfold groupFrame; avoids_tac), hI.hp.frame hfr (by unfold groupFrame; avoids_tac),
    hI.rho.frame hfr (by unfold groupFrame; avoids_tac),
    accCols_step (by norm_num) hI.acc (fun k hk t ht => (hI.zhat k hk t ht).1) hzh hpost,
    hI.zMisc.frame hfr (by unfold groupFrame; avoids_tac),
    hI.zCw.frame hfr (by unfold groupFrame; avoids_tac),
    hI.zIdx.frame hfr (by unfold groupFrame; avoids_tac)⟩,
    (hR.trans hb2).mono (by unfold Gas.pG1; omega)⟩

end MlDsaOpt44.Proofs
