import MlDsaOpt65.Fn.NttV4.Passes
import MlDsaOpt44.Fn.Ntt.V4.Top
import MlDsaOpt65.Budget
import MlDsa.Bridge44
/-!
# v4 `ntt` and `intt` end to end (ML-DSA-65)

As `MlDsaOpt44/Fn/Ntt/V4/Top.lean`, for the polynomial addresses of the two call
sites (`ZH`/`ZH2`, `ACC + 0x2000 g`): prologue, the three passes, the return.
The forward lanes start in the `γ1 = 2^19` bias interval (`lo6`/`hi6`); the
inverse NTT's last pass stores `uh6L (SP_g + W) HP_g` with `W ≡ NTT⁻¹`, which is
`UseHint(HP_g, SP_g + W − (γ2 − 1))` (`uh6L_spec`) and
`SP_g + W − (γ2 − 1) ≡ NTT⁻¹ + SP_g − spOff (mod q)`.
-/

namespace MlDsaOpt65.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon
open MlDsaOpt65.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.Ntt4 MlDsaOpt65.Proofs.Ntt6
  MlDsaOpt65.Proofs.NttV4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem ntt_v4 {s : State} (hs : Ctx s) {p : Nat} (hp : p = ZH ∨ p = ZH2) {ret : Nat}
    {tail : List UInt256} (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (p + 32 * t)) k ∧
          lane (word m (p + 32 * t)) k ≤ zHi) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (p + 32 * t)) k < 2 ^ 28 ∧
          ((lane (word m' (p + 32 * t)) k : Int) - (MlDsa.Fips204.ntt (lanesPoly m p k))[t]!) %
            (MlDsa.Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(p, p + 8192)] ∧
      Call s Entry.ntt [wd p] ret tail m [] m' Gas.ntt := by
  rw [MlDsa.Bridge44.ntt_eq, MlDsa.Bridge44.q_eq]
  have hpv : p = 32768 ∨ p = 40960 := by unfold ZH ZH2 at hp; exact hp
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.ntt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m p k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  have hP0 : (∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (p + 32 * t)) k ∧
      lane (word m (p + 32 * t)) k ≤ zHi) →
      PI m p (fun t => t % 32 < 0) (fun t w => LI6 (UInt256.ofNat w) 0 (fun k => fwdL (h k) 0 t))
        (fun t w => LI6 (UInt256.ofNat w) 3 (fun k => fwdL (h k) 3 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    have hb := hH k hk t ht
    have e1 : zLo = lo6 0 := by unfold zLo lo6 MlDsa.Fips204.q; norm_num
    have e2 : zHi = hi6 0 := by unfold zHi hi6 MlDsa.Fips204.q; norm_num
    rw [e1, e2] at hb
    refine ⟨hb.1, hb.2, ?_⟩
    show _ = h k t
    simp only [hh]
    rw [lanesPoly_get' m p k ht]; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := fA_pass hs htail ret _ h p hpv m hP0
  have htbl1 := tblAt_frame htbl hF1 (by omega)
  obtain ⟨M2, hP2, hF2, hR2⟩ := fB_pass hs htail ret _ h p hpv M1 htbl1
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  have htbl2 := tblAt_frame htbl1 hF2 (by omega)
  obtain ⟨M3, hP3, hF3, hR3⟩ := fC_pass hs htail ret _ h p hpv M2 htbl2 hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun hH k hk t ht => ?_, frame_trans1 (frame_trans1 hF1 hF2) hF3, ?_⟩
  · have hv := passInvG_done (hP3 hH) (fun t _ => by omega) t ht k hk
    rw [lane_word] at hv
    refine ⟨Nat.lt_of_le_of_lt hv.2.1 (hi6_lt le_rfl), congr_of_F ?_⟩
    rw [hv.2.2, ntt_model _ (lanesPoly_size' m p k) ht, hh]
  · rw [call_iff, Entry.ntt, Gas.ntt]
    exact (((reach_post2 (f_pro hs htail m ret p (by omega)) rfl (by omega)).trans
      (hR1.trans (hR2.trans hR3))).mono (by norm_num)).of_eq (by simp) (by simp)

theorem intt_v4 {s : State} (hs : Ctx s) {g : Nat} (hg : g < 2) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) →
        (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 0x2000 * g + 32 * t)) r ≤ spOff ∧
          lane (word m (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r =
          (MlDsa.Fips204.useHint P (lane (word m (HP + 0x2000 * g + 32 * t)) r)
            ((MlDsa.Fips204.nttInv (lanesPoly m (ACC + 0x2000 * g) r))[t]! +
              lane (word m (SP + 0x2000 * g + 32 * t)) r - spOff)).toNat) ∧
      FrameExcept m m' [(ACC + 0x2000 * g, ACC + 0x2000 * g + 8192)] ∧
      Call s Entry.intt [wd (ACC + 0x2000 * g)] ret tail m [] m' Gas.intt := by
  rw [MlDsa.Bridge44.nttInv_eq]
  obtain ⟨A, hA⟩ : ∃ A, A = ACC + 0x2000 * g := ⟨_, rfl⟩
  rw [← hA]
  have hSPa : ∀ t, SP + 0x2000 * g + 32 * t = A - 18688 + 32 * t := fun t => by
    rw [hA]; unfold SP ACC; omega
  have hHPa : ∀ t, HP + 0x2000 * g + 32 * t = A + 16384 + 32 * t := fun t => by
    rw [hA]; unfold HP ACC; omega
  simp only [hSPa, hHPa]
  have hAv : A = 51456 ∨ A = 59648 := by rw [hA]; unfold ACC; omega
  have hsp : spOff = 128 * 8380417 + 261888 - 1 := by unfold spOff MlDsa.Fips204.q; norm_num
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.intt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m A k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  let H : Prop := (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (A + 32 * t)) k < 2 ^ 57) ∧
    (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (A - 18688 + 32 * t)) r ≤ spOff ∧
      lane (word m (A + 16384 + 32 * t)) r ≤ 1)
  have hP0 : H → PI m A (fun t => t / 4 < 0)
      (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (fun t w => LOK (UInt256.ofNat w) (Bi 2) (fun k => invL (scaleR h k) 2 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨hH.1 k hk t ht, ?_⟩
    show _ = h k t
    simp only [hh]
    rw [lanesPoly_get' m A k ht]; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := iC_pass hs htail ret H h A hAv m htbl hP0
  have htbl1 := tblAt_frame htbl hF1 (by omega)
  obtain ⟨M2, hP2, hF2, hR2⟩ := iB_pass hs htail ret H h A hAv M1 htbl1
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  obtain ⟨M3, hP3, hF3, hR3⟩ := iA_pass hs htail ret H h A hAv M2 m (frame_trans1 hF1 hF2)
    (fun hH t ht r hr4 => by rw [← hsp]; exact hH.2 t ht r hr4) hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun h1 h2 t ht r hr4 => ?_, frame_trans1 (frame_trans1 hF1 hF2) hF3, ?_⟩
  · obtain ⟨W, hWB, hWF, hlane⟩ := passInvG_done (hP3 ⟨h1, h2⟩) (fun t _ => by omega) t ht r hr4
    rw [hlane, uh6L_spec P rfl (h2 t ht r hr4).2]
    congr 1
    rw [useHint_emod6 P _ (_ - 261887), useHint_emod6 P _ (_ - (spOff : Int))]
    congr 1
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    have hWn : ((W : ℤ) : F) = (((MlDsa44.Fips204.nttInv (lanesPoly m A r))[t]! : ℤ) : F) := by
      push_cast
      beta_reduce at hWF
      rw [hWF, nttInv_model _ (lanesPoly_size' m A r) ht]
      have e : scaleR h r = fun i => Rinv * (((lanesPoly m A r)[i]! : ℤ) : F) := by
        funext i; simp only [scaleR, hh]; rw [mul_comm]
      rw [e, invL_smul]
      unfold Sc
      linear_combination (8347681 * invL (fun i => (((lanesPoly m A r)[i]! : ℤ) : F)) 8 t) * R_Rinv
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (W : ℤ)
      ((MlDsa44.Fips204.nttInv (lanesPoly m A r))[t]!) 8380417).mp hWn
    refine ⟨-c + 128, ?_⟩
    have hq : (MlDsa.Fips204.q : Int) = 8380417 := by unfold MlDsa.Fips204.q; norm_num
    rw [hsp, hq]
    push_cast
    linear_combination -hc
  · rw [call_iff, Entry.intt, Gas.intt]
    exact (((i_pro hs htail m ret A (by omega)).trans (hR1.trans (hR2.trans hR3))).mono
      (by norm_num)).of_eq (by simp) (by simp)

end MlDsaOpt65.Proofs.Ntt4
