import MlDsaOpt87.Fn.NttV4.Passes
import MlDsaOpt44.Fn.Ntt.V4.Top
import MlDsaOpt87.Budget
import MlDsa.Bridge44
/-!
# v4 `ntt` and `intt` end to end (ML-DSA-87)

As `MlDsaOpt44/Fn/Ntt/V4/Top.lean`, for the polynomial addresses of the two call
sites (`ZH`/`ZH2`, `ACC`/`ACC + 0x2000`): prologue, the three passes, the return.
The forward lanes start in the `γ1 = 2^19` bias interval (`lo6`/`hi6`); the inverse
NTT stores its last layer's outputs (`< 2^26 + q`, congruent to `NTT⁻¹`, `invL_smul`
cancelling the `premont` factor against `Sc`); UseHint is the separate `usehint`.
-/

namespace MlDsaOpt87.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon
open MlDsaOpt87.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.Ntt4 MlDsaOpt65.Proofs.Ntt6
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

theorem intt_v4 {s : State} (hs : Ctx s) {p : Nat} (hp : p = ACC ∨ p = ACC + 0x2000)
    {ret : Nat} {tail : List UInt256} (hr : RetOK Stack.intt ret tail) (m : ByteArray)
    (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (p + 32 * t)) k < 2 ^ 57) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (p + 32 * t)) k < 2 ^ 30 ∧
          ((lane (word m' (p + 32 * t)) k : Int) - (MlDsa.Fips204.nttInv (lanesPoly m p k))[t]!) %
            (MlDsa.Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(p, p + 8192)] ∧
      Call s Entry.intt [wd p] ret tail m [] m' Gas.intt := by
  rw [MlDsa.Bridge44.nttInv_eq, MlDsa.Bridge44.q_eq]
  have hpv : p = 51456 ∨ p = 59648 := by unfold ACC at hp; omega
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.intt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m p k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  have hP0 : (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (p + 32 * t)) k < 2 ^ 57) →
      PI m p (fun t => t / 4 < 0) (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
        (fun t w => LOK (UInt256.ofNat w) (Bi 2) (fun k => invL (scaleR h k) 2 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨hH k hk t ht, ?_⟩
    show _ = h k t
    simp only [hh]
    rw [lanesPoly_get' m p k ht]; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := iC_pass hs htail ret _ h p hpv m htbl hP0
  have htbl1 := tblAt_frame htbl hF1 (by omega)
  obtain ⟨M2, hP2, hF2, hR2⟩ := iB_pass hs htail ret _ h p hpv M1 htbl1
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  obtain ⟨M3, hP3, hF3, hR3⟩ := iA_pass hs htail ret _ h p hpv M2 hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun hH k hk t ht => ?_, frame_trans1 (frame_trans1 hF1 hF2) hF3, ?_⟩
  · have hv := passInvG_done (hP3 hH) (fun t _ => by omega) t ht k hk
    rw [lane_word] at hv
    refine ⟨by have := hv.1; unfold Bu at this; omega, congr_of_F ?_⟩
    have hv2 := hv.2
    beta_reduce at hv2
    rw [hv2, nttInv_model _ (lanesPoly_size' m p k) ht]
    have e : scaleR h k = fun i => Rinv * (((lanesPoly m p k)[i]! : ℤ) : F) := by
      funext i; simp only [scaleR, hh]; rw [mul_comm]
    rw [e, invL_smul]
    unfold Sc
    linear_combination (8347681 * invL (fun i => (((lanesPoly m p k)[i]! : ℤ) : F)) 8 t) * R_Rinv
  · rw [call_iff, Entry.intt, Gas.intt]
    exact (((i_pro hs htail m ret p (by omega)).trans (hR1.trans (hR2.trans hR3))).mono
      (by norm_num)).of_eq (by simp) (by simp)

end MlDsaOpt87.Proofs.Ntt4
