import MlDsaOptGlam44.Fn.Ntt.FwdA
import MlDsaOptGlam44.Fn.Ntt.FwdB
import MlDsaOptGlam44.Fn.Ntt.Inv1
import MlDsaOptGlam44.Fn.Ntt.Inv2
import MlDsaOptGlam44.Fn.Ntt.Ctl
/-!
# The four loops of the glam `ntt` / `intt`, and both routines end to end

Each pass iterates its generated loop body (`*_body`, 16 words) with its back
edge (`Ctl.lean`) 15 times, then runs the last body and the exit; the memory
after each iteration is known only through the pass invariant (v4's
`reach_iterF`, `PI`). The routines chain the invariants as v4's
`Ntt4.ntt_v4` / `intt_v4` do, with layer boundaries 4 and 8 instead of
3, 6, 8 (forward) and 2, 5, 8 (inverse).
-/

namespace MlDsaOptGlam44.Proofs.NttG

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.NttV4 MlDsaOpt44.Proofs.Ntt4
open MlDsaOptGlam44.Proofs MlDsaOptGlam44.Proofs.Infra

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local notation "cM" => UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855
local notation "cCI" => UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723
local notation "cU0" => UInt256.ofNat 3207598986782593870493972684755717093467514342740420773020159
local notation "cU1" => UInt256.ofNat 276192476357013953623747158765658614701703779022658540142636
local notation "cU2" => UInt256.ofNat 102837757730839990959496584137676933742227568448368519617200127
local notation "cU3" => UInt256.ofNat 6421475075300574421752121441301562791814612862276811058316287

/-- Forward pass predicates: lanes in the layer-`L` interval, congruent to `fwdL`. -/
local notation "FP" h:max L:max => fun t w => LI (UInt256.ofNat w) L (fun k => fwdL (h k) L t)
/-- Inverse pass predicates: lanes below `B`, congruent to `invL` of the scaled input. -/
local notation "IP" h:max B:max L:max => fun t w => LOK (UInt256.ofNat w) B (fun k => invL (scaleR h k) L t)

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950) (ret : Nat)
  (H : Prop) (h : Nat → Nat → F)
include hs htail

theorem fwA_pass (M0 : ByteArray) (hP0 : H → PI M0 32768 (fun t => t % 16 < 0) (FP h 0) (FP h 4)) :
    ∃ M', (H → PI M' 32768 (fun t => t % 16 < 16) (FP h 0) (FP h 4)) ∧
      FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 23761 (UInt256.ofNat 32768 :: UInt256.ofNat 33280 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s 24955 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M') 38682 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s 23761 (UInt256.ofNat (32768 + 32 * c) :: UInt256.ofNat 33280 ::
      cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PI M 32768 (fun t => t % 16 < c) (FP h 0) (FP h 4)) ∧
      FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun _ => 2389 + 28) 15 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fwA_body hs htail ret H h c (by omega) M hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (fwA_cont hs htail M' ret (32768 + 32 * c) (by omega))) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fwA_body hs htail ret H h 15 (by norm_num) M1 hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fwA_exit hs htail M2 ret (32768 + 32 * 15) (by norm_num))).mono
      (by simp only [costSum]; norm_num)⟩

theorem fwB_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hj : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PI M0 32768 (fun t => t / 16 < 0) (FP h 4) (FP h 8)) :
    ∃ M', (H → PI M' 32768 (fun t => t / 16 < 16) (FP h 4) (FP h 8)) ∧
      FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 24955 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s ret tail M') 43680 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 24955 (UInt256.ofNat (32768 + 512 * n) ::
      UInt256.ofNat (4096 + 480 * n) :: cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M 32768 (fun t => t / 16 < n) (FP h 4) (FP h 8)) ∧
      FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun _ => 2689 + 40) 15 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fwB_body hs htail ret H h n (by omega) M
        (tblG_frame htbl hQ.2 (by norm_num)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (fwB_cont hs htail M' ret _ _ (by omega) (by omega))) (by omega)
          (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fwB_body hs htail ret H h 15 (by norm_num) M1
    (tblG_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fwB_exit hs htail M2 ret _ _ (by norm_num) (by norm_num) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

theorem inA_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PI M0 43264 (fun t => t / 16 < 0) (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (IP h (Bi 4) 4)) :
    ∃ M', (H → PI M' 43264 (fun t => t / 16 < 16)
        (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t)) (IP h (Bi 4) 4)) ∧
      FrameExcept M0 M' [(43264, 43264 + 8192)] ∧
      Reach (callState s 26375 (UInt256.ofNat 43264 :: UInt256.ofNat 11296 :: cCI :: cM ::
          UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M0)
        (callState s 28269 (UInt256.ofNat 43264 :: UInt256.ofNat 43776 :: cU3 :: cU2 :: cU1 :: cU0 ::
          cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M') 57100 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 26375 (UInt256.ofNat (43264 + 512 * n) ::
      UInt256.ofNat (11296 - 480 * n) :: cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M 43264 (fun t => t / 16 < n)
        (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t)) (IP h (Bi 4) 4)) ∧
      FrameExcept M0 M [(43264, 43264 + 8192)])
    (c := fun _ => 3521 + 46) 15 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := inA_body hs htail ret H h n (by omega) M
        (tblG_frame htbl hQ.2 (by norm_num)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (inA_cont hs htail M' ret _ _ (by omega) (by omega) (by omega)
          (by omega))) (by omega) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := inA_body hs htail ret H h 15 (by norm_num) M1
    (tblG_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (inA_exit hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem inB_pass (M0 m0 : ByteArray) (hF0 : FrameExcept m0 M0 [(43264, 43264 + 8192)])
    (hSH : H → ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (SP + 32 * t)) r ≤ spOff ∧
      lane (word m0 (HP + 32 * t)) r ≤ 1)
    (hj : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PI M0 43264 (fun t => t % 16 < 0) (IP h (Bi 4) 4)
      (fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))) :
    ∃ M', (H → PI M' 43264 (fun t => t % 16 < 16) (IP h (Bi 4) 4)
        (fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))) ∧
      FrameExcept M0 M' [(43264, 43264 + 8192)] ∧
      Reach (callState s 28269 (UInt256.ofNat 43264 :: UInt256.ofNat 43776 :: cU3 :: cU2 :: cU1 :: cU0 ::
          cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M0)
        (callState s ret tail M') 88362 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s 28269 (UInt256.ofNat (43264 + 32 * c) :: UInt256.ofNat 43776 ::
      cU3 :: cU2 :: cU1 :: cU0 :: cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PI M 43264 (fun t => t % 16 < c) (IP h (Bi 4) 4)
        (fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))) ∧
      FrameExcept M0 M [(43264, 43264 + 8192)])
    (c := fun _ => 5493 + 28) 15 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := inB_body hs htail ret H h c (by omega) M m0
        (frame_trans1 hF0 hQ.2) hSH hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (inB_cont hs htail M' ret (43264 + 32 * c) (by omega))) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := inB_body hs htail ret H h 15 (by norm_num) M1 m0
    (frame_trans1 hF0 hF1) hSH hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (inB_exit hs htail M2 ret (43264 + 32 * 15) (by norm_num) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

end

theorem ntt_g {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (ZH + 32 * t)) k ∧
          lane (word m (ZH + 32 * t)) k ≤ zHi) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (ZH + 32 * t)) k < 2 ^ 28 ∧
          ((lane (word m' (ZH + 32 * t)) k : Int) - (Fips204.ntt (lanesPoly m ZH k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.ntt [wd ZH] ret tail m [] m' Gas.ntt := by
  have htail : tail.length ≤ 950 := by
    have := hr.depth; simp only [Stack.ntt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m ZH k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  have hP0 : (∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (ZH + 32 * t)) k ∧
      lane (word m (ZH + 32 * t)) k ≤ zHi) →
      PI m 32768 (fun t => t % 16 < 0) (fun t w => LI (UInt256.ofNat w) 0 (fun k => fwdL (h k) 0 t))
        (fun t w => LI (UInt256.ofNat w) 4 (fun k => fwdL (h k) 4 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    have hb := hH k hk t ht
    unfold ZH at hb
    rw [zLo_eq, zHi_eq] at hb
    refine ⟨hb.1, hb.2, ?_⟩
    show _ = h k t
    simp only [hh]
    rw [lanesPoly_get' m ZH k ht]; unfold ZH; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := fwA_pass hs htail ret _ h m hP0
  have htbl1 := tblG_frame htbl hF1 (by norm_num)
  obtain ⟨M2, hP2, hF2, hR2⟩ := fwB_pass hs htail ret _ h M1 htbl1 hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M2, fun hH k hk t ht => ?_, ?_, ?_⟩
  · have hv := passInvG_done (hP2 hH) (fun t _ => by omega) t ht k hk
    rw [lane_word] at hv
    unfold ZH
    refine ⟨Nat.lt_of_le_of_lt hv.2.1 (hi4_lt le_rfl), congr_of_F ?_⟩
    rw [hv.2.2, ntt_model _ (lanesPoly_size' m 32768 k) ht, hh]
    rfl
  · unfold ZH; exact frame_trans1 hF1 hF2
  · rw [call_iff, Entry.ntt, Gas.ntt]
    exact (((f_pro hs htail m ret).trans (hR1.trans hR2)).mono (by norm_num)).of_eq
      (by simp [ZH]) (by simp)

theorem intt_g {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 57) →
        (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 32 * t)) r ≤ spOff ∧
          lane (word m (HP + 32 * t)) r ≤ 1) →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 32 * t)) r =
          (Fips204.useHint (lane (word m (HP + 32 * t)) r)
            ((Fips204.nttInv (lanesPoly m ACC r))[t]! + lane (word m (SP + 32 * t)) r - spOff)).toNat) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.intt [wd ACC] ret tail m [] m' Gas.intt := by
  have htail : tail.length ≤ 950 := by
    have := hr.depth; simp only [Stack.intt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m ACC k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  let H : Prop := (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 57) ∧
    (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 32 * t)) r ≤ spOff ∧
      lane (word m (HP + 32 * t)) r ≤ 1)
  have hP0 : H → PI m 43264 (fun t => t / 16 < 0)
      (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (fun t w => LOK (UInt256.ofNat w) (Bi 4) (fun k => invL (scaleR h k) 4 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨?_, ?_⟩
    · have := hH.1 k hk t ht; unfold ACC at this; exact this
    · show _ = h k t
      simp only [hh]
      rw [lanesPoly_get' m ACC k ht]; unfold ACC; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := inA_pass hs htail ret H h m htbl hP0
  obtain ⟨M2, hP2, hF2, hR2⟩ := inB_pass hs htail ret H h M1 m hF1 (fun hH => hH.2)
    hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M2, fun h1 h2 t ht r hr4 => ?_, ?_, ?_⟩
  · obtain ⟨W, hWB, hWF, hlane⟩ := passInvG_done (hP2 ⟨h1, h2⟩) (fun t _ => by omega) t ht r hr4
    rw [show ACC + 32 * t = 43264 + 32 * t from rfl, hlane, uh4L_spec (h2 t ht r hr4).2]
    congr 1
    apply useHint_congr
    have hWn : ((W : ℤ) : F) = (((Fips204.nttInv (lanesPoly m ACC r))[t]! : ℤ) : F) := by
      push_cast
      beta_reduce at hWF
      rw [hWF, nttInv_model _ (lanesPoly_size' m ACC r) ht]
      have e : scaleR h r = fun i => Rinv * (((lanesPoly m ACC r)[i]! : ℤ) : F) := by
        funext i; simp only [scaleR, hh]; rw [mul_comm]
      rw [e, invL_smul]
      unfold Sc
      linear_combination (8347681 * invL (fun i => (((lanesPoly m ACC r)[i]! : ℤ) : F)) 8 t) * R_Rinv
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (W : ℤ)
      ((Fips204.nttInv (lanesPoly m ACC r))[t]!) 8380417).mp hWn
    obtain ⟨c, hc⟩ := hd
    refine ⟨-c + 128, ?_⟩
    have hsp : (spOff : Int) = 128 * 8380417 + 95231 := by
      unfold spOff Fips204.gamma2 Fips204.q; norm_num
    have hq : (Fips204.q : Int) = 8380417 := by unfold Fips204.q; norm_num
    rw [hsp, hq]
    push_cast
    linear_combination -hc
  · unfold ACC; exact frame_trans1 hF1 hF2
  · rw [call_iff, Entry.intt, Gas.intt]
    exact (((i_pro hs htail m ret).trans (hR1.trans hR2)).mono (by norm_num)).of_eq
      (by simp [ACC]) (by simp)

end MlDsaOptGlam44.Proofs.NttG
