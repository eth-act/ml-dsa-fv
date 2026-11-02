import MlDsaOpt44.Fn.Ntt.V4.Passes
import MlDsaOpt44.Fn.Ntt.Model
import MlDsaOpt44.Budget
/-!
# v4 `ntt` and `intt` end to end (WP G, H)

Prologue, the three passes, the return. The pass invariants are chained
(`passInvG_done` → `passInvG_init`) and the zeta table survives every pass
(`tblAt_frame`).

* `ntt`: inputs in `[zLo, zHi]` (`z + 8q`) start the bias interval; after 8
  layers the lanes are `< 2^28` and congruent to `ntt_model`.
* `intt`: the last pass stores `uh4L (SP + W) HP` with `W ≡ NTT⁻¹` (`invL_smul`
  cancels the `premont` factor against `Sc`), which is `UseHint(HP, SP + W − (γ2 − 1))`
  (`uh4L_spec`); `SP + W − (γ2 − 1) ≡ NTT⁻¹ + SP − spOff (mod q)`.
-/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.NttV4

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedTactic false

theorem lanesPoly_get' (m : ByteArray) (base k : Nat) {t : Nat} (ht : t < 256) :
    (lanesPoly m base k)[t]! = (lane (word m (base + 32 * t)) k : Int) := by
  unfold lanesPoly; simp [getElem!_pos, ht]

theorem lanesPoly_size' (m : ByteArray) (base k : Nat) : (lanesPoly m base k).size = 256 := by
  simp [lanesPoly]

theorem lane_word (m : ByteArray) (a k : Nat) :
    lane (UInt256.ofNat (word m a)).toNat k = lane (word m a) k := by
  rw [toNat_ofNat_of_lt (word_lt m a)]

theorem congr_of_F {x : Nat} {y : Int} (h : ((x : ℕ) : F) = ((y : ℤ) : F)) :
    ((x : Int) - y) % (Fips204.q : Int) = 0 := by
  apply Int.emod_eq_zero_of_dvd
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub y (x : ℤ) 8380417).mp (by push_cast; exact h.symm)
  simpa [Fips204.q] using this

theorem ntt_v4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (ZH + 32 * t)) k ∧
          lane (word m (ZH + 32 * t)) k ≤ zHi) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (ZH + 32 * t)) k < 2 ^ 28 ∧
          ((lane (word m' (ZH + 32 * t)) k : Int) - (Fips204.ntt (lanesPoly m ZH k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.ntt [wd ZH] ret tail m [] m' Gas.ntt := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.ntt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m ZH k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  have hP0 : (∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (ZH + 32 * t)) k ∧
      lane (word m (ZH + 32 * t)) k ≤ zHi) →
      PI m 32768 (fun t => t % 32 < 0) (fun t w => LI (UInt256.ofNat w) 0 (fun k => fwdL (h k) 0 t))
        (fun t w => LI (UInt256.ofNat w) 3 (fun k => fwdL (h k) 3 t)) := by
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
  obtain ⟨M1, hP1, hF1, hR1⟩ := fA_pass hs htail ret _ h m hP0
  have htbl1 := tblAt_frame htbl hF1 (by norm_num)
  obtain ⟨M2, hP2, hF2, hR2⟩ := fB_pass hs htail ret _ h M1 htbl1
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  have htbl2 := tblAt_frame htbl1 hF2 (by norm_num)
  obtain ⟨M3, hP3, hF3, hR3⟩ := fC_pass hs htail ret _ h M2 htbl2 hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun hH k hk t ht => ?_, ?_, ?_⟩
  · have hv := passInvG_done (hP3 hH) (fun t _ => by omega) t ht k hk
    rw [lane_word] at hv
    unfold ZH
    refine ⟨Nat.lt_of_le_of_lt hv.2.1 (hi4_lt le_rfl), congr_of_F ?_⟩
    rw [hv.2.2, ntt_model _ (lanesPoly_size' m 32768 k) ht, hh]
    rfl
  · unfold ZH; exact frame_trans1 (frame_trans1 hF1 hF2) hF3
  · rw [call_iff, Entry.ntt, Gas.ntt]
    exact (((f_pro hs htail m ret).trans (hR1.trans (hR2.trans hR3))).mono (by norm_num)).of_eq
      (by simp [ZH]) (by simp)

/-- `UseHint` only sees its argument mod `q`. -/
theorem useHint_congr (h : Int) {a b : Int} (hab : (Fips204.q : Int) ∣ a - b) :
    Fips204.useHint h a = Fips204.useHint h b := by
  rw [useHint_emod' h a, useHint_emod' h b]
  congr 1
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hab)

theorem intt_v4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 57) →
        (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 32 * t)) r ≤ spOff ∧
          lane (word m (HP + 32 * t)) r ≤ 1) →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 32 * t)) r =
          (Fips204.useHint (lane (word m (HP + 32 * t)) r)
            ((Fips204.nttInv (lanesPoly m ACC r))[t]! + lane (word m (SP + 32 * t)) r - spOff)).toNat) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.intt [wd ACC] ret tail m [] m' Gas.intt := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.intt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m ACC k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  let H : Prop := (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 57) ∧
    (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 32 * t)) r ≤ spOff ∧
      lane (word m (HP + 32 * t)) r ≤ 1)
  have hP0 : H → PI m 43264 (fun t => t / 4 < 0)
      (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (fun t w => LOK (UInt256.ofNat w) (Bi 2) (fun k => invL (scaleR h k) 2 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨?_, ?_⟩
    · have := hH.1 k hk t ht; unfold ACC at this; exact this
    · show _ = h k t
      simp only [hh]
      rw [lanesPoly_get' m ACC k ht]; unfold ACC; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := iC_pass hs htail ret H h m htbl hP0
  have htbl1 := tblAt_frame htbl hF1 (by norm_num)
  obtain ⟨M2, hP2, hF2, hR2⟩ := iB_pass hs htail ret H h M1 htbl1
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  obtain ⟨M3, hP3, hF3, hR3⟩ := iA_pass hs htail ret H h M2 m (frame_trans1 hF1 hF2) (fun hH => hH.2)
    hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun h1 h2 t ht r hr4 => ?_, ?_, ?_⟩
  · obtain ⟨W, hWB, hWF, hlane⟩ := passInvG_done (hP3 ⟨h1, h2⟩) (fun t _ => by omega) t ht r hr4
    rw [show ACC + 32 * t = 43264 + 32 * t from rfl, hlane, uh4L_spec (h2 t ht r hr4).2]
    congr 1
    apply useHint_congr
    -- `W ≡ NTT⁻¹(ACC)[t]`
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
  · unfold ACC; exact frame_trans1 (frame_trans1 hF1 hF2) hF3
  · rw [call_iff, Entry.intt, Gas.intt]
    exact (((i_pro hs htail m ret).trans (hR1.trans (hR2.trans hR3))).mono (by norm_num)).of_eq
      (by simp [ACC]) (by simp)

end MlDsaOpt44.Proofs.Ntt4
