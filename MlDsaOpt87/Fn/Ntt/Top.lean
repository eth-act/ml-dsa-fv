import MlDsaOpt87.Fn.Ntt.Passes
import MlDsaOpt44.Fn.Ntt.Model
import MlDsaOpt87.Budget
import MlDsaOpt87.Layout
/- Ported from `MlDsaOpt44/Fn/Ntt/Top.lean` by `scripts/proofgen_port.py 87` --sub 43264=51456 --sub 44288=52480 --sub 66080=91680 --sub 60000=70000; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# `ntt` and `intt` end to end (WP7)

Prologue, the three passes, the return; the pass invariants are chained
(`passInv_done` → `passInv_init`), the zeta table survives every pass
(`tblAt_frame`), and the final lane congruences come from `ntt_model` /
`nttInv_model` (`invL_smul` cancels the `premont` factor against `Sc`).
-/

namespace MlDsaOpt87.Proofs.NttW

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt87.Proofs MlDsaOpt44.Proofs

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

theorem ntt_full {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (32768 + 32 * t)) k < 2 ^ 25) →  -- port: literal base
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (32768 + 32 * t)) k < 2 ^ 28 ∧  -- port: literal base
          ((lane (word m' (32768 + 32 * t)) k : Int) - (Fips204.ntt (lanesPoly m 32768 k))[t]!) %  -- port: literal base
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(32768, 32768 + 8192)] ∧  -- port: literal base
      Call s Entry.ntt [wd 32768] ret tail m [] m' Gas.ntt := by  -- port: literal base
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.ntt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m 32768 k)[t]! : ℤ) : F) := ⟨_, rfl⟩  -- port: literal base
  have hP0 : (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (32768 + 32 * t)) k < 2 ^ 25) →  -- port: literal base
      PassInv m 32768 (fun t => t % 32 < 0) (Bf 0) (Bf 3) (fun k => fwdL (h k) 0)
        (fun k => fwdL (h k) 3) := by
    intro hH
    refine passInv_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨?_, ?_⟩
    · have := hH k hk t ht; unfold Bf; omega  -- port: literal base
    · show _ = h k t
      simp only [hh]
      rw [lanesPoly_get' m 32768 k ht]; push_cast; rfl  -- port: literal base
  obtain ⟨M1, hP1, hF1, hR1⟩ := fA_pass hs htail ret _ h m hP0
  have htbl1 := tblAt_frame htbl hF1 (by norm_num)
  obtain ⟨M2, hP2, hF2, hR2⟩ := fB_pass hs htail ret _ h M1 htbl1
    (fun hH => passInv_init (passInv_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  have htbl2 := tblAt_frame htbl1 hF2 (by norm_num)
  obtain ⟨M3, hP3, hF3, hR3⟩ := fC_pass hs htail ret _ h M2 htbl2 hr.jumpdest hr.small
    (fun hH => passInv_init (passInv_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun hH k hk t ht => ?_, ?_, ?_⟩
  · have hv := passInv_done (hP3 hH) (fun t _ => by omega) t ht k hk
    rw [lane_word] at hv
    -- port: literal base, `unfold ZH` dropped
    refine ⟨by have := hv.1; unfold Bf at this; omega, congr_of_F ?_⟩
    rw [hv.2, ntt_model _ (lanesPoly_size' m 32768 k) ht, hh]
    -- port: literal base, the `rw` closes the goal (`rfl` dropped)
  · exact frame_trans1 (frame_trans1 hF1 hF2) hF3  -- port: literal base
  · rw [call_iff, Entry.ntt, Gas.ntt]
    exact (((f_pro hs htail m ret).trans (hR1.trans (hR2.trans hR3))).mono (by norm_num)).of_eq
      (by simp) (by simp)  -- port: literal base

theorem intt_full {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (51456 + 32 * t)) k < 2 ^ 58) →  -- port: literal base
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (51456 + 32 * t)) k < 2 ^ 27 ∧  -- port: literal base
          ((lane (word m' (51456 + 32 * t)) k : Int) - (Fips204.nttInv (lanesPoly m 51456 k))[t]!) %  -- port: literal base
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(51456, 51456 + 8192)] ∧  -- port: literal base
      Call s Entry.intt [wd 51456] ret tail m [] m' Gas.intt := by  -- port: literal base
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.intt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m 51456 k)[t]! : ℤ) : F) := ⟨_, rfl⟩  -- port: literal base
  have hP0 : (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (51456 + 32 * t)) k < 2 ^ 58) →  -- port: literal base
      PassInv m 51456 (fun t => t / 4 < 0) (2 ^ 58) (Bi 2) h (fun k => invL (scaleR h k) 2) := by
    intro hH
    refine passInv_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨?_, ?_⟩
    · have := hH k hk t ht; exact this  -- port: literal base
    · show _ = h k t
      simp only [hh]
      rw [lanesPoly_get' m 51456 k ht]; push_cast; rfl  -- port: literal base
  obtain ⟨M1, hP1, hF1, hR1⟩ := iC_pass hs htail ret _ h m htbl hP0
  have htbl1 := tblAt_frame htbl hF1 (by norm_num)
  obtain ⟨M2, hP2, hF2, hR2⟩ := iB_pass hs htail ret _ h M1 htbl1
    (fun hH => passInv_init (passInv_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  obtain ⟨M3, hP3, hF3, hR3⟩ := iA_pass hs htail ret _ h M2 hr.jumpdest hr.small
    (fun hH => passInv_init (passInv_done (hP2 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M3, fun hH k hk t ht => ?_, ?_, ?_⟩
  · have hv := passInv_done (hP3 hH) (fun t _ => by omega) t ht k hk
    rw [lane_word] at hv
    -- port: literal base, `unfold ACC` dropped
    refine ⟨by have := hv.1; unfold Bu at this; omega, congr_of_F ?_⟩
    have hv2 := hv.2
    beta_reduce at hv2
    rw [hv2, nttInv_model _ (lanesPoly_size' m 51456 k) ht]
    have e : scaleR h k = fun i => Rinv * (((lanesPoly m 51456 k)[i]! : ℤ) : F) := by
      funext i; simp only [scaleR, hh]; rw [mul_comm]  -- port: literal base, `rfl` dropped
    rw [e, invL_smul]
    unfold Sc
    linear_combination (8347681 * invL (fun i => (((lanesPoly m 51456 k)[i]! : ℤ) : F)) 8 t) * R_Rinv
  · exact frame_trans1 (frame_trans1 hF1 hF2) hF3  -- port: literal base
  · rw [call_iff, Entry.intt, Gas.intt]
    exact (((i_pro hs htail m ret).trans (hR1.trans (hR2.trans hR3))).mono (by norm_num)).of_eq
      (by simp) (by simp)  -- port: literal base

end MlDsaOpt87.Proofs.NttW
