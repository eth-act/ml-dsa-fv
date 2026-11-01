import MlDsaOpt44.Fn.Fix.Loop
set_option warningAsError true
/-!
# `fix`: one group and one phase of the group loop
-/

namespace MlDsaOpt44.Proofs.Fix

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- One visit of the group loop body: a flagged or a clean group. -/
theorem group_step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2065 ≤ s.activeWords.toNat) {sl : Nat} (hsl : sl < 4)
    (c : Nat → Nat) (flim g w : Nat) (M : ByteArray) (hg : g < 42) (hfl : 31232 + 32 * g ≠ flim)
    (hflim : flim < 65536) (hacc : AccAt M sl c (8 * g) w)
    (hcand : ∀ i, i < 8 → lane (word M (20480 + 32 * (8 * g + i))) sl = c (8 * g + i))
    (hflag : word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = F c g) :
    ∃ M' w', AccAt M' sl c (8 * g + 8) w' ∧ LaneFrame M M' sl (8 * g + 8) ∧
      Reach (gst s ret tail (64 * sl) (lmask sl) (nmask sl) 13029 flim (20480 + 256 * g)
          (20480 + 32 * w) (31232 + 32 * g) M)
        (gst s ret tail (64 * sl) (lmask sl) (nmask sl) 13546 flim (20480 + 256 * (g + 1))
          (20480 + 32 * w') (31232 + 32 * g) M') 720 := by
  have hsh : 64 * sl ≤ 192 := by omega
  have hwle : w ≤ 8 * g := hacc.1 ▸ accL_length_le c _
  have hb : word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = 0 ∨
      word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = 1 := by omega
  rcases hb with hb | hb
  · -- clean group
    have hq := F_zero (hflag ▸ hb)
    have h1 := fx_gl_clean (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) flim
      (20480 + 256 * g) (20480 + 32 * w) (31232 + 32 * g) hsh hfl (by omega) hflim hb
    have h2 := clean_reach (ret := ret) hs htail hsz (sl := sl) M flim (20480 + 256 * g)
      (20480 + 32 * w) (31232 + 32 * g) (by omega) (by omega)
    have h3 := fx_ctail (ret := ret) hs htail hsz (cwN sl (20480 + 256 * g) (20480 + 32 * w) M 8)
      (64 * sl) (lmask sl) (nmask sl) flim (20480 + 256 * g) (20480 + 32 * w) (31232 + 32 * g)
      (by omega) (by omega)
    rw [show 256 + (20480 + 256 * g) = 20480 + 256 * (g + 1) by omega,
      show 256 + (20480 + 32 * w) = 20480 + 32 * (w + 8) by omega] at h3
    obtain ⟨hA, hL⟩ := cwN_inv hsl c g w M hacc hcand hq 8 (le_refl _)
    exact ⟨_, w + 8, hA, hL, ((h1.trans h2).trans h3).mono (by omega)⟩
  · -- flagged group
    have h1 := fx_gl_flag (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) flim
      (20480 + 256 * g) (20480 + 32 * w) (31232 + 32 * g) hsh hfl (by omega) hflim hb
    have h2 := flagged_reach (ret := ret) hs htail hsz hsl M flim (20480 + 256 * g)
      (20480 + 32 * w) (31232 + 32 * g) (by omega) (by omega)
    obtain ⟨wn, hwn, hA, hL⟩ := fsN_inv hsl c g w M hacc hcand 8 (le_refl _)
    have h3 := fx_ftail (ret := ret) hs htail hsz (fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) 8).1
      (64 * sl) (lmask sl) (nmask sl) flim (20480 + 256 * g)
      (fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) 8).2 (31232 + 32 * g) (by omega)
    rw [show 256 + (20480 + 256 * g) = 20480 + 256 * (g + 1) by omega] at h3
    rw [hwn] at h2 h3
    exact ⟨_, wn, hA, hL, (h1.trans h2).trans h3⟩

/-- A phase of the group loop, from group `g` up to `lim`: either 256
coefficients are accepted (return `1`), or the loop reaches the
exhaustion test `fxe` with fewer. -/
theorem phase {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2065 ≤ s.activeWords.toNat)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 65536)
    {sl : Nat} (hsl : sl < 4) (c : Nat → Nat) (lim : Nat) (hlim : lim ≤ 42) :
    ∀ d g w (M : ByteArray), g + d = lim → AccAt M sl c (8 * g) w → w < 256 →
      (∀ t, 8 * g ≤ t → t < 8 * lim → lane (word M (20480 + 32 * t)) sl = c t) →
      (∀ g', g ≤ g' → g' < lim → word M (31232 + 32 * g') / 2 ^ (23 + 64 * sl) % 2 = F c g') →
      ∃ M', LaneFrame M M' sl (8 * lim) ∧
        ((256 ≤ (accL c (8 * lim)).length ∧
            (∀ i, i < 256 → lane (word M' (20480 + 32 * i)) sl = (accL c (8 * lim))[i]!) ∧
            Reach (gst s ret tail (64 * sl) (lmask sl) (nmask sl) 13029 (31232 + 32 * lim)
                (20480 + 256 * g) (20480 + 32 * w) (31232 + 32 * g) M)
              (callState s ret (wd 1 :: tail) M') (d * 784)) ∨
          (AccAt M' sl c (8 * lim) (accL c (8 * lim)).length ∧ (accL c (8 * lim)).length < 256 ∧
            Reach (gst s ret tail (64 * sl) (lmask sl) (nmask sl) 13029 (31232 + 32 * lim)
                (20480 + 256 * g) (20480 + 32 * w) (31232 + 32 * g) M)
              (gst s ret tail (64 * sl) (lmask sl) (nmask sl) 13565 (31232 + 32 * lim)
                (20480 + 256 * lim) (20480 + 32 * (accL c (8 * lim)).length) (31232 + 32 * lim) M')
              (d * 784 + 23)))
  | 0, g, w, M, hgd, hacc, hw, _, _ => by
    have hg : g = lim := by omega
    subst hg
    refine ⟨M, LaneFrame.refl _ _ _, Or.inr ⟨hacc.1 ▸ hacc, hacc.1 ▸ hw, ?_⟩⟩
    rw [← hacc.1]
    exact (fx_gl_ext (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) (31232 + 32 * g)
      (20480 + 256 * g) (20480 + 32 * w) (31232 + 32 * g) rfl (by omega) (by omega)).mono (by omega)
  | d + 1, g, w, M, hgd, hacc, hw, hcand, hflag => by
    obtain ⟨M1, w1, hA1, hL1, hr1⟩ := group_step (ret := ret) hs htail hsz hsl c (31232 + 32 * lim) g w M
      (by omega) (by omega) (by omega) hacc
      (fun i hi => hcand (8 * g + i) (by omega) (by omega)) (hflag g (le_refl _) (by omega))
    have hmono : 8 * g + 8 ≤ 8 * lim := by omega
    by_cases hdone : 256 ≤ w1
    · have hd := fx_done (ret := ret) hs htail hsz M1 (64 * sl) (lmask sl) (nmask sl)
        (31232 + 32 * lim) (20480 + 256 * (g + 1)) (20480 + 32 * w1) (31232 + 32 * g) (by omega)
        (by omega) (by have := hA1.1 ▸ accL_length_le c (8 * g + 8); omega) hj hret
      refine ⟨M1, hL1.mono hmono, Or.inl ⟨?_, fun i hi => ?_, (hr1.trans hd).mono (by
        rw [Nat.succ_mul]; omega)⟩⟩
      · have := accL_mono_length c hmono; have := hA1.1; omega
      · rw [hA1.2 i (by omega), accL_prefix c hmono (by rw [← hA1.1]; omega)]
    · have hn := fx_next (ret := ret) hs htail hsz M1 (64 * sl) (lmask sl) (nmask sl)
        (31232 + 32 * lim) (20480 + 256 * (g + 1)) (20480 + 32 * w1) (31232 + 32 * g) (by omega)
        (by omega)
      rw [show 32 + (31232 + 32 * g) = 31232 + 32 * (g + 1) by omega] at hn
      have hfr : ∀ g', g + 1 ≤ g' → g' < lim →
          word M1 (31232 + 32 * g') = word M (31232 + 32 * g') := fun g' _ _ =>
        hL1.1.word (by simp only [avoids_cons, avoids_nil, and_true]; omega)
      obtain ⟨M2, hL2, hres⟩ := phase hs htail hsz hj hret hsl c lim hlim d (g + 1) w1 M1 (by omega)
        (by rw [show 8 * (g + 1) = 8 * g + 8 by omega]; exact hA1) (by omega)
        (fun t h1 h2 => by
          rw [hL1.word_hi (show 8 * g + 8 ≤ t by omega)]; exact hcand t (by omega) h2)
        (fun g' h1 h2 => by rw [hfr g' h1 h2]; exact hflag g' (by omega) h2)
      refine ⟨M2, hL1.trans hL2 hmono, ?_⟩
      rcases hres with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, ((hr1.trans hn).trans h3).mono (by rw [Nat.succ_mul]; omega)⟩
      · exact Or.inr ⟨h1, h2, ((hr1.trans hn).trans h3).mono (by rw [Nat.succ_mul]; omega)⟩

end MlDsaOpt44.Proofs.Fix
