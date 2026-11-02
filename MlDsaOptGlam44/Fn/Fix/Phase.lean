import MlDsaOptGlam44.Fn.Fix.Loop
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/Phase.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# `fix`: one group and one phase of the group loop (v4)

The loop head `fxg` (pc 20355) holds `wp :: rp :: rlim :: …`; a visit runs one
group (flag test, eight flagged steps or eight masked copies) and the test at
`fxn` (pc 20513): continue while `wp < END256` and `rp < rlim`, return `1` once
256 coefficients are written, else go to the exhaustion test `fxe` (pc 20716).
A visit costs at most 580 (a flagged group and the exit to `fxe`); the return
path costs 20 more.
-/

namespace MlDsaOptGlam44.Proofs.Fix

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Fix

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

set_option maxRecDepth 10000

/-- The flag mask of lane `sl` (`2^23 << 64 sl`). -/
def fmv (sl : Nat) : Nat := 8388608 * 2 ^ (64 * sl)

theorem fmv_and (sl W : Nat) : fmv sl &&& W = 0 ↔ W / 2 ^ (23 + 64 * sl) % 2 = 0 := by
  have h : fmv sl = 2 ^ (23 + 64 * sl) := by unfold fmv; rw [pow_add]; norm_num
  have hb := Nat.testBit_eq_decide_div_mod_eq (x := W) (i := 23 + 64 * sl)
  rw [h]
  constructor
  · intro h0
    have := congrArg (fun x => x.testBit (23 + 64 * sl)) h0
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.true_and, Nat.zero_testBit] at this
    rw [this] at hb
    simp only [Bool.false_eq, decide_eq_false_iff_not] at hb
    omega
  · intro h0
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : 23 + 64 * sl = j
    · subst hj; rw [hb]; simp [h0]
    · simp [hj]

theorem flag_addr (g : Nat) : 28672 + (20480 + 256 * g) / 8 = 31232 + 32 * g := by omega

/-- Loop layout of slot `sl`. -/
abbrev G (s : State) (ret : Nat) (tail : List UInt256) (sl pc rlim rp wp : Nat) (M : ByteArray) :
    State :=
  gst s ret tail (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl) pc rlim rp wp M

theorem qsv_lt {sl : Nat} (hsl : sl < 4) : qsv sl < 2 ^ 256 := by
  have := qs_lt (64 * sl) (by omega); unfold qsv; norm_num; exact this

/-- One group: from `fxg` to `fxn`. -/
theorem group_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat) {sl : Nat} (hsl : sl < 4)
    (c : Nat → Nat) (rlim g w : Nat) (M : ByteArray) (hg : g < 42) (hacc : AccAt M sl c (8 * g) w)
    (hcand : ∀ i, i < 8 → lane (word M (20480 + 32 * (8 * g + i))) sl = c (8 * g + i))
    (hflag : word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = F c g) :
    ∃ M' w', AccAt M' sl c (8 * g + 8) w' ∧ LaneFrame M M' sl (8 * g + 8) ∧
      Reach (G s ret tail sl 20355 rlim (20480 + 256 * g) (20480 + 32 * w) M)
        (G s ret tail sl 20513 rlim (20480 + 256 * g) (20480 + 32 * w') M') 500 := by
  have hwle : w ≤ 8 * g := hacc.1 ▸ accL_length_le c _
  have hb : word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = 0 ∨
      word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = 1 := by omega
  rcases hb with hb | hb
  · -- clean group
    have hq := F_zero (hflag ▸ hb)
    have h1 := fx_gl_clean (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
      rlim (20480 + 256 * g) (20480 + 32 * w) (by omega) (by rw [flag_addr, fmv_and]; exact hb)
    have h2 := clean_reach (ret := ret) hs htail hsz (sl := sl) (64 * sl) (qsv sl) (fmv sl) rlim M
      (20480 + 256 * g) (20480 + 32 * w) (by omega) (by omega)
    rw [show 256 + (20480 + 32 * w) = 20480 + 32 * (w + 8) by omega] at h2
    obtain ⟨hA, hL⟩ := cwN_inv hsl c g w M hacc hcand hq 8 (le_refl _)
    exact ⟨_, w + 8, hA, hL, (h1.trans h2).mono (by omega)⟩
  · -- flagged group
    have h1 := fx_gl_flag (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
      rlim (20480 + 256 * g) (20480 + 32 * w) (by omega)
      (by rw [flag_addr]; intro h0; rw [(fmv_and sl _).mp h0] at hb; exact absurd hb (by decide))
    have h2 := flagged_reach (ret := ret) hs htail hsz (sl := sl) (64 * sl) (fmv sl) rlim M
      (20480 + 256 * g) (20480 + 32 * w) (qsv_lt hsl) (by omega) (by omega)
    obtain ⟨wn, hwn, hA, hL⟩ := fsN_inv hsl c g w M hacc hcand 8 (le_refl _)
    rw [hwn] at h2
    exact ⟨_, wn, hA, hL, h1.trans h2⟩

/-- A phase of the group loop, from group `g` up to `lim`: either 256
coefficients are accepted (return `1`), or the loop reaches the exhaustion
test `fxe` with fewer. -/
theorem phase {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 65536)
    {sl : Nat} (hsl : sl < 4) (c : Nat → Nat) (lim : Nat) (hlim : lim ≤ 42) :
    ∀ d g w (M : ByteArray), g + d = lim → 0 < d → AccAt M sl c (8 * g) w → w < 256 →
      (∀ t, 8 * g ≤ t → t < 8 * lim → lane (word M (20480 + 32 * t)) sl = c t) →
      (∀ g', g ≤ g' → g' < lim → word M (31232 + 32 * g') / 2 ^ (23 + 64 * sl) % 2 = F c g') →
      ∃ M', LaneFrame M M' sl (8 * lim) ∧
        ((256 ≤ (accL c (8 * lim)).length ∧
            (∀ i, i < 256 → lane (word M' (20480 + 32 * i)) sl = (accL c (8 * lim))[i]!) ∧
            Reach (G s ret tail sl 20355 (20480 + 256 * lim) (20480 + 256 * g) (20480 + 32 * w) M)
              (callState s ret (wd 1 :: tail) M') (d * 580 + 20)) ∨
          (AccAt M' sl c (8 * lim) (accL c (8 * lim)).length ∧ (accL c (8 * lim)).length < 256 ∧
            Reach (G s ret tail sl 20355 (20480 + 256 * lim) (20480 + 256 * g) (20480 + 32 * w) M)
              (G s ret tail sl 20716 (20480 + 256 * lim) (20480 + 256 * lim)
                (20480 + 32 * (accL c (8 * lim)).length) M') (d * 580)))
  | 0, _, _, _, _, hd, _, _, _, _ => absurd hd (by omega)
  | d + 1, g, w, M, hgd, _, hacc, hw, hcand, hflag => by
    obtain ⟨M1, w1, hA1, hL1, hr1⟩ := group_body (ret := ret) hs htail hsz hsl c
      (20480 + 256 * lim) g w M (by omega) hacc
      (fun i hi => hcand (8 * g + i) (by omega) (by omega)) (hflag g (le_refl _) (by omega))
    have hmono : 8 * g + 8 ≤ 8 * lim := by omega
    have hw1 : w1 ≤ 8 * g + 8 := hA1.1 ▸ accL_length_le c _
    by_cases hdone : 256 ≤ w1
    · have hd := fx_gn_done (ret := ret) hs htail hsz M1 (64 * sl) (lmask sl) (nmask sl) (qsv sl)
        (fmv sl) (20480 + 256 * lim) (20480 + 256 * g) (20480 + 32 * w1) (by omega) (by omega)
        (by omega) (by omega) hj hret
      refine ⟨M1, hL1.mono hmono, Or.inl ⟨?_, fun i hi => ?_, (hr1.trans hd).mono (by
        rw [Nat.succ_mul]; omega)⟩⟩
      · have := accL_mono_length c hmono; have := hA1.1; omega
      · rw [hA1.2 i (by omega), accL_prefix c hmono (by rw [← hA1.1]; omega)]
    · by_cases hd0 : d = 0
      · subst hd0
        have hlim' : lim = g + 1 := by omega
        subst hlim'
        have he := fx_gn_ext (ret := ret) hs htail hsz M1 (64 * sl) (lmask sl) (nmask sl) (qsv sl)
          (fmv sl) (20480 + 256 * (g + 1)) (20480 + 256 * g) (20480 + 32 * w1) (by omega) (by omega)
          (by omega) (by omega)
        rw [show 256 + (20480 + 256 * g) = 20480 + 256 * (g + 1) by omega] at he
        have hA1' : AccAt M1 sl c (8 * (g + 1)) w1 := by
          rw [show 8 * (g + 1) = 8 * g + 8 by omega]; exact hA1
        refine ⟨M1, hL1.mono (by omega), Or.inr ⟨hA1'.1 ▸ hA1', by rw [← hA1'.1]; omega, ?_⟩⟩
        rw [← hA1'.1]
        exact (hr1.trans he).mono (by omega)
      · have hn := fx_gn_cont (ret := ret) hs htail hsz M1 (64 * sl) (lmask sl) (nmask sl) (qsv sl)
          (fmv sl) (20480 + 256 * lim) (20480 + 256 * g) (20480 + 32 * w1) (by omega) (by omega)
          (by omega) (by omega)
        rw [show 256 + (20480 + 256 * g) = 20480 + 256 * (g + 1) by omega] at hn
        have hfr : ∀ g', g + 1 ≤ g' → g' < lim →
            word M1 (31232 + 32 * g') = word M (31232 + 32 * g') := fun g' _ _ =>
          hL1.1.word (by simp only [avoids_cons, avoids_nil, and_true]; omega)
        obtain ⟨M2, hL2, hres⟩ := phase hs htail hsz hj hret hsl c lim hlim d (g + 1) w1 M1 (by omega)
          (by omega) (by rw [show 8 * (g + 1) = 8 * g + 8 by omega]; exact hA1) (by omega)
          (fun t h1 h2 => by
            rw [hL1.word_hi (show 8 * g + 8 ≤ t by omega)]; exact hcand t (by omega) h2)
          (fun g' h1 h2 => by rw [hfr g' h1 h2]; exact hflag g' (by omega) h2)
        refine ⟨M2, hL1.trans hL2 hmono, ?_⟩
        rcases hres with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact Or.inl ⟨h1, h2, ((hr1.trans hn).trans h3).mono (by rw [Nat.succ_mul]; omega)⟩
        · exact Or.inr ⟨h1, h2, ((hr1.trans hn).trans h3).mono (by rw [Nat.succ_mul]; omega)⟩

end MlDsaOptGlam44.Proofs.Fix
