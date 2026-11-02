import MlDsaOptGlam87.Fn.Fix.Blocks
import MlDsaOpt44.Fn.Fix.Lane
import MlDsaOpt44.Fn.Fix.Rej
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Fix/Loop.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Fix/Loop.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`G`/`cst`/`(pc := _)`/`(ret := _)`/`(rT := _)`/`(rF := _)` and the `reach_mcopy` index relocated by hand (`proofgen_port.maps 87`)
set_option warningAsError true
/-!
# `fix`: the group loop

One phase of the group loop (`fxg`, pc 19921) runs groups `g … lim − 1`
(`lim = 35` before the sixth squeeze, `42` after). The invariant: lane `sl`
of `ABUF[0, w)` is the accepted list `accL c (8 g)` (`AccAt`), the unread
positions `[8 g, 8 lim)` still hold the candidates, and only lane `sl` of
`ABUF[0, 8 g)` has changed (`LaneFrame`). A flagged group writes every
candidate at `w` (masked lane copy, as a clean group does) and advances `w`
on acceptance only. Addresses are literal: `ABUF = 20480`, `FL = 31232`.
-/

namespace MlDsaOptGlam87.Proofs.Fix

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs.Fix
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-! ## Lane-only writes -/

/-- `M'` differs from `M` only in lane `sl` of `ABUF[0, hi)`. -/
def LaneFrame (M M' : ByteArray) (sl hi : Nat) : Prop :=
  FrameExcept M M' [(20480, 20480 + 32 * hi)] ∧
    ∀ t k, k < 4 → k ≠ sl → lane (word M' (20480 + 32 * t)) k = lane (word M (20480 + 32 * t)) k

theorem LaneFrame.refl (M : ByteArray) (sl hi : Nat) : LaneFrame M M sl hi :=
  ⟨FrameExcept.refl _ _, fun _ _ _ _ => rfl⟩

theorem LaneFrame.trans {M₁ M₂ M₃ : ByteArray} {sl h h' : Nat} (a : LaneFrame M₁ M₂ sl h)
    (b : LaneFrame M₂ M₃ sl h') (hh : h ≤ h') : LaneFrame M₁ M₃ sl h' := by
  refine ⟨(a.1.trans b.1).mono ?_, fun t k hk hks => by rw [b.2 t k hk hks, a.2 t k hk hks]⟩
  intro r hr
  refine ⟨(20480, 20480 + 32 * h'), List.mem_singleton_self _, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

theorem LaneFrame.mono {M M' : ByteArray} {sl h h' : Nat} (a : LaneFrame M M' sl h) (hh : h ≤ h') :
    LaneFrame M M' sl h' :=
  (LaneFrame.refl M sl 0).trans a (Nat.zero_le _) |>.trans (LaneFrame.refl M' sl h') hh

theorem LaneFrame.word_hi {M M' : ByteArray} {sl h t : Nat} (a : LaneFrame M M' sl h)
    (ht : h ≤ t) : word M' (20480 + 32 * t) = word M (20480 + 32 * t) :=
  a.1.word (by simp only [avoids_cons, avoids_nil, and_true]; omega)

theorem word_put (M : ByteArray) {V : Nat} (hV : V < 2 ^ 256) (j t : Nat) :
    word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded V 32) (20480 + 32 * j))
      (20480 + 32 * t) = if t = j then V else word M (20480 + 32 * t) := by
  split
  · subst t; exact word_mstore _ _ _ hV
  · exact word_mstore_disjoint _ _ (by omega)

theorem laneFrame_put (M : ByteArray) {V sl j hi : Nat} (hV : V < 2 ^ 256)
    (hl : ∀ k, k < 4 → k ≠ sl → lane V k = lane (word M (20480 + 32 * j)) k) (hj : j < hi) :
    LaneFrame M (MachineState.writeBytes M (Data.Bytes.natToBytesPadded V 32) (20480 + 32 * j))
      sl hi := by
  refine ⟨(FrameExcept.mstore _ _ _).mono ?_, fun t k hk hks => ?_⟩
  · intro r hr
    refine ⟨(20480, 20480 + 32 * hi), List.mem_singleton_self _, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; constructor <;> simp only <;> omega
  · rw [word_put M hV]
    split
    · subst t; exact hl k hk hks
    · rfl

/-! ## The accepted prefix -/

/-- Lane `sl` of `ABUF[0, w)` is the accepted list of the first `n` candidates. -/
def AccAt (M : ByteArray) (sl : Nat) (c : Nat → Nat) (n w : Nat) : Prop :=
  w = (accL c n).length ∧ ∀ i, i < w → lane (word M (20480 + 32 * i)) sl = (accL c n)[i]!

/-- Flag of group `g` of a candidate stream. -/
def F (c : Nat → Nat) (g : Nat) : Nat :=
  if (List.range 8).any (fun i => decide (Fips204.q ≤ c (8 * g + i))) then 1 else 0

theorem F_zero {c : Nat → Nat} {g : Nat} (h : F c g = 0) : ∀ i, i < 8 → c (8 * g + i) < Fips204.q := by
  intro i hi
  unfold F at h
  split at h
  · exact absurd h (by decide)
  · rename_i hh
    simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq, not_exists, not_and,
      Nat.not_le] at hh
    exact hh i hi

/-- Acceptance bit of a lane value. -/
def ab (v : Nat) : Nat := if 8380417 > v then 1 else 0

/-- Acceptance of one candidate (the bytecode's `q > v`). -/
theorem accept_step {M M' : ByteArray} {sl : Nat} {c : Nat → Nat} {n w : Nat} {v : Nat}
    (hacc : AccAt M sl c n w) (hv : v = c n) {V : Nat} (hV : V < 2 ^ 256)
    (hM' : M' = MachineState.writeBytes M (Data.Bytes.natToBytesPadded V 32) (20480 + 32 * w))
    (hVl : lane V sl = v) :
    AccAt M' sl c (n + 1) (w + ab v) := by
  obtain ⟨hw, hpre⟩ := hacc
  subst hM'
  unfold ab AccAt
  by_cases hq : c n < Fips204.q
  · have hq' : 8380417 > v := by rw [hv]; exact hq
    rw [if_pos hq', accL_succ_acc hq]
    refine ⟨by simp [hw], fun i hi => ?_⟩
    rw [word_put M hV]
    split
    · subst i; rw [hVl, hv, ← accL_succ_acc hq, hw, accL_last c hq]
    · rw [hpre i (by omega)]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (show i < (accL c n).length by omega)]
  · have hq' : ¬ 8380417 > v := by rw [hv]; exact hq
    rw [if_neg hq', accL_succ_rej hq, Nat.add_zero]
    refine ⟨hw, fun i hi => ?_⟩
    rw [word_put M hV, if_neg (by omega)]
    exact hpre i hi

/-! ## The lane test of the flagged path -/

/-- `q << 64 sl`, the flagged path's acceptance bound. -/
def qsv (sl : Nat) : Nat := 8380417 * 2 ^ (64 * sl)

theorem land_lmask (sl W : Nat) :
    lmask sl &&& W = lane W sl * 2 ^ (64 * sl) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, lmask_bit, Nat.testBit_mul_two_pow, testBit_lane]
  by_cases h1 : 64 * sl ≤ j
  · by_cases h2 : j < 64 * sl + 64
    · simp [h1, h2, show j - 64 * sl < 64 by omega, show 64 * sl + (j - 64 * sl) = j by omega]
    · simp [h1, h2, show ¬ j - 64 * sl < 64 by omega]
  · simp [h1]

theorem acc_eq (sl W : Nat) :
    acc (qsv sl) (lmask sl &&& W) = ab (lane W sl) := by
  unfold acc ab qsv
  rw [land_lmask]
  have hp : 0 < 2 ^ (64 * sl) := by positivity
  by_cases h : 8380417 > lane W sl
  · rw [if_pos (Nat.mul_lt_mul_of_pos_right h hp), if_pos h]
  · rw [if_neg (fun h' => h (Nat.lt_of_mul_lt_mul_right h')), if_neg h]

/-! ## Flagged groups: eight branch-free steps -/

/-- One flagged step: the masked write at `wp` and the pointer update. -/
def fs (sl rp : Nat) (p : ByteArray × Nat) (i : Nat) : ByteArray × Nat :=
  (cw p.1 p.2 (32 * i + rp) (lmask sl) (nmask sl),
    p.2 + acc (qsv sl) (lmask sl &&& word p.1 (32 * i + rp)) * 32)

def fsN (sl rp : Nat) (p : ByteArray × Nat) : Nat → ByteArray × Nat
  | 0 => p
  | n + 1 => fs sl rp (fsN sl rp p n) n

theorem acc_le (qs v : Nat) : acc qs v ≤ 1 := by unfold acc; split <;> omega

theorem fsN_le (sl rp : Nat) (p : ByteArray × Nat) : ∀ n, (fsN sl rp p n).2 ≤ p.2 + 32 * n
  | 0 => by simp [fsN]
  | n + 1 => by
    have := fsN_le sl rp p n
    have := acc_le (qsv sl) (lmask sl &&& word (fsN sl rp p n).1 (32 * n + rp))
    simp only [fsN, fs]; omega

theorem flagged_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat) {sl : Nat}
    (sh fm rlim : Nat) (M : ByteArray) (rp wp : Nat) (hqs : qsv sl < 2 ^ 256) (hrp : rp + 256 ≤ 91680)
    (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh (lmask sl) (nmask sl) (qsv sl) fm 20112 rlim rp wp M)
      (gst s ret tail sh (lmask sl) (nmask sl) (qsv sl) fm 20079 rlim rp (fsN sl rp (M, wp) 8).2
        (fsN sl rp (M, wp) 8).1) 462 := by
  have b := fun i => fsN_le sl rp (M, wp) i
  simp only at b
  have h0 := fx_cand0 (ret := ret) hs htail hsz M sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp wp hqs hrp (by omega)
  have h1 := fx_cand1 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 1).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 1).2 hqs hrp (by have := b 1; omega)
  have h2 := fx_cand2 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 2).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 2).2 hqs hrp (by have := b 2; omega)
  have h3 := fx_cand3 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 3).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 3).2 hqs hrp (by have := b 3; omega)
  have h4 := fx_cand4 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 4).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 4).2 hqs hrp (by have := b 4; omega)
  have h5 := fx_cand5 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 5).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 5).2 hqs hrp (by have := b 5; omega)
  have h6 := fx_cand6 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 6).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 6).2 hqs hrp (by have := b 6; omega)
  have h7 := fx_cand7 (ret := ret) hs htail hsz (fsN sl rp (M, wp) 7).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim rp
    (fsN sl rp (M, wp) 7).2 hqs hrp (by have := b 7; omega)
  have h8 := fx_ftail (ret := ret) hs htail hsz (fsN sl rp (M, wp) 8).1 sh (lmask sl) (nmask sl) (qsv sl) fm rlim
    rp (fsN sl rp (M, wp) 8).2
  exact ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8)

/-- Semantics of the flagged steps over the group at `8 g`. -/
theorem fsN_inv {sl : Nat} (hsl : sl < 4) (c : Nat → Nat) (g w : Nat) (M : ByteArray)
    (hacc : AccAt M sl c (8 * g) w)
    (hcand : ∀ i, i < 8 → lane (word M (20480 + 32 * (8 * g + i))) sl = c (8 * g + i)) :
    ∀ n, n ≤ 8 → ∃ wn, (fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) n).2 = 20480 + 32 * wn ∧
      AccAt (fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) n).1 sl c (8 * g + n) wn ∧
      LaneFrame M (fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) n).1 sl (8 * g + n)
  | 0, _ => ⟨w, rfl, hacc, LaneFrame.refl _ _ _⟩
  | n + 1, hn => by
    obtain ⟨wn, hwn, hA, hL⟩ := fsN_inv hsl c g w M hacc hcand n (by omega)
    have hwle : wn ≤ 8 * g + n := hA.1 ▸ accL_length_le c _
    set p := fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) n with hp
    have haddr : 32 * n + (20480 + 256 * g) = 20480 + 32 * (8 * g + n) := by omega
    have hv : lane (word p.1 (32 * n + (20480 + 256 * g))) sl = c (8 * g + n) := by
      rw [haddr, hL.word_hi (le_refl _)]; exact hcand n (by omega)
    have hVlt : ((lmask sl &&& word p.1 (32 * n + (20480 + 256 * g)) ||| nmask sl &&& word p.1 p.2) %
        2 ^ 256) < 2 ^ 256 := Nat.mod_lt _ (by positivity)
    have hfw : (fsN sl (20480 + 256 * g) (M, 20480 + 32 * w) (n + 1)).1 =
        MachineState.writeBytes p.1 (Data.Bytes.natToBytesPadded ((lmask sl &&&
          word p.1 (32 * n + (20480 + 256 * g)) ||| nmask sl &&& word p.1 p.2) % 2 ^ 256) 32)
          (20480 + 32 * wn) := by
      simp only [fsN, fs, cw, ← hp, hwn]; rfl
    refine ⟨wn + ab (c (8 * g + n)), ?_, ?_, ?_⟩
    · simp only [fsN, fs, ← hp, hwn, acc_eq, hv]; omega
    · rw [hfw, show 8 * g + (n + 1) = 8 * g + n + 1 by omega]
      exact accept_step hA rfl hVlt rfl (by rw [lane_cw hsl hsl, if_pos rfl, hv])
    · rw [hfw]
      refine hL.trans (laneFrame_put p.1 hVlt (fun k hk hks => ?_) (by omega)) (by omega)
      rw [lane_cw hsl hk, if_neg hks, hwn]

/-! ## Clean groups: eight masked copies -/

def cwN (sl rp wp : Nat) (M : ByteArray) : Nat → ByteArray
  | 0 => M
  | n + 1 => cw (cwN sl rp wp M n) (32 * n + wp) (32 * n + rp) (lmask sl) (nmask sl)

theorem clean_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat) {sl : Nat}
    (sh qs fm rlim : Nat) (M : ByteArray) (rp wp : Nat) (hrp : rp + 256 ≤ 91680)
    (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh (lmask sl) (nmask sl) qs fm 19937 rlim rp wp M)
      (gst s ret tail sh (lmask sl) (nmask sl) qs fm 20079 rlim rp (256 + wp) (cwN sl rp wp M 8)) 378 := by
  have h0 := fx_copy0 (ret := ret) hs htail hsz M sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h1 := fx_copy1 (ret := ret) hs htail hsz (cwN sl rp wp M 1) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h2 := fx_copy2 (ret := ret) hs htail hsz (cwN sl rp wp M 2) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h3 := fx_copy3 (ret := ret) hs htail hsz (cwN sl rp wp M 3) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h4 := fx_copy4 (ret := ret) hs htail hsz (cwN sl rp wp M 4) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h5 := fx_copy5 (ret := ret) hs htail hsz (cwN sl rp wp M 5) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h6 := fx_copy6 (ret := ret) hs htail hsz (cwN sl rp wp M 6) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h7 := fx_copy7 (ret := ret) hs htail hsz (cwN sl rp wp M 7) sh (lmask sl) (nmask sl) qs fm rlim rp wp hrp hwp
  have h8 := fx_ctail (ret := ret) hs htail hsz (cwN sl rp wp M 8) sh (lmask sl) (nmask sl) qs fm rlim rp wp
    (by omega)
  exact ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8)

theorem cwN_inv {sl : Nat} (hsl : sl < 4) (c : Nat → Nat) (g w : Nat) (M : ByteArray)
    (hacc : AccAt M sl c (8 * g) w)
    (hcand : ∀ i, i < 8 → lane (word M (20480 + 32 * (8 * g + i))) sl = c (8 * g + i))
    (hq : ∀ i, i < 8 → c (8 * g + i) < Fips204.q) :
    ∀ n, n ≤ 8 → AccAt (cwN sl (20480 + 256 * g) (20480 + 32 * w) M n) sl c (8 * g + n) (w + n) ∧
      LaneFrame M (cwN sl (20480 + 256 * g) (20480 + 32 * w) M n) sl (8 * g + n)
  | 0, _ => ⟨hacc, LaneFrame.refl _ _ _⟩
  | n + 1, hn => by
    obtain ⟨hA, hL⟩ := cwN_inv hsl c g w M hacc hcand hq n (by omega)
    have hwle : w + n ≤ 8 * g + n := hA.1 ▸ accL_length_le c _
    set p := cwN sl (20480 + 256 * g) (20480 + 32 * w) M n with hp
    have hr : lane (word p (20480 + 32 * (8 * g + n))) sl = c (8 * g + n) := by
      rw [hL.word_hi (le_refl _)]; exact hcand n (by omega)
    have hVlt : ((lmask sl &&& word p (20480 + 32 * (8 * g + n)) |||
        nmask sl &&& word p (20480 + 32 * (w + n))) % 2 ^ 256) < 2 ^ 256 := Nat.mod_lt _ (by positivity)
    have hcw : cwN sl (20480 + 256 * g) (20480 + 32 * w) M (n + 1) =
        MachineState.writeBytes p (Data.Bytes.natToBytesPadded ((lmask sl &&&
          word p (20480 + 32 * (8 * g + n)) ||| nmask sl &&& word p (20480 + 32 * (w + n))) % 2 ^ 256) 32)
          (20480 + 32 * (w + n)) := by
      simp only [cwN, cw, ← hp]
      rw [show 32 * n + (20480 + 256 * g) = 20480 + 32 * (8 * g + n) by omega,
        show 32 * n + (20480 + 32 * w) = 20480 + 32 * (w + n) by omega]
      rfl
    have hab : ab (c (8 * g + n)) = 1 := by
      unfold ab; rw [if_pos (show 8380417 > c (8 * g + n) from hq n (by omega))]
    refine ⟨?_, ?_⟩
    · rw [hcw, show 8 * g + (n + 1) = 8 * g + n + 1 by omega, show w + (n + 1) = w + n + ab (c (8 * g + n)) by
        rw [hab]; omega]
      exact accept_step hA rfl hVlt rfl (by rw [lane_cw hsl hsl, if_pos rfl, hr])
    · rw [hcw]
      refine hL.trans (laneFrame_put p hVlt (fun k hk hks => ?_) (by omega)) (by omega)
      rw [lane_cw hsl hk, if_neg hks]

end MlDsaOptGlam87.Proofs.Fix
