import MlDsaOptGlam44.Fn.Blk
import MlDsaOptGlam44.Fn.Keccak
import MlDsaOpt44.Math.SlotHead
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Squeeze.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The five squeezes of a SIMD group (`group`, WP C)

`SqInv m M I b`: after `b` rounds of `kf4` + `blk b'` (`blkh` for `b' = 4`)
the `KS` state is `permN b` of the seed states `I`, the candidate/flag words
of blocks `b' < b` below candidate 256 / flag word 32 are in `ABUF` / `FL`,
`HAVE6 = 0`, the iota table is intact and only the group's scratch regions
changed since `m`.
-/

namespace MlDsaOptGlam44.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

/-- Regions a group writes (`groupFrame` of `Fn/Group.lean`). -/
def gsFrame : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800)]

/-- Close `Avoids rs lo hi` for literal layout ranges. -/
macro "grp_avoids" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    and_true, MlDsaOptGlam44.Proofs.GroupP.gsFrame, KS, KB, RC4, HAVE6, ABUF, FL, ZH, ACC, RHO1, BK]
  omega))

theorem FrameExcept.of_avoid {m m' : ByteArray} {rs rs' : List (Nat × Nat)} (h : FrameExcept m m' rs)
    (hs : ∀ a, (∀ r ∈ rs', a < r.1 ∨ r.2 ≤ a) → ∀ r ∈ rs, a < r.1 ∨ r.2 ≤ a) :
    FrameExcept m m' rs' :=
  fun a ha => h a (hs a ha)

/-- Close the side goal of `FrameExcept.of_avoid` for literal layout ranges. -/
macro "grp_sub" : tactic => `(tactic| (
  intro a ha
  simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil, IsEmpty.forall_iff,
    forall_const, implies_true, and_true, MlDsaOptGlam44.Proofs.GroupP.gsFrame, KS, KB, RC4, HAVE6, ABUF, FL,
    ZH, ACC, RHO1, BK] at ha ⊢
  omega))

def SqInv (m M : ByteArray) (I : Nat → Fips202.SpongeState) (b : Nat) : Prop :=
  KS4 M (fun k => permN b (I k)) ∧ RC4Table M ∧ word M HAVE6 = 0 ∧ FrameExcept m M gsFrame ∧
  ∀ b', b' < b →
    (∀ i, i < 56 → b' * 56 + i < 256 →
      word M (ABUF + 1792 * b' + 32 * i) = pack4 fun k => cand (permN (b' + 1) (I k)) i) ∧
    (∀ g, g < 7 → b' * 7 + g < 32 →
      word M (FL + 224 * b' + 32 * g) = flagWord (fun k => permN (b' + 1) (I k)) g)

set_option linter.unusedVariables false in  -- glam: trivial table
theorem rc4_frame {M M' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept M M' rs)
    (ha : ∀ i, i < 24 → Avoids rs (RC4 + 32 * i) (RC4 + 32 * i + 32)) (hrc : RC4Table M) :
    RC4Table M' := trivial  -- glam: no iota table

theorem ks4_frame {M M' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept M M' rs)
    (ha : ∀ x, x < 25 → Avoids rs (KS + 32 * x) (KS + 32 * x + 32)) {S : Nat → Fips202.SpongeState}
    (hks : KS4 M S) : KS4 M' S := fun x hx => by rw [FrameExcept.word h (ha x hx)]; exact hks x hx

/-- Glue: the base stack of `group`'s body. -/
abbrev gB (col ret : Nat) (tail : List UInt256) : List UInt256 := wd 15 :: wd col :: wd 0 :: wd ret :: tail

/-- `kf4` of round `b` from an invariant at `b`. -/
theorem squeeze_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {col b : Nat} (hb : b < 5) {m M : ByteArray}
    {I : Nat → Fips202.SpongeState} (hI : Sized4 I) (hinv : SqInv m M I b)
    (hjK : Decode.isValidJumpDest optBytecode (20925 + 22 * b) = true) :
    ∃ M1, KS4 M1 (fun k => permN (b + 1) (I k)) ∧ FrameExcept M M1 [(KS, KS + 800), (KB, KB + 800)] ∧
      Call s Entry.kf4 [] (20925 + 22 * b) (gB col ret tail) M [] M1 Gas.kf4 := by
  obtain ⟨hks, hrc, -, -, -⟩ := hinv
  obtain ⟨M1, hk1, hf1, hc1⟩ := kf4_call hs (hr.callee (B' := Stack.kf4) (ret' := 20925 + 22 * b)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    hjK (by omega)) M hrc
  have hS : Sized4 fun k => permN b (I k) := fun k hk => permN_size (hI k hk) b
  have e : (fun k => permN (b + 1) (I k)) = fun k => EvmSemantics.Crypto.Keccak.permute (permN b (I k)) :=
    funext fun k => permN_succ b (I k)
  exact ⟨M1, by rw [e]; exact hk1 _ hS hks, hf1, hc1⟩

/-- One round `kf4` + `blk` (`b < 4`). -/
theorem squeeze_step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {col b : Nat} (hb : b < 4) {m M : ByteArray}
    {I : Nat → Fips202.SpongeState} (hI : Sized4 I) (hinv : SqInv m M I b)
    (hK : Reach (callState s (20917 + 22 * b) (gB col ret tail) M)
      (callState s 42887 (wd (20925 + 22 * b) :: gB col ret tail) M) 15)
    (hL : ∀ M, Reach (callState s (20925 + 22 * b) (gB col ret tail) M)
      (callState s 10481 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (20939 + 22 * b) ::
        gB col ret tail) M) 21)
    (hjK : Decode.isValidJumpDest optBytecode (20925 + 22 * b) = true)
    (hjL : Decode.isValidJumpDest optBytecode (20939 + 22 * b) = true) :
    ∃ M', SqInv m M' I (b + 1) ∧
      Reach (callState s (20917 + 22 * b) (gB col ret tail) M)
        (callState s (20917 + 22 * (b + 1)) (gB col ret tail) M') (36 + Gas.kf4 + Gas.blk) := by
  obtain ⟨M1, hks1, hf1, hc1⟩ := squeeze_kf4 hs hr (col := col) (by omega) hI hinv hjK
  obtain ⟨-, hrc, h6, hfr, hblocks⟩ := hinv
  have hS1 : Sized4 fun k => permN (b + 1) (I k) := fun k hk => permN_size (hI k hk) (b + 1)
  obtain ⟨M2, hb2, hf2, hc2⟩ := blk_call hs (hr.callee (B' := Stack.blk) (ret' := 20939 + 22 * b)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    hjL (by omega)) M1 (abp := ABUF + 1792 * b) (flp := FL + 224 * b)
    (by unfold KS ABUF; omega) (by unfold ABUF TOP; omega) (by unfold KS FL; omega)
    (by unfold FL TOP; omega) (by unfold ABUF FL; omega)
  obtain ⟨hA, hF⟩ := hb2 _ hS1 hks1
  refine ⟨M2, ⟨ks4_frame hf2 (fun x hx => by grp_avoids) hks1,
    rc4_frame hf2 (fun i hi => by grp_avoids) (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
    ?_, ?_, ?_⟩, ?_⟩
  · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact h6
  · exact FrameExcept.of_avoid (hfr.trans (hf1.trans hf2)) (by grp_sub)
  · intro b' hb'
    by_cases hbb : b' = b
    · subst hbb; exact ⟨fun i hi _ => hA i hi, fun g hg _ => hF g hg⟩
    · obtain ⟨hA', hF'⟩ := hblocks b' (by omega)
      refine ⟨fun i hi hi' => ?_, fun g hg hg' => ?_⟩
      · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]
        exact hA' i hi hi'
      · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]
        exact hF' g hg hg'
  · have h := hK.trans ((call_iff.mp hc1).trans ((hL M1).trans (call_iff.mp hc2)))
    rw [show 20917 + 22 * (b + 1) = 20939 + 22 * b by ring]
    exact h.mono (by omega)

/-- Rounds `0 … n − 1` (`n ≤ 4`). -/
theorem squeezes {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {col : Nat} {m M0 : ByteArray}
    {I : Nat → Fips202.SpongeState} (hI : Sized4 I) (hinv : SqInv m M0 I 0)
    (hK : ∀ b, b < 5 → ∀ M, Reach (callState s (20917 + 22 * b) (gB col ret tail) M)
      (callState s 42887 (wd (20925 + 22 * b) :: gB col ret tail) M) 15)
    (hL : ∀ b, b < 4 → ∀ M, Reach (callState s (20925 + 22 * b) (gB col ret tail) M)
      (callState s 10481 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (20939 + 22 * b) ::
        gB col ret tail) M) 21)
    (hjK : ∀ b, b < 5 → Decode.isValidJumpDest optBytecode (20925 + 22 * b) = true)
    (hjL : ∀ b, b < 4 → Decode.isValidJumpDest optBytecode (20939 + 22 * b) = true) :
    ∀ n, n ≤ 4 → ∃ M', SqInv m M' I n ∧
      Reach (callState s 20917 (gB col ret tail) M0)
        (callState s (20917 + 22 * n) (gB col ret tail) M') (n * (36 + Gas.kf4 + Gas.blk))
  | 0, _ => ⟨M0, hinv, (Reach.refl _).of_eq rfl rfl⟩
  | n + 1, hn => by
    obtain ⟨M', hinv', hR⟩ := squeezes hs hr hI hinv hK hL hjK hjL n (by omega)
    obtain ⟨M'', hinv'', hR'⟩ := squeeze_step hs hr (by omega) hI hinv' (hK n (by omega) M')
      (hL n (by omega)) (hjK n (by omega)) (hjL n (by omega))
    exact ⟨M'', hinv'', (hR.trans hR').mono (by rw [Nat.succ_mul])⟩

/-- Round 4: `kf4` + `blkh`. -/
theorem squeeze_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {col : Nat} {m M : ByteArray}
    {I : Nat → Fips202.SpongeState} (hI : Sized4 I) (hinv : SqInv m M I 4)
    (hK : Reach (callState s (20917 + 22 * 4) (gB col ret tail) M)
      (callState s 42887 (wd (20925 + 22 * 4) :: gB col ret tail) M) 15)
    (hL : ∀ M, Reach (callState s (20925 + 22 * 4) (gB col ret tail) M)
      (callState s 10487 (wd (FL + 224 * 4) :: wd (ABUF + 1792 * 4) :: wd 21027 ::
        gB col ret tail) M) 21)
    (hjK : Decode.isValidJumpDest optBytecode (20925 + 22 * 4) = true)
    (hjL : Decode.isValidJumpDest optBytecode 21027 = true) :
    ∃ M', SqInv m M' I 5 ∧
      Reach (callState s (20917 + 22 * 4) (gB col ret tail) M)
        (callState s 21027 (gB col ret tail) M') (36 + Gas.kf4 + Gas.blkh) := by
  obtain ⟨M1, hks1, hf1, hc1⟩ := squeeze_kf4 hs hr (col := col) (b := 4) (by omega) hI hinv hjK
  obtain ⟨-, hrc, h6, hfr, hblocks⟩ := hinv
  have hS1 : Sized4 fun k => permN (4 + 1) (I k) := fun k hk => permN_size (hI k hk) (4 + 1)
  obtain ⟨M2, hb2, hf2, hc2⟩ := blkh_call hs (hr.callee (B' := Stack.blk) (ret' := 21027)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    hjL (by omega)) M1 (abp := ABUF + 1792 * 4) (flp := FL + 224 * 4)
    (by unfold KS ABUF; omega) (by unfold ABUF TOP; omega) (by unfold KS FL; omega)
    (by unfold FL TOP; omega) (by unfold ABUF FL; omega)
  obtain ⟨hA, hF⟩ := hb2 _ hS1 hks1
  refine ⟨M2, ⟨ks4_frame hf2 (fun x hx => by grp_avoids) hks1,
    rc4_frame hf2 (fun i hi => by grp_avoids) (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
    ?_, ?_, ?_⟩, ?_⟩
  · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact h6
  · exact FrameExcept.of_avoid (hfr.trans (hf1.trans hf2)) (by grp_sub)
  · intro b' hb'
    by_cases hbb : b' = 4
    · subst hbb; exact ⟨fun i _ hi' => hA i (by omega), fun g _ hg' => hF g (by omega)⟩
    · obtain ⟨hA', hF'⟩ := hblocks b' (by omega)
      refine ⟨fun i hi hi' => ?_, fun g hg hg' => ?_⟩
      · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]
        exact hA' i hi hi'
      · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]
        exact hF' g hg hg'
  · exact (hK.trans ((call_iff.mp hc1).trans ((hL M1).trans (call_iff.mp hc2)))).mono (by omega)

end MlDsaOptGlam44.Proofs.GroupP
