import MlDsaOpt87.Fn.Keccak
import MlDsaOpt87.Fn.Blk
import MlDsaOpt44.Math.SpongeBytes
import MlDsaOpt87.Fn.Group.Common
import MlDsaOpt87.Fn.Group.Defs
/- Ported from `MlDsaOpt44/Fn/Group/Squeeze.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
-- port: `gB` carries `amask col rb`; the return pcs of the five squeezes are 15291 + 22 b (kf4) / 15299 + 22 b (blk)
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The five squeezes of a SIMD group (`group`, WP6)

`SqInv m M I b`: after `b` rounds of `kf4` + `blk b'` the `KS` state is
`permN b` of the seed states `I`, the candidate/flag words of blocks
`b' < b` are in `ABUF` / `FL`, `HAVE6 = 0`, the iota table is intact and only
the group's scratch regions changed since `m`.
-/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt87.Proofs.Infra

/-- Regions a group writes before `pass3`. -/
def gsFrame : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800)]

/-- Close `Avoids rs lo hi` for literal layout ranges. -/
macro "grp_avoids" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    and_true, MlDsaOpt87.Proofs.GroupP.gsFrame, MlDsaOpt87.Proofs.groupFrame, KS, KB, RC4, HAVE6,
    ABUF, FL, ZH, MlDsaOpt87.Proofs.ACC, MlDsaOpt87.Proofs.RHO1, MlDsaOpt87.Proofs.BK]
  omega))

theorem FrameExcept.of_avoid {m m' : ByteArray} {rs rs' : List (Nat × Nat)} (h : FrameExcept m m' rs)
    (hs : ∀ a, (∀ r ∈ rs', a < r.1 ∨ r.2 ≤ a) → ∀ r ∈ rs, a < r.1 ∨ r.2 ≤ a) :
    FrameExcept m m' rs' :=
  fun a ha => h a (hs a ha)

/-- Close the side goal of `FrameExcept.of_avoid` for literal layout ranges. -/
macro "grp_sub" : tactic => `(tactic| (
  intro a ha
  simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil, IsEmpty.forall_iff,
    forall_const, implies_true, and_true, MlDsaOpt87.Proofs.GroupP.gsFrame,
    MlDsaOpt87.Proofs.groupFrame, KS, KB, RC4, HAVE6, ABUF, FL, ZH, MlDsaOpt87.Proofs.ACC,
    MlDsaOpt87.Proofs.RHO1, MlDsaOpt87.Proofs.BK] at ha ⊢
  omega))

def SqInv (m M : ByteArray) (I : Nat → Fips202.SpongeState) (b : Nat) : Prop :=
  KS4 M (fun k => permN b (I k)) ∧ RC4Table M ∧ word M HAVE6 = 0 ∧ FrameExcept m M gsFrame ∧
  ∀ b', b' < b →
    (∀ i, i < 56 → word M (ABUF + 1792 * b' + 32 * i) = pack4 fun k => cand (permN (b' + 1) (I k)) i) ∧
    (∀ g, g < 7 → word M (FL + 224 * b' + 32 * g) = flagWord (fun k => permN (b' + 1) (I k)) g)

theorem rc4_frame {M M' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept M M' rs)
    (ha : ∀ i, i < 24 → Avoids rs (RC4 + 32 * i) (RC4 + 32 * i + 32)) (hrc : RC4Table M) :
    RC4Table M' := fun i hi => by rw [FrameExcept.word h (ha i hi)]; exact hrc i hi

theorem ks4_frame {M M' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept M M' rs)
    (ha : ∀ x, x < 25 → Avoids rs (KS + 32 * x) (KS + 32 * x + 32)) {S : Nat → Fips202.SpongeState}
    (hks : KS4 M S) : KS4 M' S := fun x hx => by rw [FrameExcept.word h (ha x hx)]; exact hks x hx

/-- Glue: the base stack of `group`'s body. -/
abbrev gB (amask col rb ret : Nat) (tail : List UInt256) : List UInt256 :=  -- port: `amask`, `rb`
  wd amask :: wd col :: wd rb :: wd ret :: tail

theorem squeeze_step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {amask col rb b : Nat} (hb : b < 5) {m M : ByteArray}
    {I : Nat → Fips202.SpongeState} (hI : Sized4 I) (hinv : SqInv m M I b)
    (hK : Reach (callState s (15291 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 22277 (wd (15299 + 22 * b) :: gB amask col rb ret tail) M) 15)
    (hL : ∀ M, Reach (callState s (15299 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 10997 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (15313 + 22 * b) ::
        gB amask col rb ret tail) M) 21)
    (hjK : Decode.isValidJumpDest optBytecode (15299 + 22 * b) = true)
    (hjL : Decode.isValidJumpDest optBytecode (15313 + 22 * b) = true) :
    ∃ M', SqInv m M' I (b + 1) ∧
      Reach (callState s (15291 + 22 * b) (gB amask col rb ret tail) M)
        (callState s (15291 + 22 * (b + 1)) (gB amask col rb ret tail) M') (36 + Gas.kf4 + Gas.blk) := by
  obtain ⟨hks, hrc, h6, hfr, hblocks⟩ := hinv
  obtain ⟨M1, hk1, hf1, hc1⟩ := MlDsaOpt87.Proofs.kf4_call hs (hr.callee (B' := Stack.kf4)
    (ret' := 15299 + 22 * b)
    (extra := [wd amask, wd col, wd rb, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    hjK (by omega)) M hrc
  have hS : Sized4 fun k => permN b (I k) := fun k hk => permN_size (hI k hk) b
  have hS1 : Sized4 fun k => permN (b + 1) (I k) := fun k hk => permN_size (hI k hk) (b + 1)
  have hks1 : KS4 M1 fun k => permN (b + 1) (I k) := by
    have e : (fun k => permN (b + 1) (I k)) = fun k => EvmSemantics.Crypto.Keccak.permute (permN b (I k)) :=
      funext fun k => permN_succ b (I k)
    rw [e]; exact hk1 _ hS hks
  obtain ⟨M2, hb2, hf2, hc2⟩ := MlDsaOpt87.Proofs.blk_call hs (hr.callee (B' := Stack.blk)
    (ret' := 15313 + 22 * b)
    (extra := [wd amask, wd col, wd rb, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    hjL (by omega)) M1 (b := b) (by omega)
  obtain ⟨hA, hF⟩ := hb2 _ hS1 hks1
  refine ⟨M2, ⟨ks4_frame hf2 (fun x hx => by grp_avoids) hks1,
    rc4_frame hf2 (fun i hi => by grp_avoids) (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
    ?_, ?_, ?_⟩, ?_⟩
  · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact h6
  · exact FrameExcept.of_avoid (hfr.trans (hf1.trans hf2)) (by grp_sub)
  · intro b' hb'
    by_cases hbb : b' = b
    · subst hbb; exact ⟨hA, hF⟩
    · obtain ⟨hA', hF'⟩ := hblocks b' (by omega)
      refine ⟨fun i hi => ?_, fun g hg => ?_⟩
      · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact hA' i hi
      · rw [FrameExcept.word hf2 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact hF' g hg
  · have h := hK.trans (hc1.trans ((hL M1).trans hc2))
    rw [show 15291 + 22 * (b + 1) = 15313 + 22 * b by ring]
    exact h.mono (by omega)

theorem squeezes {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {amask col rb : Nat} {m M0 : ByteArray}
    {I : Nat → Fips202.SpongeState} (hI : Sized4 I) (hinv : SqInv m M0 I 0)
    (hK : ∀ b, b < 5 → ∀ M, Reach (callState s (15291 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 22277 (wd (15299 + 22 * b) :: gB amask col rb ret tail) M) 15)
    (hL : ∀ b, b < 5 → ∀ M, Reach (callState s (15299 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 10997 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (15313 + 22 * b) ::
        gB amask col rb ret tail) M) 21)
    (hjK : ∀ b, b < 5 → Decode.isValidJumpDest optBytecode (15299 + 22 * b) = true)
    (hjL : ∀ b, b < 5 → Decode.isValidJumpDest optBytecode (15313 + 22 * b) = true) :
    ∀ n, n ≤ 5 → ∃ M', SqInv m M' I n ∧
      Reach (callState s 15291 (gB amask col rb ret tail) M0)
        (callState s (15291 + 22 * n) (gB amask col rb ret tail) M') (n * (36 + Gas.kf4 + Gas.blk))
  | 0, _ => ⟨M0, hinv, (Reach.refl _).of_eq rfl rfl⟩
  | n + 1, hn => by
    obtain ⟨M', hinv', hR⟩ := squeezes hs hr hI hinv hK hL hjK hjL n (by omega)
    obtain ⟨M'', hinv'', hR'⟩ := squeeze_step hs hr (by omega) hI hinv' (hK n (by omega) M')
      (hL n (by omega)) (hjK n (by omega)) (hjL n (by omega))
    exact ⟨M'', hinv'', (hR.trans hR').mono (by rw [Nat.succ_mul])⟩

end MlDsaOpt87.Proofs.GroupP
