import MlDsaOpt87.Fn.Ntt.FwdA
import MlDsaOpt87.Fn.Ntt.FwdB
import MlDsaOpt87.Fn.Ntt.FwdC
import MlDsaOpt87.Fn.Ntt.InvC
import MlDsaOpt87.Fn.Ntt.InvB
import MlDsaOpt87.Fn.Ntt.InvA
import MlDsaOpt87.Fn.Ntt.Ctl
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Ntt/Passes.lean` by `scripts/proofgen_port.py 87` --sub 43264=51456 --sub 44288=52480 --sub 66080=91680 --sub 60000=70000; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# The six loops of `ntt` / `intt` (WP7)

Each pass iterates its loop body (`*_body`, generated) with the matching back
edge (`Ctl`), then runs the last body and the exit. The memory after each
iteration is known only through the pass invariant (`reach_iterF`).
-/

namespace MlDsaOpt87.Proofs.NttW

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt87.Proofs MlDsaOpt44.Proofs

set_option maxHeartbeats 0

local notation "cC2" => UInt256.ofNat 105209460187928082099348286046428385038300376303896864318478598146
local notation "cM" => UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855
local notation "cCI" => UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723

/-- Sum of an iteration-dependent cost. -/
def costSum (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => costSum c n + c n

theorem reach_iterF {S : Nat → ByteArray → State} {Q : Nat → ByteArray → Prop} {c : Nat → Nat} :
    ∀ n, (∀ i M, i < n → Q i M → ∃ M', Q (i + 1) M' ∧ Reach (S i M) (S (i + 1) M') (c i)) →
      ∀ M, Q 0 M → ∃ M', Q n M' ∧ Reach (S 0 M) (S n M') (costSum c n)
  | 0, _, M, hM => ⟨M, hM, by simpa [costSum] using Reach.refl (S 0 M)⟩
  | n + 1, h, M, hM => by
    obtain ⟨M₁, hP₁, hR₁⟩ := reach_iterF n (fun i M hi => h i M (by omega)) M hM
    obtain ⟨M₂, hP₂, hR₂⟩ := h n M₁ (by omega) hP₁
    exact ⟨M₂, hP₂, hR₁.trans hR₂⟩

theorem reach_post1 {S : State} {s : State} {pc : Nat} {rest : List UInt256} {mem : ByteArray}
    {a a' c : Nat} (h : Reach S (callState s pc (UInt256.ofNat a :: rest) mem) c) (ha : a = a') :
    Reach S (callState s pc (UInt256.ofNat a' :: rest) mem) c := by subst ha; exact h

theorem reach_post2 {S : State} {s : State} {pc : Nat} {rest : List UInt256} {mem : ByteArray}
    {a b a' b' c : Nat} (h : Reach S (callState s pc (UInt256.ofNat a :: UInt256.ofNat b :: rest) mem) c)
    (ha : a = a') (hb : b = b') :
    Reach S (callState s pc (UInt256.ofNat a' :: UInt256.ofNat b' :: rest) mem) c := by
  subst ha hb; exact h

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960) (ret : Nat)
  (H : Prop) (h : Nat → Nat → F)
include hs htail

theorem fA_pass (M0 : ByteArray)
    (hP0 : H → PassInv M0 32768 (fun t => t % 32 < 0) (Bf 0) (Bf 3) (fun k => fwdL (h k) 0)
      (fun k => fwdL (h k) 3)) :
    ∃ M', (H → PassInv M' 32768 (fun t => t % 32 < 32) (Bf 0) (Bf 3) (fun k => fwdL (h k) 0)
      (fun k => fwdL (h k) 3)) ∧ FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 17692 (UInt256.ofNat 32768 :: UInt256.ofNat 33792 :: cC2 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s 18157 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cC2 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M') 34346 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s 17692 (UInt256.ofNat (32768 + 32 * c) :: UInt256.ofNat (33792) :: cC2 ::
      cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PassInv M 32768 (fun t => t % 32 < c) (Bf 0) (Bf 3) (fun k => fwdL (h k) 0)
      (fun k => fwdL (h k) 3)) ∧ FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun _ => 1045 + 28) 31 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fA_body hs htail ret H h c (by omega) M hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (fA_cont hs htail M' ret (32768 + 32 * c) (by omega))) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fA_body hs htail ret H h 31 (by norm_num) M1 hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fA_exit hs htail M2 ret (32768 + 32 * 31) (by norm_num))).mono
      (by simp only [costSum]; norm_num)⟩

theorem fB_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PassInv M0 32768 (fun t => 4 * (t / 32) + t % 4 < 0) (Bf 3) (Bf 6)
      (fun k => fwdL (h k) 3) (fun k => fwdL (h k) 6)) :
    ∃ M', (H → PassInv M' 32768 (fun t => 4 * (t / 32) + t % 4 < 32) (Bf 3) (Bf 6)
      (fun k => fwdL (h k) 3) (fun k => fwdL (h k) 6)) ∧ FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 18157 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cC2 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s 18651 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cC2 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M') 37354 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 18157 (UInt256.ofNat (32768 + 1024 * (n / 4) + 32 * (n % 4)) ::
      UInt256.ofNat (4096 + 224 * (n / 4)) :: cC2 :: cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PassInv M 32768 (fun t => 4 * (t / 32) + t % 4 < n) (Bf 3) (Bf 6)
      (fun k => fwdL (h k) 3) (fun k => fwdL (h k) 6)) ∧ FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun n => 1129 + if n % 4 = 3 then 68 else 28) 31 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fB_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      refine ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩, ?_⟩
      by_cases hj : n % 4 = 3
      · exact (reach_post2 (hR'.trans (fB_co hs htail M' ret _ _ (by omega) (by omega) (by omega) (by omega)))
          (by omega) (by omega)).mono (by simp [hj])
      · exact (reach_post2 (hR'.trans (fB_ci hs htail M' ret _ _ (by omega) (by omega)))
          (by omega) (by omega)).mono (by simp [hj]))
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fB_body hs htail ret H h 31 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fB_ex hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem fC_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PassInv M0 32768 (fun t => t / 4 < 0) (Bf 6) (Bf 8)
      (fun k => fwdL (h k) 6) (fun k => fwdL (h k) 8)) :
    ∃ M', (H → PassInv M' 32768 (fun t => t / 4 < 64) (Bf 6) (Bf 8)
      (fun k => fwdL (h k) 6) (fun k => fwdL (h k) 8)) ∧ FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 18651 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cC2 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s ret tail M') 27986 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 18651 (UInt256.ofNat (32768 + 128 * n) ::
      UInt256.ofNat (5888 + 96 * n) :: cC2 :: cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PassInv M 32768 (fun t => t / 4 < n) (Bf 6) (Bf 8)
      (fun k => fwdL (h k) 6) (fun k => fwdL (h k) 8)) ∧ FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun _ => 397 + 40) 63 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fC_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (fC_cont hs htail M' ret _ _ (by omega) (by omega))) (by omega) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fC_body hs htail ret H h 63 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fC_exit hs htail M2 ret _ _ (by norm_num) (by norm_num) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

theorem iC_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PassInv M0 51456 (fun t => t / 4 < 0) (2 ^ 58) (Bi 2) h
      (fun k => invL (scaleR h k) 2)) :
    ∃ M', (H → PassInv M' 51456 (fun t => t / 4 < 64) (2 ^ 58) (Bi 2) h
      (fun k => invL (scaleR h k) 2)) ∧ FrameExcept M0 M' [(51456, 51456 + 8192)] ∧
      Reach (callState s 18894 (UInt256.ofNat 51456 :: UInt256.ofNat 11936 :: cCI :: cM ::
          UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M0)
        (callState s 19164 (UInt256.ofNat 51456 :: UInt256.ofNat 5664 :: cCI :: cM ::
          UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M') 39370 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 18894 (UInt256.ofNat (51456 + 128 * n) ::
      UInt256.ofNat (11936 - 96 * n) :: cCI :: cM :: UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PassInv M 51456 (fun t => t / 4 < n) (2 ^ 58) (Bi 2) h
      (fun k => invL (scaleR h k) 2)) ∧ FrameExcept M0 M [(51456, 51456 + 8192)])
    (c := fun _ => 569 + 46) 63 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := iC_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (iC_cont hs htail M' ret _ _ (by omega) (by omega) (by omega) (by omega)))
          (by omega) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := iC_body hs htail ret H h 63 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (iC_exit hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem iB_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PassInv M0 51456 (fun t => 4 * (t / 32) + t % 4 < 0) (Bi 2) (Bi 5)
      (fun k => invL (scaleR h k) 2) (fun k => invL (scaleR h k) 5)) :
    ∃ M', (H → PassInv M' 51456 (fun t => 4 * (t / 32) + t % 4 < 32) (Bi 2) (Bi 5)
      (fun k => invL (scaleR h k) 2) (fun k => invL (scaleR h k) 5)) ∧
      FrameExcept M0 M' [(51456, 51456 + 8192)] ∧
      Reach (callState s 19164 (UInt256.ofNat 51456 :: UInt256.ofNat 5664 :: cCI :: cM ::
          UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M0)
        (callState s 19686 (UInt256.ofNat 51456 :: UInt256.ofNat 52480 :: cCI :: cM ::
          UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M') 38560 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 19164 (UInt256.ofNat (51456 + 1024 * (n / 4) + 32 * (n % 4)) ::
      UInt256.ofNat (5664 - 224 * (n / 4)) :: cCI :: cM :: UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PassInv M 51456 (fun t => 4 * (t / 32) + t % 4 < n) (Bi 2) (Bi 5)
      (fun k => invL (scaleR h k) 2) (fun k => invL (scaleR h k) 5)) ∧
      FrameExcept M0 M [(51456, 51456 + 8192)])
    (c := fun n => 1165 + if n % 4 = 3 then 74 else 28) 31 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := iB_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      refine ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩, ?_⟩
      by_cases hj : n % 4 = 3
      · exact (reach_post2 (hR'.trans (iB_co hs htail M' ret _ _ (by omega) (by omega) (by omega) (by omega)
          (by omega))) (by omega) (by omega)).mono (by simp [hj])
      · exact (reach_post2 (hR'.trans (iB_ci hs htail M' ret _ _ (by omega) (by omega)))
          (by omega) (by omega)).mono (by simp [hj]))
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := iB_body hs htail ret H h 31 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (iB_ex hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem iA_pass (M0 : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PassInv M0 51456 (fun t => t % 32 < 0) (Bi 5) Bu (fun k => invL (scaleR h k) 5)
      (fun k t => Sc * invL (scaleR h k) 8 t)) :
    ∃ M', (H → PassInv M' 51456 (fun t => t % 32 < 32) (Bi 5) Bu (fun k => invL (scaleR h k) 5)
      (fun k t => Sc * invL (scaleR h k) 8 t)) ∧ FrameExcept M0 M' [(51456, 51456 + 8192)] ∧
      Reach (callState s 19686 (UInt256.ofNat 51456 :: UInt256.ofNat 52480 :: cCI :: cM ::
          UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M0)
        (callState s ret tail M') 41650 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s 19686 (UInt256.ofNat (51456 + 32 * c) :: UInt256.ofNat (52480) :: cCI ::
      cM :: UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PassInv M 51456 (fun t => t % 32 < c) (Bi 5) Bu (fun k => invL (scaleR h k) 5)
      (fun k t => Sc * invL (scaleR h k) 8 t)) ∧ FrameExcept M0 M [(51456, 51456 + 8192)])
    (c := fun _ => 1273 + 28) 31 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := iA_body hs htail ret H h c (by omega) M hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (iA_cont hs htail M' ret (51456 + 32 * c) (by omega))) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := iA_body hs htail ret H h 31 (by norm_num) M1 hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (iA_exit hs htail M2 ret (51456 + 32 * 31) (by norm_num) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

end

end MlDsaOpt87.Proofs.NttW
