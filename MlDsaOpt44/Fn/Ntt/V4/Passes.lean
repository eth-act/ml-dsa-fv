import MlDsaOpt44.Fn.Ntt.V4.FwdA
import MlDsaOpt44.Fn.Ntt.V4.FwdB
import MlDsaOpt44.Fn.Ntt.V4.FwdC
import MlDsaOpt44.Fn.Ntt.V4.InvC
import MlDsaOpt44.Fn.Ntt.V4.InvB
import MlDsaOpt44.Fn.Ntt.V4.InvA
import MlDsaOpt44.Fn.Ntt.V4.Ctl
/-!
# The six loops of the v4 `ntt` / `intt` (WP G, H)

Each pass iterates its generated loop body (`*_body`) with the matching back
edge (`Ctl`), then runs the last body and the exit; the memory after each
iteration is known only through the pass invariant (`reach_iterF`). The
last inverse pass also carries the frame of the `SP`/`HP` words it reads.
-/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

set_option maxHeartbeats 0

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

/-- Forward pass predicates: lanes in the layer-`L` interval, congruent to `fwdL`. -/
local notation "FP" h:max L:max => fun t w => LI (UInt256.ofNat w) L (fun k => fwdL (h k) L t)
/-- Inverse pass predicates: lanes below `B`, congruent to `invL` of the scaled input. -/
local notation "IP" h:max B:max L:max => fun t w => LOK (UInt256.ofNat w) B (fun k => invL (scaleR h k) L t)

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960) (ret : Nat)
  (H : Prop) (h : Nat → Nat → F)
include hs htail

theorem fA_pass (M0 : ByteArray) (hP0 : H → PI M0 32768 (fun t => t % 32 < 0) (FP h 0) (FP h 3)) :
    ∃ M', (H → PI M' 32768 (fun t => t % 32 < 32) (FP h 0) (FP h 3)) ∧
      FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 16584 (UInt256.ofNat 32768 :: UInt256.ofNat 33792 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s 17049 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M') 30890 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s 16584 (UInt256.ofNat (32768 + 32 * c) :: UInt256.ofNat (33792) ::
      cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PI M 32768 (fun t => t % 32 < c) (FP h 0) (FP h 3)) ∧
      FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun _ => 937 + 28) 31 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fA_body hs htail ret H h c (by omega) M hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (fA_cont hs htail M' ret (32768 + 32 * c) (by omega))) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fA_body hs htail ret H h 31 (by norm_num) M1 hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fA_exit hs htail M2 ret (32768 + 32 * 31) (by norm_num))).mono
      (by simp only [costSum]; norm_num)⟩

theorem fB_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PI M0 32768 (fun t => 4 * (t / 32) + t % 4 < 0) (FP h 3) (FP h 6)) :
    ∃ M', (H → PI M' 32768 (fun t => 4 * (t / 32) + t % 4 < 32) (FP h 3) (FP h 6)) ∧
      FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 17049 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s 17543 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M') 35050 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 17049 (UInt256.ofNat (32768 + 1024 * (n / 4) + 32 * (n % 4)) ::
      UInt256.ofNat (4096 + 224 * (n / 4)) :: cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M 32768 (fun t => 4 * (t / 32) + t % 4 < n) (FP h 3) (FP h 6)) ∧
      FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun n => 1057 + if n % 4 = 3 then 68 else 28) 31 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fB_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      refine ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩, ?_⟩
      by_cases hj : n % 4 = 3
      · exact (reach_post2 (hR'.trans (fB_co hs htail M' ret _ _ (by omega) (by omega) (by omega)
          (by omega))) (by omega) (by omega)).mono (by simp [hj])
      · exact (reach_post2 (hR'.trans (fB_ci hs htail M' ret _ _ (by omega) (by omega)))
          (by omega) (by omega)).mono (by simp [hj]))
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fB_body hs htail ret H h 31 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fB_ex hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem fC_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PI M0 32768 (fun t => t / 4 < 0) (FP h 6) (FP h 8)) :
    ∃ M', (H → PI M' 32768 (fun t => t / 4 < 64) (FP h 6) (FP h 8)) ∧
      FrameExcept M0 M' [(32768, 32768 + 8192)] ∧
      Reach (callState s 17543 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cM ::
          UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M0)
        (callState s ret tail M') 26448 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 17543 (UInt256.ofNat (32768 + 128 * n) ::
      UInt256.ofNat (5888 + 96 * n) :: cM :: UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M 32768 (fun t => t / 4 < n) (FP h 6) (FP h 8)) ∧
      FrameExcept M0 M [(32768, 32768 + 8192)])
    (c := fun _ => 373 + 40) 63 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := fC_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (fC_cont hs htail M' ret _ _ (by omega) (by omega))) (by omega)
          (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := fC_body hs htail ret H h 63 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (fC_exit hs htail M2 ret _ _ (by norm_num) (by norm_num) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

theorem iC_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PI M0 43264 (fun t => t / 4 < 0) (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (IP h (Bi 2) 2)) :
    ∃ M', (H → PI M' 43264 (fun t => t / 4 < 64)
        (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t)) (IP h (Bi 2) 2)) ∧
      FrameExcept M0 M' [(43264, 43264 + 8192)] ∧
      Reach (callState s 17786 (UInt256.ofNat 43264 :: UInt256.ofNat 11936 :: cCI :: cM ::
          UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M0)
        (callState s 18056 (UInt256.ofNat 43264 :: UInt256.ofNat 5664 :: cCI :: cM ::
          UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M') 38602 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 17786 (UInt256.ofNat (43264 + 128 * n) ::
      UInt256.ofNat (11936 - 96 * n) :: cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M 43264 (fun t => t / 4 < n)
        (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t)) (IP h (Bi 2) 2)) ∧
      FrameExcept M0 M [(43264, 43264 + 8192)])
    (c := fun _ => 557 + 46) 63 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := iC_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (iC_cont hs htail M' ret _ _ (by omega) (by omega) (by omega)
          (by omega))) (by omega) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := iC_body hs htail ret H h 63 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (iC_exit hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem iB_pass (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PI M0 43264 (fun t => 4 * (t / 32) + t % 4 < 0) (IP h (Bi 2) 2) (IP h (Bi 5) 5)) :
    ∃ M', (H → PI M' 43264 (fun t => 4 * (t / 32) + t % 4 < 32) (IP h (Bi 2) 2) (IP h (Bi 5) 5)) ∧
      FrameExcept M0 M' [(43264, 43264 + 8192)] ∧
      Reach (callState s 18056 (UInt256.ofNat 43264 :: UInt256.ofNat 5664 :: cCI :: cM ::
          UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M0)
        (callState s 18578 (UInt256.ofNat 43264 :: UInt256.ofNat 44288 :: cCI :: cM ::
          UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M') 37408 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s 18056 (UInt256.ofNat (43264 + 1024 * (n / 4) + 32 * (n % 4)) ::
      UInt256.ofNat (5664 - 224 * (n / 4)) :: cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M 43264 (fun t => 4 * (t / 32) + t % 4 < n) (IP h (Bi 2) 2) (IP h (Bi 5) 5)) ∧
      FrameExcept M0 M [(43264, 43264 + 8192)])
    (c := fun n => 1129 + if n % 4 = 3 then 74 else 28) 31 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := iB_body hs htail ret H h n (by omega) M
        (tblAt_frame htbl hQ.2 (by norm_num)) hQ.1
      refine ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩, ?_⟩
      by_cases hj : n % 4 = 3
      · exact (reach_post2 (hR'.trans (iB_co hs htail M' ret _ _ (by omega) (by omega) (by omega)
          (by omega) (by omega))) (by omega) (by omega)).mono (by simp [hj])
      · exact (reach_post2 (hR'.trans (iB_ci hs htail M' ret _ _ (by omega) (by omega)))
          (by omega) (by omega)).mono (by simp [hj]))
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := iB_body hs htail ret H h 31 (by norm_num) M1
    (tblAt_frame htbl hF1 (by norm_num)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (iB_ex hs htail M2 ret _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem iA_pass (M0 m0 : ByteArray) (hF0 : FrameExcept m0 M0 [(43264, 43264 + 8192)])
    (hSH : H → ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (SP + 32 * t)) r ≤ spOff ∧
      lane (word m0 (HP + 32 * t)) r ≤ 1)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PI M0 43264 (fun t => t % 32 < 0) (IP h (Bi 5) 5)
      (fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))) :
    ∃ M', (H → PI M' 43264 (fun t => t % 32 < 32) (IP h (Bi 5) 5)
        (fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))) ∧
      FrameExcept M0 M' [(43264, 43264 + 8192)] ∧
      Reach (callState s 18578 (UInt256.ofNat 43264 :: UInt256.ofNat 44288 :: cCI :: cM ::
          UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M0)
        (callState s ret tail M') 79410 := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s 18578 (UInt256.ofNat (43264 + 32 * c) :: UInt256.ofNat (44288) :: cCI ::
      cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PI M 43264 (fun t => t % 32 < c) (IP h (Bi 5) 5)
        (fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))) ∧
      FrameExcept M0 M [(43264, 43264 + 8192)])
    (c := fun _ => 2453 + 28) 31 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := iA_body hs htail ret H h c (by omega) M m0
        (frame_trans1 hF0 hQ.2) hSH hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (iA_cont hs htail M' ret (43264 + 32 * c) (by omega))) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := iA_body hs htail ret H h 31 (by norm_num) M1 m0
    (frame_trans1 hF0 hF1) hSH hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (iA_exit hs htail M2 ret (43264 + 32 * 31) (by norm_num) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

end

end MlDsaOpt44.Proofs.Ntt4
