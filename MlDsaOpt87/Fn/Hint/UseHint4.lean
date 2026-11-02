import MlDsaOpt65.Fn.NttV4.Lemmas
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/-!
# v4 `usehint` (ML-DSA-87): blocks, loop and the contract body

`usehint [B, ret]` with `B = ACC + 0x2000 g`: entry `[B, B + 0x2000]` (13 gas), 256 visits of
the loop body (162 gas each; `uh_body`: reads `B + 32t`, `B + 32t − 0x4900` (`SP_g`),
`B + 32t + 0x4000` (`HP_g`), stores the v4 UseHint word `uh6W` at `B + 32t`), exit (12 gas):
`13 + 256 · 162 + 12 = 41497 = Gas.usehint`. The loop body is `gen_opt.py` `uh_word`, the same
code ML-DSA-65 fuses into its inverse NTT, so the word lemmas are shared
(`MlDsaOpt65/Fn/NttV4/Lemmas.lean`: `uh6W_lanes`, `uh6L_spec`); the loop is as v3's
(`Fn/Hint/G5UseHint.lean`).
-/

namespace MlDsaOpt87.Proofs.UH4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt44.Proofs.Ntt4 (uX uY uQ)
open MlDsaOpt65.Proofs.Ntt6 (uh6W uF6 uV6 uD6 uh6W_lanes)
open MlDsaOpt65.Proofs.NttV4 (uh6L uh6L_spec useHint_emod6 uh6_x_lt)

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem uh_entry (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (B : Nat) :
    Reach (callState s 17092 (wd B :: wd ret :: tail) M)
      (callState s 17099 (wd B :: wd (8192 + B) :: wd ret :: tail) M) 13 := by
  opt87_reach [7826, 7827, 7828, 7829, 7830]

theorem uh_body (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (p e : Nat) (hp : 18688 ≤ p)
    (hpe : p + 32 < e) (he : e + 16384 ≤ 90656) :
    Reach (callState s 17099 (wd p :: wd e :: wd ret :: tail) M)
      (callState s 17099 (wd (32 + p) :: wd e :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          (uh6W (UInt256.ofNat (word M p)) (word M (p - 18688)) (word M (16384 + p))).toNat 32) p)) 162 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7831, 7832, 7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845,
    7846, 7847, 7848, 7849, 7850, 7851, 7852, 7853, 7854, 7855, 7856, 7857, 7858, 7859, 7860, 7861, 7862,
    7863, 7864, 7865, 7866, 7867, 7868, 7869, 7870, 7871, 7872, 7873, 7874, 7875, 7876, 7877, 7878, 7879,
    7880, 7881]
    with [uh6W, uF6, uV6, uD6, uY, uQ, uX]

theorem uh_last (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (p e : Nat) (hp : 18688 ≤ p)
    (hpe : p + 32 = e) (he : e + 16384 ≤ 90656) :
    Reach (callState s 17099 (wd p :: wd e :: wd ret :: tail) M)
      (callState s 17270 (wd (32 + p) :: wd e :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          (uh6W (UInt256.ofNat (word M p)) (word M (p - 18688)) (word M (16384 + p))).toNat 32) p)) 162 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hpe
  opt87_reach [7831, 7832, 7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845,
    7846, 7847, 7848, 7849, 7850, 7851, 7852, 7853, 7854, 7855, 7856, 7857, 7858, 7859, 7860, 7861, 7862,
    7863, 7864, 7865, 7866, 7867, 7868, 7869, 7870, 7871, 7872, 7873, 7874, 7875, 7876, 7877, 7878, 7879,
    7880, 7881]
    with [uh6W, uF6, uV6, uD6, uY, uQ, uX]

set_option maxRecDepth 100000 in
theorem uh_ret (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (a b : Nat) :
    Reach (callState s 17270 (wd a :: wd b :: wd ret :: tail) M) (callState s ret tail M) 12 := by
  opt87_reach [7882, 7883, 7884] with [hj]

end

/-- Value stored at `B + 32 t`. -/
def uv (M : ByteArray) (B t : Nat) : Nat :=
  (uh6W (UInt256.ofNat (word M (B + 32 * t))) (word M (B + 32 * t - 18688))
    (word M (16384 + (B + 32 * t)))).toNat

/-- Memory after `j` iterations. -/
def Mj (M : ByteArray) (B j : Nat) : ByteArray := storeWords M B (uv M B) j

theorem Mj_reads (M : ByteArray) {B j a : Nat}
    (h2 : a + 32 ≤ B ∨ B + 32 * j ≤ a) : word (Mj M B j) a = word M a :=
  FrameExcept.word (FrameExcept.storeWords M B (uv M B) j)
    (by simp only [avoids_cons, avoids_nil, and_true]; omega)

theorem uv_lt (M : ByteArray) (B t : Nat) : uv M B t < 2 ^ 256 := by
  unfold uv; exact MlDsaOpt44.Proofs.PK.u_toNat_lt _

theorem Mj_succ (M : ByteArray) (B j : Nat) :
    Mj M B (j + 1) = MachineState.writeBytes (Mj M B j)
      (Data.Bytes.natToBytesPadded (uv M B j) 32) (B + 32 * j) := by
  unfold Mj; rw [storeWords_succ, show B + j * 32 = B + 32 * j by omega]

theorem uh_step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) {B : Nat} (hB : 18688 + 32 ≤ B)
    (hBe : B + 8192 + 16384 ≤ 90656) (j : Nat) (hj : j + 1 < 256) :
    Reach (callState s 17099 (wd (B + 32 * j) :: wd (8192 + B) :: wd ret :: tail) (Mj M B j))
      (callState s 17099 (wd (B + 32 * (j + 1)) :: wd (8192 + B) :: wd ret :: tail) (Mj M B (j + 1)))
      162 := by
  have hb := uh_body hs (ret := ret) htail (Mj M B j) (B + 32 * j) (8192 + B) (by omega) (by omega)
    (by omega)
  rw [Mj_reads M (a := B + 32 * j) (by omega), Mj_reads M (a := B + 32 * j - 18688) (by omega),
    Mj_reads M (a := 16384 + (B + 32 * j)) (by omega)] at hb
  refine hb.of_eq rfl ?_
  rw [Mj_succ, show B + 32 * (j + 1) = 32 + (B + 32 * j) by omega]; rfl

theorem uh_run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) {B : Nat} (hB : 18688 + 32 ≤ B)
    (hBe : B + 8192 + 16384 ≤ 90656) :
    Reach (callState s 17092 (wd B :: wd ret :: tail) m) (callState s ret tail (Mj m B 256)) 41497 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.usehint, Stack.leaf] at this; omega
  have hloop := Reach.loop (I := fun j => callState s 17099
    (wd (B + 32 * j) :: wd (8192 + B) :: wd ret :: tail) (Mj m B j)) 255
    (fun j hj => uh_step hs htail m hB hBe j (by omega))
  have hent := uh_entry hs (ret := ret) htail m B
  have hlast := uh_last hs (ret := ret) htail (Mj m B 255) (B + 32 * 255) (8192 + B) (by omega)
    (by omega) (by omega)
  rw [Mj_reads m (a := B + 32 * 255) (by omega), Mj_reads m (a := B + 32 * 255 - 18688) (by omega),
    Mj_reads m (a := 16384 + (B + 32 * 255)) (by omega)] at hlast
  have hfin := uh_ret hs htail hr.jumpdest hr.small (Mj m B 256) (32 + (B + 32 * 255)) (8192 + B)
  have hlast' : Reach (callState s 17099 (wd (B + 32 * 255) :: wd (8192 + B) :: wd ret :: tail)
      (Mj m B 255)) (callState s 17270 (wd (32 + (B + 32 * 255)) :: wd (8192 + B) :: wd ret :: tail)
      (Mj m B 256)) 162 :=
    hlast.of_eq rfl (by rw [show Mj m B 256 = Mj m B (255 + 1) from rfl, Mj_succ m B 255]; rfl)
  have hall := ((hent.trans (hloop.of_eq (by simp [Mj, storeWords]) rfl)).trans hlast').trans hfin
  exact hall.mono (by norm_num)

/-- Every lane of the stored word is below `16` (final `AND 15`). -/
theorem uh6W_lt16 (x : UInt256) (s h : Nat) {r : Nat} (hr : r < 4) :
    lane (uh6W x s h).toNat r < 16 := by
  unfold uh6W uF6
  set v := uV6 (uD6 (uY (uX x s))) h
  rw [MlDsaOpt44.Proofs.NttW.toNat_eq_pack4 v,
    show (94156526030800211462641076851929073193762651939542684139535 : Nat) = pack4 fun _ => 15 by
      unfold pack4; norm_num,
    MlDsaOpt44.Proofs.L10.u_and (fun r _ => by show _ < _; omega) (MlDsaOpt44.Proofs.L10.lanes_lane _),
    MlDsaOpt44.Proofs.Ntt4.lane_ofNat_pack4
      (fun r _ => Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)) hr]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

set_option maxRecDepth 100000 in
theorem usehint_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) {g : Nat} (hg : g < 2) :
    ∃ m', (∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t)) r < 2 ^ 30 ∧
          lane (word m (SP + 0x2000 * g + 32 * t)) r ≤ spOff ∧
          lane (word m (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r =
          (Fips204.useHint P (lane (word m (HP + 0x2000 * g + 32 * t)) r)
            ((lane (word m (ACC + 0x2000 * g + 32 * t)) r : Int) +
              lane (word m (SP + 0x2000 * g + 32 * t)) r - spOff)).toNat) ∧
      (∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r < 16) ∧
      FrameExcept m m' [(ACC + 0x2000 * g, ACC + 0x2000 * g + 8192)] ∧
      Call s Entry.usehint [wd (ACC + 0x2000 * g)] ret tail m [] m' Gas.usehint := by
  have hB : 18688 + 32 ≤ ACC + 0x2000 * g := by unfold ACC; omega
  have hBe : ACC + 0x2000 * g + 8192 + 16384 ≤ 90656 := by unfold ACC; omega
  have hw : ∀ t, t < 256 → word (Mj m (ACC + 0x2000 * g) 256) (ACC + 0x2000 * g + 32 * t) =
      uv m (ACC + 0x2000 * g) t := fun t ht => word_storeWords (uv_lt m _ t) 256 ht
  have hsp : ∀ t, SP + 0x2000 * g + 32 * t = ACC + 0x2000 * g + 32 * t - 18688 := fun t => by
    unfold SP ACC; omega
  have hhp : ∀ t, HP + 0x2000 * g + 32 * t = 16384 + (ACC + 0x2000 * g + 32 * t) := fun t => by
    unfold HP ACC; omega
  have hspv : spOff = 128 * 8380417 + 261888 - 1 := by unfold spOff Fips204.q; norm_num
  refine ⟨Mj m (ACC + 0x2000 * g) 256, fun t ht h r hr' => ?_, fun t ht r hr' => ?_, ?_, ?_⟩
  · rw [hsp, hhp] at h ⊢
    rw [hw t ht, uv]
    have hx : ∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t - 18688)) r +
        lane (UInt256.ofNat (word m (ACC + 0x2000 * g + 32 * t))).toNat r < 2 ^ 31 := fun r hr => by
      rw [toNat_ofNat_of_lt (word_lt _ _)]
      exact uh6_x_lt (h r hr).1 (by rw [← hspv]; exact (h r hr).2.1)
    rw [uh6W_lanes (word_lt _ _) (word_lt _ _) hx (fun r hr => (h r hr).2.2) r hr',
      toNat_ofNat_of_lt (word_lt _ _), uh6L_spec P rfl (h r hr').2.2]
    refine congrArg Int.toNat ?_
    rw [useHint_emod6 P _ (_ - 261887), useHint_emod6 P _ (_ - (spOff : Int))]
    refine congrArg (Fips204.useHint P _) ?_
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨128, ?_⟩
    have hq : (Fips204.q : Int) = 8380417 := by unfold Fips204.q; norm_num
    rw [hspv, hq]
    push_cast
    ring
  · rw [hw t ht, uv]; exact uh6W_lt16 _ _ _ hr'
  · exact FrameExcept.storeWords m (ACC + 0x2000 * g) (uv m (ACC + 0x2000 * g)) 256
  · rw [call_iff, Entry.usehint, Gas.usehint]
    exact uh_run hs hr m hB hBe

end MlDsaOpt87.Proofs.UH4
