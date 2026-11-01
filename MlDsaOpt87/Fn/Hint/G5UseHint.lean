import MlDsaOpt65.Fn.Hint.G5Pure
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
set_option warningAsError true
/-!
# `usehint` (ML-DSA-87): blocks, loop and the contract body

`usehint [B, ret]` with `B = ACC + 0x2000 g`: entry `[B, B + 0x2000]` (13 gas), 256 visits of
the loop body (188 gas each; `uh_body`: reads `B + 32t`, `B + 32t − 0x4900`,
`B + 32t + 0x4000`, stores `uhW` at `B + 32t`), exit (12 gas):
`13 + 256 · 188 + 12 = 48153 = Gas.usehint`. The stored word is `G5H.uhW` (`Fn/Hint/G5Pure`).
-/

namespace MlDsaOpt87.Proofs.G5UH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt65.Proofs.G5H

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem uh_entry (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (B : Nat) :
    Reach (callState s 17065 (wd B :: wd ret :: tail) M)
      (callState s 17072 (wd B :: wd (8192 + B) :: wd ret :: tail) M) 13 := by
  opt87_reach [7706, 7707, 7708, 7709, 7710]

theorem uh_body (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (p e : Nat) (hp : 18688 ≤ p)
    (hpe : p + 32 < e) (he : e + 16384 ≤ 90656) :
    Reach (callState s 17072 (wd p :: wd e :: wd ret :: tail) M)
      (callState s 17072 (wd (32 + p) :: wd e :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          (uhW (word M p) (word M (p - 18688)) (word M (16384 + p))).toNat 32) p)) 188 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7711, 7712, 7713, 7714, 7715, 7716, 7717, 7718, 7719, 7720, 7721, 7722, 7723, 7724, 7725, 7726, 7727, 7728, 7729, 7730, 7731, 7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743, 7744, 7745, 7746, 7747, 7748, 7749, 7750, 7751, 7752, 7753, 7754, 7755, 7756, 7757, 7758, 7759, 7760, 7761, 7762, 7763, 7764, 7765, 7766, 7767, 7768, 7769]
    with [uhW, uhF, uhV, uhD, uhR, uhQ, uhX]

theorem uh_last (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (p e : Nat) (hp : 18688 ≤ p)
    (hpe : p + 32 = e) (he : e + 16384 ≤ 90656) :
    Reach (callState s 17072 (wd p :: wd e :: wd ret :: tail) M)
      (callState s 17333 (wd (32 + p) :: wd e :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          (uhW (word M p) (word M (p - 18688)) (word M (16384 + p))).toNat 32) p)) 188 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hpe
  opt87_reach [7711, 7712, 7713, 7714, 7715, 7716, 7717, 7718, 7719, 7720, 7721, 7722, 7723, 7724, 7725, 7726, 7727, 7728, 7729, 7730, 7731, 7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743, 7744, 7745, 7746, 7747, 7748, 7749, 7750, 7751, 7752, 7753, 7754, 7755, 7756, 7757, 7758, 7759, 7760, 7761, 7762, 7763, 7764, 7765, 7766, 7767, 7768, 7769]
    with [uhW, uhF, uhV, uhD, uhR, uhQ, uhX]

set_option maxRecDepth 100000 in
theorem uh_ret (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (a b : Nat) :
    Reach (callState s 17333 (wd a :: wd b :: wd ret :: tail) M) (callState s ret tail M) 12 := by
  opt87_reach [7770, 7771, 7772] with [hj]

end

/-- Value stored at `B + 32 t`. -/
def uv (M : ByteArray) (B t : Nat) : Nat :=
  (uhW (word M (B + 32 * t)) (word M (B + 32 * t - 18688)) (word M (16384 + (B + 32 * t)))).toNat

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
    Reach (callState s 17072 (wd (B + 32 * j) :: wd (8192 + B) :: wd ret :: tail) (Mj M B j))
      (callState s 17072 (wd (B + 32 * (j + 1)) :: wd (8192 + B) :: wd ret :: tail) (Mj M B (j + 1)))
      188 := by
  have hb := uh_body hs (ret := ret) htail (Mj M B j) (B + 32 * j) (8192 + B) (by omega) (by omega)
    (by omega)
  rw [Mj_reads M (a := B + 32 * j) (by omega), Mj_reads M (a := B + 32 * j - 18688) (by omega),
    Mj_reads M (a := 16384 + (B + 32 * j)) (by omega)] at hb
  refine hb.of_eq rfl ?_
  rw [Mj_succ, show B + 32 * (j + 1) = 32 + (B + 32 * j) by omega]; rfl

theorem uh_run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) {B : Nat} (hB : 18688 + 32 ≤ B)
    (hBe : B + 8192 + 16384 ≤ 90656) :
    Reach (callState s 17065 (wd B :: wd ret :: tail) m) (callState s ret tail (Mj m B 256)) 48153 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.usehint, Stack.leaf] at this; omega
  have hloop := Reach.loop (I := fun j => callState s 17072
    (wd (B + 32 * j) :: wd (8192 + B) :: wd ret :: tail) (Mj m B j)) 255
    (fun j hj => uh_step hs htail m hB hBe j (by omega))
  have hent := uh_entry hs (ret := ret) htail m B
  have hlast := uh_last hs (ret := ret) htail (Mj m B 255) (B + 32 * 255) (8192 + B) (by omega)
    (by omega) (by omega)
  rw [Mj_reads m (a := B + 32 * 255) (by omega), Mj_reads m (a := B + 32 * 255 - 18688) (by omega),
    Mj_reads m (a := 16384 + (B + 32 * 255)) (by omega)] at hlast
  have hfin := uh_ret hs htail hr.jumpdest hr.small (Mj m B 256) (32 + (B + 32 * 255)) (8192 + B)
  have hlast' : Reach (callState s 17072 (wd (B + 32 * 255) :: wd (8192 + B) :: wd ret :: tail)
      (Mj m B 255)) (callState s 17333 (wd (32 + (B + 32 * 255)) :: wd (8192 + B) :: wd ret :: tail)
      (Mj m B 256)) 188 := hlast.of_eq rfl (by rw [show Mj m B 256 = Mj m B (255 + 1) from rfl, Mj_succ m B 255]; rfl)
  have hall := ((hent.trans (hloop.of_eq (by simp [Mj, storeWords]) rfl)).trans hlast').trans hfin
  exact hall.mono (by norm_num)

theorem usehint_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) {g : Nat} (hg : g < 2) :
    ∃ m', (∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t)) r < 2 ^ 27 ∧
          lane (word m (SP + 0x2000 * g + 32 * t)) r < 2 ^ 29 ∧
          lane (word m (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r =
          (Fips204.useHint P (lane (word m (HP + 0x2000 * g + 32 * t)) r)
            ((lane (word m (ACC + 0x2000 * g + 32 * t)) r : Int) -
              lane (word m (SP + 0x2000 * g + 32 * t)) r)).toNat) ∧
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
  refine ⟨Mj m (ACC + 0x2000 * g) 256, fun t ht h r hr' => ?_, fun t ht r hr' => ?_, ?_, ?_⟩
  · rw [hsp, hhp] at h
    rw [hw t ht, uv, hsp, hhp]
    exact uhW_spec P rfl (word_lt _ _) (word_lt _ _) (word_lt _ _) h hr'
  · rw [hw t ht, uv]; exact uhW_lt16 _ _ _ hr'
  · have h := FrameExcept.storeWords m (ACC + 0x2000 * g) (uv m (ACC + 0x2000 * g)) 256
    exact h
  · rw [call_iff, Entry.usehint, Gas.usehint]
    exact uh_run hs hr m hB hBe

end MlDsaOpt87.Proofs.G5UH
