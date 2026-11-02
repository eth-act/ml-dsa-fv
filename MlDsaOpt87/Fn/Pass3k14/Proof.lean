import MlDsaOpt87.Fn.Group.Common
import MlDsaOpt44.Fn.Group.Pass3k4
set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
/-!
# `pass3k14` (ML-DSA-87): 256 iterations of `ACC[0x2000 + 32 t] += kronWord14 t` (WP G1)

Template: `MlDsaOpt44/Fn/Group/Pass3k4.lean`. The multiplier word is
`(ZH[t] >> 192) | (ZH2[t] << 64)`; there is no candidate mask.
-/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- The Kronecker term of `pass3k14` at byte offset `i` (no reduction of the
product: the `AND` with a word mask makes it redundant). -/
def k14v (M : ByteArray) (i : Nat) : Nat :=
  (word M (ACC + 0x2000 + i) + ((word M (ZH2 + i) * 2 ^ 64 ||| word M (ZH + i) / 2 ^ 192) *
      word M (ABUF + i) &&& M64 * 2 ^ 192)) % 2 ^ 256

/-- Value `pass3k14` stores at `ACC[0x2000 + 32 t]`. -/
def k14f (m : ByteArray) (t : Nat) : Nat :=
  (word m (ACC + 0x2000 + 32 * t) + (word m (ABUF + 32 * t) *
      (word m (ZH + 32 * t) / 2 ^ 192 ||| word m (ZH2 + 32 * t) * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&&
    (M64 * 2 ^ 192))) % 2 ^ 256

theorem k14_body {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {i ret : Nat} (M : ByteArray) (hi : i + 32 < 8192) :
    Reach (callState s 12530 (wd i :: wd ret :: tail) M)
      (callState s 12530 (wd (i + 32) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (k14v M i) 32) (ACC + 0x2000 + i))) 115 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5326, 5327, 5328, 5329, 5330, 5331, 5332, 5333, 5334, 5335, 5336, 5337, 5338, 5339,
    5340, 5341, 5342, 5343, 5344, 5345, 5346, 5347, 5348, 5349, 5350, 5351, 5341, 5353, 5354, 5355,
    5356, 5357, 5358, 5359, 5360, 5361]
    with [k14v, ACC, ABUF, ZH, ZH2, M64]
  simp only [Nat.add_comm, Nat.mul_comm, Nat.and_comm, Nat.or_comm, and_self]

theorem k14_last {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret : Nat} (M : ByteArray) :
    Reach (callState s 12530 (wd 8160 :: wd ret :: tail) M)
      (callState s 12614 (wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (k14v M 8160) 32) (ACC + 0x2000 + 8160))) 117 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5326, 5327, 5328, 5329, 5330, 5331, 5332, 5333, 5334, 5335, 5336, 5337, 5338, 5339,
    5340, 5341, 5342, 5343, 5344, 5345, 5346, 5347, 5348, 5349, 5350, 5351, 5341, 5353, 5354, 5355,
    5356, 5357, 5358, 5359, 5360, 5361, 5362]
    with [k14v, ACC, ABUF, ZH, ZH2, M64]
  simp only [Nat.add_comm, Nat.mul_comm, Nat.and_comm, Nat.or_comm, and_self]

/-- The product of the unreduced multiplier, masked, is the product of the reduced one. -/
theorem k14_mask (x y a : Nat) :
    (x * 2 ^ 64 ||| y) * a &&& M64 * 2 ^ 192 =
      a * (y ||| x * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&& M64 * 2 ^ 192 := by
  have hM : M64 * 2 ^ 192 < 2 ^ 256 := by unfold M64; norm_num
  rw [← MlDsaOpt44.Proofs.GroupP.and_mod_of_lt (a := (x * 2 ^ 64 ||| y) * a) hM]
  congr 1
  rw [Nat.mul_comm a, Nat.mul_mod, Nat.mul_mod (y ||| _) a]
  congr 2
  rw [Nat.or_mod_two_pow, Nat.or_mod_two_pow (a := y), Nat.mod_mod, Nat.or_comm]

theorem k14_step (m : ByteArray) {j : Nat} (hj : j < 256) :
    MachineState.writeBytes (storeWords m (ACC + 0x2000) (k14f m) j)
        (Data.Bytes.natToBytesPadded (k14v (storeWords m (ACC + 0x2000) (k14f m) j) (32 * j)) 32)
        (ACC + 0x2000 + 32 * j) =
      storeWords m (ACC + 0x2000) (k14f m) (j + 1) := by
  refine storeWords_next rfl rfl ?_
  unfold k14v k14f
  rw [word_storeWords_out (a := ACC + 0x2000 + 32 * j) (by omega),
    word_storeWords_out (a := ABUF + 32 * j) (by unfold ABUF ACC; omega),
    word_storeWords_out (a := ZH + 32 * j) (by unfold ZH ACC; omega),
    word_storeWords_out (a := ZH2 + 32 * j) (by unfold ZH2 ACC; omega), k14_mask]

theorem pass3k14_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3k14 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 0x2000 + 32 * t) = k14f m t) ∧
      FrameExcept m m' [(ACC + 0x2000, ACC + 0x4000)] ∧
      Call s Entry.pass3k14 [] ret tail m [] m' Gas.pass3k14 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3k14, Stack.leaf] at this; omega
  have hret := hr.small
  let Mem : Nat → ByteArray := storeWords m (ACC + 0x2000) (k14f m)
  let I : Nat → State := fun j => callState s 12530 (wd (32 * j) :: wd ret :: tail) (Mem j)
  have hentry : Reach (callState s 12528 (wd ret :: tail) m) (I 0) 3 := by
    simp only [I, Mem, Nat.mul_zero, storeWords_zero]
    opt87_reach [5324, 5325]
  have hbody : ∀ j, j < 255 → Reach (I j) (I (j + 1)) 115 := by
    intro j hj
    have h := k14_body hs htail (i := 32 * j) (ret := ret) (Mem j) (by omega)
    rw [k14_step m (by omega)] at h
    simp only [I, Mem]
    rw [show 32 * (j + 1) = 32 * j + 32 by ring]
    exact h
  have hlast : Reach (I 255) (callState s ret tail (Mem 256)) 125 := by
    have h := k14_last hs htail (ret := ret) (Mem 255)
    rw [show (8160 : Nat) = 32 * 255 by norm_num, k14_step m (by omega)] at h
    exact h.trans (reach_ret hs 5363 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit])
      (by simp only [finVal_lit, pcAt_lit]) (by norm_num) hr.jumpdest hret (by omega))
  have hv : ∀ t, k14f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
  · show FrameExcept m (storeWords m (ACC + 0x2000) (k14f m) 256) [(ACC + 0x2000, ACC + 0x4000)]
    have h := FrameExcept.storeWords m (ACC + 0x2000) (k14f m) 256
    simpa [ACC] using h
  · rw [call_iff, Entry.pass3k14, Gas.pass3k14]
    exact ((hentry.trans (Reach.loop 255 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt87.Proofs.GroupP
