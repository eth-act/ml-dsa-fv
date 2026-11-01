import MlDsaOpt44.Fn.Group.Common
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # `pass3k4`: 256 iterations of `ACC[t] += kronWord t` (WP6) -/

namespace MlDsaOpt44.Proofs.GroupP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

theorem and_mod_of_lt {a b n : Nat} (hb : b < 2 ^ n) : a % 2 ^ n &&& b = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hj : j < n
  · simp [hj]
  · have : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

/-- The Kronecker term of `pass3k4` at byte offset `i` (no reduction of the
product: the `AND` with a word mask makes it redundant). -/
def k4v (M : ByteArray) (i : Nat) : Nat :=
  (word M (ACC + i) + ((word M (ABUF + i) &&& (2 ^ 256 - 2 ^ 128)) * (word M (ZH + i) / 2 ^ 128) &&&
    M64 * 2 ^ 192)) % 2 ^ 256

/-- Value `pass3k4` stores at `ACC[t]` (`kronWord` unfolded). -/
def k4f (m : ByteArray) (t : Nat) : Nat :=
  (word m (ACC + 32 * t) +
    ((word m (ABUF + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (word m (ZH + 32 * t) / 2 ^ 128) % 2 ^ 256 &&&
      (M64 * 2 ^ 192))) % 2 ^ 256

theorem k4_body {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {i ret : Nat} (M : ByteArray) (hi : i + 32 < 8192) :
    Reach (callState s 10645 (wd i :: wd ret :: tail) M)
      (callState s 10645 (wd (i + 32) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (k4v M i) 32) (ACC + i))) 100 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480,
    4481, 4482, 4483, 4484, 4485, 4486, 4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496]
    with [k4v, ACC, ABUF, ZH, M64]
  simp only [Nat.add_comm, Nat.mul_comm, Nat.and_comm, and_self]

theorem k4_last {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret : Nat} (M : ByteArray) :
    Reach (callState s 10645 (wd 8160 :: wd ret :: tail) M)
      (callState s 10753 (wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (k4v M 8160) 32) (ACC + 8160))) 102 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480,
    4481, 4482, 4483, 4484, 4485, 4486, 4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497]
    with [k4v, ACC, ABUF, ZH, M64]
  simp only [Nat.add_comm, Nat.mul_comm, Nat.and_comm, and_self]

theorem k4_step (m : ByteArray) {j : Nat} (hj : j < 256) :
    MachineState.writeBytes (storeWords m ACC (k4f m) j)
        (Data.Bytes.natToBytesPadded (k4v (storeWords m ACC (k4f m) j) (32 * j)) 32) (ACC + 32 * j) =
      storeWords m ACC (k4f m) (j + 1) := by
  refine storeWords_next rfl rfl ?_
  unfold k4v k4f
  rw [word_storeWords_out (a := ACC + 32 * j) (by omega),
    word_storeWords_out (a := ABUF + 32 * j) (by unfold ABUF ACC; omega),
    word_storeWords_out (a := ZH + 32 * j) (by unfold ZH ACC; omega),
    and_mod_of_lt (by unfold M64; norm_num)]

theorem pass3k4_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3k4 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) = (word m (ACC + 32 * t) +
        ((word m (ABUF + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (word m (ZH + 32 * t) / 2 ^ 128) % 2 ^ 256 &&&
          (M64 * 2 ^ 192))) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3k4 [] ret tail m [] m' Gas.pass3k4 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3k4, Stack.leaf] at this; omega
  have hret := hr.small
  let Mem : Nat → ByteArray := storeWords m ACC (k4f m)
  let I : Nat → State := fun j => callState s 10645 (wd (32 * j) :: wd ret :: tail) (Mem j)
  have hentry : Reach (callState s 10643 (wd ret :: tail) m) (I 0) 3 := by
    simp only [I, Mem, Nat.mul_zero, storeWords_zero]
    opt44_reach [4464, 4465]
  have hbody : ∀ j, j < 255 → Reach (I j) (I (j + 1)) 100 := by
    intro j hj
    have h := k4_body hs htail (i := 32 * j) (ret := ret) (Mem j) (by omega)
    rw [k4_step m (by omega)] at h
    simp only [I, Mem]
    rw [show 32 * (j + 1) = 32 * j + 32 by ring]
    exact h
  have hlast : Reach (I 255) (callState s ret tail (Mem 256)) 110 := by
    have h := k4_last hs htail (ret := ret) (Mem 255)
    rw [show (8160 : Nat) = 32 * 255 by norm_num, k4_step m (by omega)] at h
    exact h.trans (reach_ret hs 4498 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit])
      (by simp only [finVal_lit, pcAt_lit]) (by norm_num) hr.jumpdest hret (by omega))
  have hv : ∀ t, k4f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]; rfl
  · simpa using FrameExcept.storeWords m ACC (k4f m) 256
  · rw [call_iff, Entry.pass3k4, Gas.pass3k4]
    exact ((hentry.trans (Reach.loop 255 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt44.Proofs.GroupP
