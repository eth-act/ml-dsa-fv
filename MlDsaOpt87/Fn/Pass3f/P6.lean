import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f6` (ML-DSA-87): row group 0, columns 5, 6 (adds)

128 iterations at `p = CW + 64 j`, two words each: `ACC[t] += …`; word `t` of
`ACC` is read before it is written, so the post is about the original memory.
`pass3f6_call_aux` states the post as the body of `p3f6Word` with `bz` unfolded.
-/

namespace MlDsaOpt87.Proofs.Pass3fP6

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- Value stored at `p + 0x9900` by a word block (`p` in `CW`). -/
def v (M : ByteArray) (p : Nat) : Nat :=
  let z1 := word M (p + 0x7000)
  (word M (p + 0x9900) + word M p * lane z1 1 + word M (p + 0x2000) * lane z1 2) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `opt_reach`) is `v`'s. -/
theorem arith {z c x a : Nat} :
    (a * (M64 &&& z / 2 ^ 128) + (x * (M64 &&& z / 2 ^ 64) + c)) % 2 ^ 256 =
    (c + x * lane z 1 + a * lane z 2) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  simp only [hM, lane, Nat.reduceMul]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev K (ret : Nat) (tail : List UInt256) : List UInt256 := wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 12401 (wd p :: K ret tail) M)
      (callState s 12447 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0x9900))) 109 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5259, 5260, 5261, 5262, 5263, 5264, 5265, 5266, 5267, 5268, 5269, 5270, 5271, 5272, 5273, 5274, 5275, 5276, 5277, 5278, 5279, 5280, 5281, 5282, 5283, 5284, 5285, 5286, 5287, 5288, 5289, 5290, 5291, 5292, 5293, 5294] with [v, M64]
  rw [show 8192 + p = p + 8192 by omega,
    show 28672 + p = p + 28672 by omega,
    show 39168 + p = p + 39168 by omega]
  congr 2
  exact arith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 12447 (wd p :: K ret tail) M)
      (callState s 12495 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0x9900))) 114 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5295, 5296, 5297, 5298, 5299, 5300, 5301, 5302, 5303, 5304, 5305, 5306, 5307, 5308, 5309, 5310, 5311, 5312, 5313, 5314, 5315, 5316, 5317, 5318, 5319, 5320, 5321, 5322, 5323, 5324, 5325, 5326, 5327, 5328, 5329, 5330, 5331] with [v, M64]
  rw [show 32 + p = p + 32 by omega,
    show 8224 + p = p + 32 + 8192 by omega,
    show 28704 + p = p + 32 + 28672 by omega,
    show 39200 + p = p + 32 + 39168 by omega]
  congr 2
  exact arith

theorem tl {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 12495 (wd p :: K ret tail) M)
      (callState s 12401 (wd (p + 64) :: K ret tail) M) 28 := by
  opt87_reach [5332, 5333, 5334, 5335, 5336, 5337, 5338]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 12495 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 40 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  opt87_reach [5332, 5333, 5334, 5335, 5336, 5337, 5338, 5339, 5340, 5341] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 12388 (wd ret :: tail) M) (callState s 12401 (wd 0x3000 :: K ret tail) M) 7 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  opt87_reach [5256, 5257, 5258] with [M64]

/-- Words outside the stored prefix are untouched. -/
theorem word_storeWords_out {m : ByteArray} {base : Nat} {f : Nat → Nat} {n a : Nat}
    (h : a + 32 ≤ base ∨ base + 32 * n ≤ a) : word (storeWords m base f n) a = word m a :=
  FrameExcept.word (FrameExcept.storeWords m base f n) (by
    simp only [Avoids, List.mem_singleton, forall_eq]; exact h)

/-- `ACC[t]`'s value as a function of `t`. -/
def f (m : ByteArray) (t : Nat) : Nat := v m (CW + 32 * t)

/-- `v` of a memory that differs from `m` only in `ACC[0, n)`, `n ≤ t`. -/
theorem v_store (m : ByteArray) {n t : Nat} (hn : n ≤ t) (ht : t < 256) :
    v (storeWords m ACC (f m) n) (CW + 32 * t) = f m t := by
  unfold f v
  simp only [CW, ACC] at *
  rw [word_storeWords_out (a := 12288 + 32 * t) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 8192) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 28672) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 39168) (by omega)]

theorem next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m ACC (f m) n)
        (Data.Bytes.natToBytesPadded (v (storeWords m ACC (f m) n) p) 32) (p + 0x9900) =
      storeWords m ACC (f m) (n + 1) := by
  rw [storeWords_succ, hp, v_store m (Nat.le_refl n) hn]
  congr 1
  unfold CW ACC; omega

theorem iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 12401 (wd (CW + 64 * j) :: K ret tail) (storeWords m ACC (f m) (2 * j)))
      (callState s 12495 (wd (CW + 64 * j) :: K ret tail) (storeWords m ACC (f m) (2 * j + 2))) 223 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have h0 := w0 hs htail (ret := ret) (storeWords m ACC (f m) (2 * j)) hp
  rw [next m (by omega) (by omega)] at h0
  have h1 := w1 hs htail (ret := ret) (storeWords m ACC (f m) (2 * j + 1)) hp
  rw [next m (by omega) (by omega)] at h1
  exact h0.trans h1

theorem reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f6 (wd ret :: tail) m)
      (callState s ret tail (storeWords m ACC (f m) 256)) Gas.pass3f6 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 12401 (wd (CW + 64 * j) :: K ret tail) (storeWords m ACC (f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 251 := by
    intro j hj
    have h := (iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (tl hs htail (storeWords m ACC (f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m ACC (f m) 256)) 263 :=
    (iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (ex hs hr (storeWords m ACC (f m) 256))
  have hentry : Reach (callState s Entry.pass3f6 (wd ret :: tail) m) (I 0) 7 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW, Entry.pass3f6]
    exact en hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f6; omega)

end MlDsaOpt87.Proofs.Pass3fP6

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f6** with the post stated as the body of `p3f6Word` (`Fn/Group.lean`). -/
theorem pass3f6_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
      (word m (ACC + 32 * t) + word m (CW + 32 * t) * zl m 5 t +
        word m (ABUF + 32 * t) * zl m 6 t) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f6 [] ret tail m [] m' Gas.pass3f6 := by
  have hv : ∀ t, Pass3fP6.f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m ACC (Pass3fP6.f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold Pass3fP6.f Pass3fP6.v
    simp only [zl, CW, ZH, HP, ACC, ABUF, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.add_zero, Nat.zero_add]
    rw [show 12288 + 32 * t + 8192 = 20480 + 32 * t by omega,
      show 12288 + 32 * t + 28672 = 40960 + 32 * t by omega,
      show 12288 + 32 * t + 39168 = 51456 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m ACC (Pass3fP6.f m) 256
  · exact Pass3fP6.reach hs hr m

end MlDsaOpt87.Proofs
