import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f10` (ML-DSA-87): row group 1, columns 0 … 2 and column 3 rows 4 … 6 (stores)

128 iterations at `p = CW + 64 j`, two words each; `ACC + 0x2000` is disjoint
from every region read. `pass3f10_call_aux` states the post as the body of
`p3f10Word` with `bz`, `bzl` unfolded.
-/

namespace MlDsaOpt87.Proofs.Pass3fP10

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- Value stored at `p + 0xb900` by a word block (`p` in `CW`). -/
def v (M : ByteArray) (p : Nat) : Nat :=
  let z := word M (p + 0x5000)
  (word M p * lane z 0 + word M (p + 0xd900) * lane z 1 + word M (p + 0xf900) * lane z 2 +
    (word M (p + 0x2000) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z 3) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `opt_reach`) is `v`'s. -/
theorem arith {z x h g a : Nat} (hz : z < 2 ^ 256) :
    ((2 ^ 192 - 1 &&& a) * (z / 2 ^ 192) + (g * (M64 &&& z / 2 ^ 128) +
      (h * (M64 &&& z / 2 ^ 64) + x * (M64 &&& z)))) % 2 ^ 256 =
    (x * lane z 0 + h * lane z 1 + g * lane z 2 +
      (a &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z 3) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have h3 : z / 2 ^ 192 % 2 ^ 64 = z / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  have ha : (a &&& (2 ^ 192 - 1)) * 1 % 2 ^ 256 = (a &&& (2 ^ 192 - 1)) := by
    have := @Nat.and_le_right a (2 ^ 192 - 1)
    rw [Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.and_comm (2 ^ 192 - 1) a]
  simp only [hM, lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, h3, ha]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev K (ret : Nat) (tail : List UInt256) : List UInt256 := wd (2 ^ 192 - 1) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 12548 (wd p :: K ret tail) M)
      (callState s 12614 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0xb900))) 164 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5346, 5347, 5348, 5349, 5350, 5351, 5352, 5353, 5354, 5355, 5356, 5357, 5358, 5359, 5360, 5361, 5362, 5363, 5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398] with [v, M64]
  rw [show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega,
    show 47360 + p = p + 47360 by omega,
    show 55552 + p = p + 55552 by omega,
    show 63744 + p = p + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 12614 (wd p :: K ret tail) M)
      (callState s 12682 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0xb900))) 169 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433, 5434, 5435, 5436, 5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447, 5448, 5449, 5450, 5451, 5452] with [v, M64]
  rw [show 32 + p = p + 32 by omega,
    show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega,
    show 47392 + p = p + 32 + 47360 by omega,
    show 55584 + p = p + 32 + 55552 by omega,
    show 63776 + p = p + 32 + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

theorem tl {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 12682 (wd p :: K ret tail) M)
      (callState s 12548 (wd (p + 64) :: K ret tail) M) 28 := by
  opt87_reach [5453, 5454, 5455, 5456, 5457, 5458, 5459]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 12682 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 42 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  opt87_reach [5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461, 5462, 5463] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 12510 (wd ret :: tail) M) (callState s 12548 (wd 0x3000 :: K ret tail) M) 10 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  opt87_reach [5342, 5343, 5344, 5345] with [M64]

/-- Words outside the stored prefix are untouched. -/
theorem word_storeWords_out {m : ByteArray} {base : Nat} {f : Nat → Nat} {n a : Nat}
    (h : a + 32 ≤ base ∨ base + 32 * n ≤ a) : word (storeWords m base f n) a = word m a :=
  FrameExcept.word (FrameExcept.storeWords m base f n) (by
    simp only [Avoids, List.mem_singleton, forall_eq]; exact h)

/-- `(ACC + 8192)[t]`'s value as a function of `t`. -/
def f (m : ByteArray) (t : Nat) : Nat := v m (CW + 32 * t)

/-- `v` of a memory that differs from `m` only in `(ACC + 8192)[0, n)`, `n ≤ t`. -/
theorem v_store (m : ByteArray) {n t : Nat} (hn : n ≤ t) (ht : t < 256) :
    v (storeWords m (ACC + 8192) (f m) n) (CW + 32 * t) = f m t := by
  unfold f v
  simp only [CW, ACC] at *
  rw [word_storeWords_out (a := 12288 + 32 * t) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 8192) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 20480) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 55552) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 63744) (by omega)]

theorem next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m (ACC + 8192) (f m) n)
        (Data.Bytes.natToBytesPadded (v (storeWords m (ACC + 8192) (f m) n) p) 32) (p + 0xb900) =
      storeWords m (ACC + 8192) (f m) (n + 1) := by
  rw [storeWords_succ, hp, v_store m (Nat.le_refl n) hn]
  congr 1
  unfold CW ACC; omega

theorem iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 12548 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j)))
      (callState s 12682 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j + 2))) 333 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have h0 := w0 hs htail (ret := ret) (storeWords m (ACC + 8192) (f m) (2 * j)) hp
  rw [next m (by omega) (by omega)] at h0
  have h1 := w1 hs htail (ret := ret) (storeWords m (ACC + 8192) (f m) (2 * j + 1)) hp
  rw [next m (by omega) (by omega)] at h1
  exact h0.trans h1

theorem reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f10 (wd ret :: tail) m)
      (callState s ret tail (storeWords m (ACC + 8192) (f m) 256)) Gas.pass3f10 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 12548 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 361 := by
    intro j hj
    have h := (iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (tl hs htail (storeWords m (ACC + 8192) (f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m (ACC + 8192) (f m) 256)) 375 :=
    (iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (ex hs hr (storeWords m (ACC + 8192) (f m) 256))
  have hentry : Reach (callState s Entry.pass3f10 (wd ret :: tail) m) (I 0) 10 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW, Entry.pass3f10]
    exact en hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f10; omega)

end MlDsaOpt87.Proofs.Pass3fP10

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f10** with the post stated as the body of `p3f10Word` (`Fn/Group.lean`). -/
theorem pass3f10_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' ((ACC + 8192) + 32 * t) =
      (word m (CW + 32 * t) * zl m 0 t + word m (HP + 32 * t) * zl m 1 t +
        word m (HP + 8192 + 32 * t) * zl m 2 t +
        (word m (ABUF + 32 * t) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * zl m 3 t) % 2 ^ 256) ∧
      FrameExcept m m' [((ACC + 8192), (ACC + 8192) + 8192)] ∧
      Call s Entry.pass3f10 [] ret tail m [] m' Gas.pass3f10 := by
  have hv : ∀ t, Pass3fP10.f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m (ACC + 8192) (Pass3fP10.f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold Pass3fP10.f Pass3fP10.v
    simp only [zl, CW, ZH, HP, ACC, ABUF, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.add_zero, Nat.zero_add]
    rw [show 12288 + 32 * t + 8192 = 20480 + 32 * t by omega,
      show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 55552 = 67840 + 32 * t by omega,
      show 12288 + 32 * t + 63744 = 76032 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m (ACC + 8192) (Pass3fP10.f m) 256
  · exact Pass3fP10.reach hs hr m

end MlDsaOpt87.Proofs
