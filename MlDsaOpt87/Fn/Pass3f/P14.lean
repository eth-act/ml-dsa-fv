import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f14` (ML-DSA-87): row group 1, columns 4 … 6 rows 4 … 6, row 7 columns 3 … 6 (adds)

128 iterations at `p = CW + 64 j`, two words each: `ACC[2048 + t] += …`;
word `t` of `ACC + 0x2000` is read before it is written, so the post is about
the original memory. `pass3f14_call_aux` states the post as the body of
`p3f14Word` with `bzl`, `kron14` unfolded.
-/

namespace MlDsaOpt87.Proofs.Pass3fP14

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- Value stored at `p + 0xb900` by a word block (`p` in `CW`). -/
def v (M : ByteArray) (p : Nat) : Nat :=
  let z1 := word M (p + 0x7000)
  (word M (p + 0xb900) + (word M p &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z1 0 +
    (word M (p + 0xd900) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z1 1 +
    (word M (p + 0xf900) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z1 2 +
    (word M (p + 0x2000) * (word M (p + 0x5000) / 2 ^ 192 ||| z1 * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&&
      (M64 * 2 ^ 192))) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `opt_reach`) is `v`'s. -/
theorem arith {z0 z1 c x h g a : Nat} (hz : z0 < 2 ^ 256) :
    ((M64 * 2 ^ 192 &&& a * (z1 * 2 ^ 64 ||| z0 / 2 ^ 192)) +
      ((2 ^ 192 - 1 &&& g) * (M64 &&& z1 / 2 ^ 128) +
        ((2 ^ 192 - 1 &&& h) * (M64 &&& z1 / 2 ^ 64) +
          ((2 ^ 192 - 1 &&& x) * (M64 &&& z1) + c)))) % 2 ^ 256 =
    (c + (x &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z1 0 +
      (h &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z1 1 +
      (g &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z1 2 +
      (a * (z0 / 2 ^ 192 ||| z1 * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&& (M64 * 2 ^ 192))) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have hL : ∀ y, (y &&& (2 ^ 192 - 1)) * 1 % 2 ^ 256 = y &&& (2 ^ 192 - 1) := fun y => by
    have := @Nat.and_le_right y (2 ^ 192 - 1)
    rw [Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
  have hK : M64 * 2 ^ 192 < 2 ^ 256 := by unfold M64; norm_num
  have hy : z0 / 2 ^ 192 < 2 ^ 256 := by omega
  have hk : a * (z0 / 2 ^ 192 ||| z1 * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&& (M64 * 2 ^ 192) =
      M64 * 2 ^ 192 &&& a * (z1 * 2 ^ 64 ||| z0 / 2 ^ 192) := by
    have e1 : (z0 / 2 ^ 192 ||| z1 * 2 ^ 64 % 2 ^ 256) = (z1 * 2 ^ 64 ||| z0 / 2 ^ 192) % 2 ^ 256 := by
      rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt hy, Nat.or_comm]
    rw [e1, Nat.mul_mod_mod, Nat.and_comm, and_mod_of_lt' hK]
  rw [hk, Nat.and_comm (2 ^ 192 - 1) g, Nat.and_comm (2 ^ 192 - 1) h, Nat.and_comm (2 ^ 192 - 1) x]
  simp only [hM, lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, hL]
  congr 1
  ring
where
  and_mod_of_lt' {a b n : Nat} (hb : b < 2 ^ n) : b &&& a % 2 ^ n = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
    by_cases hj : j < n
    · simp [hj]
    · have : b.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hj, this]

/-- The loop's constant stack below the pointer. -/
abbrev K (ret : Nat) (tail : List UInt256) : List UInt256 := wd (M64 * 2 ^ 192) :: wd (2 ^ 192 - 1) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 12769 (wd p :: K ret tail) M)
      (callState s 12858 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0xb900))) 218 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5469, 5470, 5471, 5472, 5473, 5474, 5475, 5476, 5477, 5478, 5479, 5480, 5481, 5482, 5483, 5484, 5485, 5486, 5487, 5488, 5489, 5490, 5491, 5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501, 5502, 5503, 5504, 5505, 5506, 5507, 5508, 5509, 5510, 5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519, 5520, 5521, 5522, 5523, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533, 5534, 5535, 5536, 5537, 5538, 5539] with [v, M64]
  rw [show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega,
    show 28672 + p = p + 28672 by omega,
    show 47360 + p = p + 47360 by omega,
    show 55552 + p = p + 55552 by omega,
    show 63744 + p = p + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 12858 (wd p :: K ret tail) M)
      (callState s 12949 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0xb900))) 223 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547, 5548, 5549, 5550, 5551, 5552, 5553, 5554, 5555, 5556, 5557, 5558, 5559, 5560, 5561, 5562, 5563, 5564, 5565, 5566, 5567, 5568, 5569, 5570, 5571, 5572, 5573, 5574, 5575, 5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591, 5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600, 5601, 5602, 5603, 5604, 5605, 5606, 5607, 5608, 5609, 5610, 5611] with [v, M64]
  rw [show 32 + p = p + 32 by omega,
    show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega,
    show 28704 + p = p + 32 + 28672 by omega,
    show 47392 + p = p + 32 + 47360 by omega,
    show 55584 + p = p + 32 + 55552 by omega,
    show 63776 + p = p + 32 + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

theorem tl {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 12949 (wd p :: K ret tail) M)
      (callState s 12769 (wd (p + 64) :: K ret tail) M) 28 := by
  opt87_reach [5612, 5613, 5614, 5615, 5616, 5617, 5618]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 12949 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  opt87_reach [5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619, 5620, 5621, 5622, 5623] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 12698 (wd ret :: tail) M) (callState s 12769 (wd 0x3000 :: K ret tail) M) 13 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  opt87_reach [5464, 5465, 5466, 5467, 5468] with [M64]

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
    word_storeWords_out (a := 12288 + 32 * t + 28672) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 47360) (by omega),
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
    Reach (callState s 12769 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j)))
      (callState s 12949 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j + 2))) 441 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have h0 := w0 hs htail (ret := ret) (storeWords m (ACC + 8192) (f m) (2 * j)) hp
  rw [next m (by omega) (by omega)] at h0
  have h1 := w1 hs htail (ret := ret) (storeWords m (ACC + 8192) (f m) (2 * j + 1)) hp
  rw [next m (by omega) (by omega)] at h1
  exact h0.trans h1

theorem reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f14 (wd ret :: tail) m)
      (callState s ret tail (storeWords m (ACC + 8192) (f m) 256)) Gas.pass3f14 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 12769 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 469 := by
    intro j hj
    have h := (iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (tl hs htail (storeWords m (ACC + 8192) (f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m (ACC + 8192) (f m) 256)) 485 :=
    (iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (ex hs hr (storeWords m (ACC + 8192) (f m) 256))
  have hentry : Reach (callState s Entry.pass3f14 (wd ret :: tail) m) (I 0) 13 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW, Entry.pass3f14]
    exact en hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f14; omega)

end MlDsaOpt87.Proofs.Pass3fP14

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f14** with the post stated as the body of `p3f14Word` (`Fn/Group.lean`). -/
theorem pass3f14_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' ((ACC + 8192) + 32 * t) =
      (word m (ACC + 8192 + 32 * t) +
        (word m (CW + 32 * t) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * zl m 4 t +
        (word m (HP + 32 * t) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * zl m 5 t +
        (word m (HP + 8192 + 32 * t) &&& (2 ^ 192 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * zl m 6 t +
        (word m (ABUF + 32 * t) *
            (word m (ZH + 32 * t) / 2 ^ 192 ||| word m (ZH + 8192 + 32 * t) * 2 ^ 64 % 2 ^ 256) %
              2 ^ 256 &&& (M64 * 2 ^ 192))) % 2 ^ 256) ∧
      FrameExcept m m' [((ACC + 8192), (ACC + 8192) + 8192)] ∧
      Call s Entry.pass3f14 [] ret tail m [] m' Gas.pass3f14 := by
  have hv : ∀ t, Pass3fP14.f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m (ACC + 8192) (Pass3fP14.f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold Pass3fP14.f Pass3fP14.v
    simp only [zl, CW, ZH, HP, ACC, ABUF, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.add_zero, Nat.zero_add]
    rw [show 12288 + 32 * t + 8192 = 20480 + 32 * t by omega,
      show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 28672 = 40960 + 32 * t by omega,
      show 12288 + 32 * t + 47360 = 59648 + 32 * t by omega,
      show 12288 + 32 * t + 55552 = 67840 + 32 * t by omega,
      show 12288 + 32 * t + 63744 = 76032 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m (ACC + 8192) (Pass3fP14.f m) 256
  · exact Pass3fP14.reach hs hr m

end MlDsaOpt87.Proofs
