import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam65.Infra.Reflect
set_option maxHeartbeats 0
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f7`: row group 0 of 65's interleaved fused pass

128 iterations at `p = CW + 64 j`, two words each: `ACC[t] := f7v m (CW + 32 t)`
(`ACC` is disjoint from every region read, and its own word is read before it
is written). Addresses, entry pc and costs are literals here; the wrapper in
`Fn/Pack65.lean` restates the contract with the layout names.
-/

namespace MlDsaOptGlam65.Proofs.Pack65

open MlDsaOpt44.Proofs (M64 lane Call call_iff)
open MlDsaOpt44.Proofs.WP4 (word_storeWords_out)

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

/-- Value stored at `p + 0x9900` by a word block of `pass3f7` (`p` in `CW`). -/
def f7v (M : ByteArray) (p : Nat) : Nat :=
  let z0 := word M (p + 0x5000)
  let z1 := word M (p + 0x7000)
  (word M p * lane z0 0 + word M (p + 0xd900) * lane z0 1 +
    word M (p + 0xf900) * lane z0 2 + word M (p + 0x9900) / 2 ^ 64 * lane z0 3 +
    word M (p + 0x15700) / 2 ^ 64 * lane z1 0 +
    ((word M (p + 0x2000) &&& (2 ^ 256 - 2 ^ 128)) * (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) % 2 ^ 256 &&&
      (M64 * 2 ^ 192))) % 2 ^ 256

theorem and_mod_of_lt {a b n : Nat} (hb : b < 2 ^ n) : a % 2 ^ n &&& b = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hj : j < n
  · simp [hj]
  · have : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

theorem M64_and (x : Nat) : M64 &&& x = x % 2 ^ 64 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64

/-- The Kronecker term: the block multiplies the unreduced `(z1 << 64) | (z0 >> 192)`
and masks the unreduced product (both reductions are absorbed by the mask). -/
theorem kron_mod {a z1 z0 : Nat} :
    (M64 * 2 ^ 192 &&& ((2 ^ 256 - 2 ^ 128) &&& a) * (z1 * 2 ^ 64 ||| z0 / 2 ^ 192)) =
      ((a &&& (2 ^ 256 - 2 ^ 128)) * (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) % 2 ^ 256 &&&
        (M64 * 2 ^ 192)) := by
  have hM : M64 * 2 ^ 192 < 2 ^ 256 := by unfold M64; norm_num
  rw [Nat.and_comm (M64 * 2 ^ 192), ← and_mod_of_lt (n := 256) hM, Nat.and_comm a]
  congr 1
  rw [Nat.mul_mod, Nat.or_mod_two_pow]
  conv_rhs => rw [Nat.mul_mod, Nat.or_mod_two_pow, Nat.mod_mod]

/-- The block's arithmetic (in the normal form of `glam65_rreach`) is `f7v`'s. -/
theorem f7_arith {z0 z1 c h h2 acc s a : Nat} (hz : z0 < 2 ^ 256) :
    ((M64 * 2 ^ 192 &&& ((2 ^ 256 - 2 ^ 128) &&& a) * (z1 * 2 ^ 64 ||| z0 / 2 ^ 192)) +
      (s / 2 ^ 64 * (M64 &&& z1) +
        (acc / 2 ^ 64 * (z0 / 2 ^ 192) +
          (h2 * (M64 &&& z0 / 2 ^ 128) + (h * (M64 &&& z0 / 2 ^ 64) + c * (M64 &&& z0)))))) % 2 ^ 256 =
    (c * lane z0 0 + h * lane z0 1 + h2 * lane z0 2 + acc / 2 ^ 64 * lane z0 3 +
      s / 2 ^ 64 * lane z1 0 +
      ((a &&& (2 ^ 256 - 2 ^ 128)) * (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) % 2 ^ 256 &&&
        (M64 * 2 ^ 192))) % 2 ^ 256 := by
  have h3 : z0 / 2 ^ 192 % 2 ^ 64 = z0 / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  rw [kron_mod, M64_and, M64_and, M64_and, M64_and]
  simp only [lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, h3]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev f7K (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd (M64 * 2 ^ 192) :: wd (2 ^ 256 - 2 ^ 128) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f7_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 16810 (wd p :: f7K ret tail) M)
      (callState s 16922 (wd p :: f7K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f7v M p) 32) (p + 0x9900))) 272 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [6729, 6730, 6731, 6732, 6733, 6734, 6735, 6736, 6737, 6738, 6739, 6740, 6741, 6742, 6743, 6744, 6745, 6746, 6747, 6748, 6749, 6750, 6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773, 6774, 6775, 6776, 6777, 6778, 6779, 6780, 6781, 6782, 6783, 6784, 6785, 6786, 6787, 6788, 6789, 6790, 6791, 6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811, 6812, 6813, 6814, 6815, 6816] with [f7v, M64]
  rw [show 20480 + p = p + 20480 by omega, show 28672 + p = p + 28672 by omega,
    show 8192 + p = p + 8192 by omega, show 87808 + p = p + 87808 by omega,
    show 39168 + p = p + 39168 by omega, show 63744 + p = p + 63744 by omega,
    show 55552 + p = p + 55552 by omega]
  congr 2
  exact f7_arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f7_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 16922 (wd p :: f7K ret tail) M)
      (callState s 17036 (wd p :: f7K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f7v M (p + 32)) 32) (p + 32 + 0x9900))) 277 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826, 6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842, 6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858, 6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869, 6870, 6871, 6872, 6873, 6874, 6875, 6876, 6877, 6878, 6879, 6880, 6881, 6882, 6883, 6884, 6885, 6886, 6887, 6888, 6889, 6890, 6891, 6892, 6893, 6894, 6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905] with [f7v, M64]
  rw [show 20512 + p = p + 32 + 20480 by omega, show 28704 + p = p + 32 + 28672 by omega,
    show 8224 + p = p + 32 + 8192 by omega, show 87840 + p = p + 32 + 87808 by omega,
    show 39200 + p = p + 32 + 39168 by omega, show 63776 + p = p + 32 + 63744 by omega,
    show 55584 + p = p + 32 + 55552 by omega, show 32 + p = p + 32 by omega]
  congr 2
  exact f7_arith (word_lt M _)

theorem f7_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 17036 (wd p :: f7K ret tail) M)
      (callState s 16810 (wd (p + 64) :: f7K ret tail) M) 28 := by
  glam65_rreach [6906, 6907, 6908, 6909, 6910, 6911, 6912]
  simp only [Nat.add_comm, and_self]

theorem f7_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (M : ByteArray) :
    Reach (callState s 17036 (wd 0x4fc0 :: f7K ret tail) M) (callState s ret tail M) 44 := by
  have := hr.depth
  have hret := hr.small
  have hj := hr.jumpdest
  glam65_rreach [6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914, 6915, 6916, 6917] with [hj]

theorem f7_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (M : ByteArray) :
    Reach (callState s 16731 (wd ret :: tail) M) (callState s 16810 (wd 0x3000 :: f7K ret tail) M) 13 := by
  have := hr.depth
  glam65_rreach [6724, 6725, 6726, 6727, 6728] with [M64]

/-- `ACC[t]`'s value as a function of `t`. -/
def f7f (m : ByteArray) (t : Nat) : Nat := f7v m (0x3000 + 32 * t)

/-- `f7v` of a memory that differs from `m` only in `ACC[0, n)`, `n ≤ t`. -/
theorem f7v_store (m : ByteArray) {n t : Nat} (hn : n ≤ t) (ht : t < 256) :
    f7v (storeWords m 0xc900 (f7f m) n) (0x3000 + 32 * t) = f7f m t := by
  unfold f7f f7v
  rw [word_storeWords_out (a := 0x3000 + 32 * t) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0x5000) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0x7000) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0xd900) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0xf900) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0x9900) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0x15700) (by omega),
    word_storeWords_out (a := 0x3000 + 32 * t + 0x2000) (by omega)]

theorem f7_next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = 0x3000 + 32 * n) :
    MachineState.writeBytes (storeWords m 0xc900 (f7f m) n)
        (Data.Bytes.natToBytesPadded (f7v (storeWords m 0xc900 (f7f m) n) p) 32) (p + 0x9900) =
      storeWords m 0xc900 (f7f m) (n + 1) := by
  rw [storeWords_succ, hp, f7v_store m le_rfl hn]
  congr 1
  omega

theorem f7_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 16810 (wd (0x3000 + 64 * j) :: f7K ret tail) (storeWords m 0xc900 (f7f m) (2 * j)))
      (callState s 17036 (wd (0x3000 + 64 * j) :: f7K ret tail)
        (storeWords m 0xc900 (f7f m) (2 * j + 2))) 549 := by
  have hp : 0x3000 + 64 * j + 64 ≤ 0x5000 := by omega
  have w0 := f7_w0 hs htail (ret := ret) (storeWords m 0xc900 (f7f m) (2 * j)) hp
  rw [f7_next m (by omega) (by omega)] at w0
  have w1 := f7_w1 hs htail (ret := ret) (storeWords m 0xc900 (f7f m) (2 * j + 1)) hp
  rw [f7_next m (by omega) (by omega)] at w1
  exact w0.trans w1

theorem pass3f7_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (m : ByteArray) :
    Reach (callState s 16731 (wd ret :: tail) m)
      (callState s ret tail (storeWords m 0xc900 (f7f m) 256)) 73885 := by
  have htail : tail.length ≤ 960 := by have := hr.depth; omega
  let I : Nat → State := fun j =>
    callState s 16810 (wd (0x3000 + 64 * j) :: f7K ret tail) (storeWords m 0xc900 (f7f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 577 := by
    intro j hj
    have h := (f7_iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (f7_tail hs htail (storeWords m 0xc900 (f7f m) (2 * j + 2)) (p := 0x3000 + 64 * j) (ret := ret)
        (by omega))
    simp only [I]
    rw [show 0x3000 + 64 * (j + 1) = 0x3000 + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m 0xc900 (f7f m) 256)) 593 :=
    (f7_iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (f7_exit hs hr (storeWords m 0xc900 (f7f m) 256))
  have hentry : Reach (callState s 16731 (wd ret :: tail) m) (I 0) 13 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    exact f7_entry hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by omega)

/-- **pass3f7** with literal addresses (`CW = 0x3000`, `ACC = 0xc900`). -/
theorem pass3f7_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (0xc900 + 32 * t) = f7v m (0x3000 + 32 * t)) ∧
      FrameExcept m m' [(0xc900, 0xc900 + 8192)] ∧
      Call s 16731 [] ret tail m [] m' 73885 := by
  have hv : ∀ t, f7f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m 0xc900 (f7f m) 256, fun t ht => word_storeWords (hv t) 256 ht, ?_, ?_⟩
  · simpa using FrameExcept.storeWords m 0xc900 (f7f m) 256
  · rw [call_iff]
    simpa using pass3f7_reach hs hr m

end MlDsaOptGlam65.Proofs.Pack65
