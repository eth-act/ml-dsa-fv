import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Layout
/- Ported from `MlDsaOpt44/Fn/Group/Pass3f4.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f4`: the fused accumulation pass (WP C)

128 iterations at `p = CW + 64 j`, two words each: `ACC[t] := f4v m (CW + 32 t)`
(reads of the original memory: `ACC` is disjoint from every region read).
`pass3f4_call_aux` states the post as the body of `acc4Word` (`Fn/Group.lean`).
-/

namespace MlDsaOptGlam44.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

/-- Value stored at `p + 0x7900` by a word block reading `M` at `p + o` (`p` in `CW`). -/
def f4v (M : ByteArray) (p : Nat) : Nat :=
  let z := word M (p + 0x5000)
  (word M p * lane z 0 + word M (p + 0x9900) * lane z 1 +
    word M (p + 0xd700) / 2 ^ 64 * lane z 2 +
    ((word M (p + 0xf700) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
      (M64 * 2 ^ 192)) +
    word M (p + 0x2000) / 2 ^ 64 * lane z 3) % 2 ^ 256

theorem and_mod_of_lt {a b n : Nat} (hb : b < 2 ^ n) : a % 2 ^ n &&& b = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hj : j < n
  · simp [hj]
  · have : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

/-- The block's arithmetic (in the normal form of `glam44_rreach`) is `f4v`'s. -/
theorem f4_arith {z c h s1 s2 a : Nat} (hz : z < 2 ^ 256) :
    (a / 2 ^ 64 * (z / 2 ^ 192) +
      ((M64 * 2 ^ 192 &&& ((2 ^ 256 - 2 ^ 128) &&& s2) * (z / 2 ^ 128)) +
        (s1 / 2 ^ 64 * (M64 &&& z / 2 ^ 128) +
          (h * (M64 &&& z / 2 ^ 64) + c * (M64 &&& z))))) % 2 ^ 256 =
    (c * lane z 0 + h * lane z 1 + s1 / 2 ^ 64 * lane z 2 +
      ((s2 &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192)) +
      a / 2 ^ 64 * lane z 3) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have h3 : z / 2 ^ 192 % 2 ^ 64 = z / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  rw [and_mod_of_lt (by unfold M64; norm_num), hM, hM, hM]
  simp only [lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, h3]
  rw [Nat.and_comm (M64 * 2 ^ 192), Nat.and_comm (2 ^ 256 - 2 ^ 128)]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev f4K (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd (M64 * 2 ^ 192) :: wd (2 ^ 256 - 2 ^ 128) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f4_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 17104 (wd p :: f4K ret tail) M)
      (callState s 17191 (wd p :: f4K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f4v M p) 32) (p + 0x7900))) 214 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam44_rreach [6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811, 6812, 6813, 6814, 6815, 6816, 6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826, 6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842, 6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858, 6859, 6860] with [f4v, M64]
  rw [show 30976 + p = p + 30976 by omega, show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega, show 63232 + p = p + 63232 by omega,
    show 55040 + p = p + 55040 by omega, show 39168 + p = p + 39168 by omega]
  congr 2
  exact f4_arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f4_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 17191 (wd p :: f4K ret tail) M)
      (callState s 17280 (wd p :: f4K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f4v M (p + 32)) 32) (p + 32 + 0x7900))) 219 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam44_rreach [6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869, 6870, 6871, 6872, 6873, 6874, 6875, 6876, 6877, 6878, 6879, 6880, 6881, 6882, 6883, 6884, 6885, 6886, 6887, 6888, 6889, 6890, 6891, 6892, 6893, 6894, 6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905, 6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914, 6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925, 6926, 6927, 6928, 6929, 6930] with [f4v, M64]
  rw [show 31008 + p = p + 32 + 30976 by omega, show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega, show 63264 + p = p + 32 + 63232 by omega,
    show 55072 + p = p + 32 + 55040 by omega, show 39200 + p = p + 32 + 39168 by omega,
    show 32 + p = p + 32 by omega]
  congr 2
  exact f4_arith (word_lt M _)

theorem f4_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 17280 (wd p :: f4K ret tail) M)
      (callState s 17104 (wd (p + 64) :: f4K ret tail) M) 28 := by
  glam44_rreach [6931, 6932, 6933, 6934, 6935, 6936, 6937]
  simp only [Nat.add_comm, and_self]

theorem f4_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (M : ByteArray) :
    Reach (callState s 17280 (wd 0x4fc0 :: f4K ret tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.pass3f4, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [6931, 6932, 6933, 6934, 6935, 6936, 6937, 6938, 6939, 6940, 6941, 6942] with [hj]

theorem f4_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (M : ByteArray) :
    Reach (callState s 17025 (wd ret :: tail) M) (callState s 17104 (wd 0x3000 :: f4K ret tail) M) 13 := by
  have := hr.depth; simp only [Stack.pass3f4, Stack.leaf] at this
  glam44_rreach [6787, 6788, 6789, 6790, 6791] with [M64]

/-- `ACC[t]`'s value as a function of `t`. -/
def f4f (m : ByteArray) (t : Nat) : Nat := f4v m (CW + 32 * t)

/-- `f4v` of a memory that differs from `m` only in `ACC[0, n)`. -/
theorem f4v_store (m : ByteArray) {n t : Nat} (hn : n ≤ 256) (ht : t < 256) :
    f4v (storeWords m ACC (f4f m) n) (CW + 32 * t) = f4f m t := by
  unfold f4f f4v
  simp only [CW, ACC] at *
  rw [WP4.word_storeWords_out (a := 12288 + 32 * t) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 20480) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0x9900) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0xd700) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0xf700) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0x2000) (by omega)]

theorem f4_next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m ACC (f4f m) n)
        (Data.Bytes.natToBytesPadded (f4v (storeWords m ACC (f4f m) n) p) 32) (p + 0x7900) =
      storeWords m ACC (f4f m) (n + 1) := by
  rw [storeWords_succ, hp, f4v_store m (by omega) hn]
  congr 1
  unfold CW ACC; omega

theorem f4_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 17104 (wd (CW + 64 * j) :: f4K ret tail) (storeWords m ACC (f4f m) (2 * j)))
      (callState s 17280 (wd (CW + 64 * j) :: f4K ret tail) (storeWords m ACC (f4f m) (2 * j + 2))) 433 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have w0 := f4_w0 hs htail (ret := ret) (storeWords m ACC (f4f m) (2 * j)) hp
  rw [f4_next m (by omega) (by omega)] at w0
  have w1 := f4_w1 hs htail (ret := ret) (storeWords m ACC (f4f m) (2 * j + 1)) hp
  rw [f4_next m (by omega) (by omega)] at w1
  exact w0.trans w1

theorem pass3f4_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f4 (wd ret :: tail) m)
      (callState s ret tail (storeWords m ACC (f4f m) 256)) Gas.pass3f4 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f4, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 17104 (wd (CW + 64 * j) :: f4K ret tail) (storeWords m ACC (f4f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 461 := by
    intro j hj
    have h := (f4_iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (f4_tail hs htail (storeWords m ACC (f4f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m ACC (f4f m) 256)) 477 :=
    (f4_iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (f4_exit hs hr (storeWords m ACC (f4f m) 256))
  have hentry : Reach (callState s Entry.pass3f4 (wd ret :: tail) m) (I 0) 13 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW]
    exact f4_entry hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f4; omega)

end MlDsaOptGlam44.Proofs.GroupP

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f4** with the post stated as the body of `acc4Word` (`Fn/Group.lean`). -/
theorem pass3f4_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        let z := word m (ZH + 32 * t)
        (word m (CW + 32 * t) * lane z 0 + word m (HP + 32 * t) * lane z 1 +
          word m (SB + 32 * t) / 2 ^ 64 * lane z 2 +
          ((word m (SB + 8192 + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
            (M64 * 2 ^ 192)) +
          word m (ABUF + 32 * t) / 2 ^ 64 * lane z 3) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f4 [] ret tail m [] m' Gas.pass3f4 := by
  have hv : ∀ t, GroupP.f4f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m ACC (GroupP.f4f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold GroupP.f4f GroupP.f4v
    simp only [CW, ZH, HP, SB, ABUF]
    rw [show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 0x9900 = 51456 + 32 * t by omega,
      show 12288 + 32 * t + 0xd700 = 67328 + 32 * t by omega,
      show 12288 + 32 * t + 0xf700 = 67328 + 8192 + 32 * t by omega,
      show 12288 + 32 * t + 0x2000 = 20480 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m ACC (GroupP.f4f m) 256
  · exact GroupP.pass3f4_reach hs hr m

end MlDsaOptGlam44.Proofs
