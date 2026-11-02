import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam65.Fn.Pack65.P3f7
set_option maxHeartbeats 0
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f8`: row group 1 of 65's interleaved fused pass

128 iterations at `p = ABUF + 64 j`, two words each:
`(ACC + 0x2000)[t] := f8v m (ABUF + 32 t)` (the target is disjoint from every
other region read, and its own word is read before it is written). Addresses, entry pc and costs are literals here; the wrapper in
`Fn/Pack65.lean` restates the contract with the layout names.
-/

namespace MlDsaOptGlam65.Proofs.Pack65

open MlDsaOpt44.Proofs (M64 lane Call call_iff)
open MlDsaOpt44.Proofs.WP4 (word_storeWords_out)

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

/-- Value stored at `p + 0x9900` by a word block of `pass3f8` (`p` in `ABUF`). -/
def f8v (M : ByteArray) (p : Nat) : Nat :=
  let z0 := word M (p + 0x3000)
  let z1 := word M (p + 0x5000)
  (word M (p + 0x9900) * z0 % 2 ^ 256 / 2 ^ 192 +
    (word M (p + 0x11700) * z0 % 2 ^ 256 &&& (M64 * 2 ^ 192)) / 2 ^ 128 +
    (word M p &&& (2 ^ 128 - 1)) * lane z1 0) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `glam65_rreach`) is `f8v`'s. -/
theorem f8_arith {z0 z1 a b c : Nat} :
    ((2 ^ 128 - 1 &&& c) * (M64 &&& z1) +
      ((M64 * 2 ^ 192 &&& b * z0) % 2 ^ 256 / 2 ^ 128 + a * z0 % 2 ^ 256 / 2 ^ 192)) % 2 ^ 256 =
    (a * z0 % 2 ^ 256 / 2 ^ 192 + (b * z0 % 2 ^ 256 &&& (M64 * 2 ^ 192)) / 2 ^ 128 +
      (c &&& (2 ^ 128 - 1)) * lane z1 0) % 2 ^ 256 := by
  have hM : M64 * 2 ^ 192 < 2 ^ 256 := by unfold M64; norm_num
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hM), Nat.and_comm (M64 * 2 ^ 192),
    ← and_mod_of_lt (n := 256) hM, M64_and, Nat.and_comm (2 ^ 128 - 1)]
  simp only [lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev f8K (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd (M64 * 2 ^ 192) :: wd (2 ^ 128 - 1) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f8_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x7000) :
    Reach (callState s 17116 (wd p :: f8K ret tail) M)
      (callState s 17173 (wd p :: f8K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f8v M p) 32) (p + 0x9900))) 135 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [6923, 6924, 6925, 6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933, 6934, 6935, 6936, 6937, 6938, 6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946, 6947, 6948, 6949, 6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966] with [f8v, M64]
  rw [show 20480 + p = p + 20480 by omega, show 12288 + p = p + 12288 by omega,
    show 71424 + p = p + 71424 by omega, show 39168 + p = p + 39168 by omega]
  congr 2
  exact f8_arith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f8_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x7000) :
    Reach (callState s 17173 (wd p :: f8K ret tail) M)
      (callState s 17232 (wd p :: f8K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f8v M (p + 32)) 32) (p + 32 + 0x9900))) 140 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006, 7007, 7008, 7009, 7010, 7011] with [f8v, M64]
  rw [show 20512 + p = p + 32 + 20480 by omega, show 12320 + p = p + 32 + 12288 by omega,
    show 71456 + p = p + 32 + 71424 by omega, show 39200 + p = p + 32 + 39168 by omega,
    show 32 + p = p + 32 by omega]
  congr 2
  exact f8_arith

theorem f8_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x7000) :
    Reach (callState s 17232 (wd p :: f8K ret tail) M)
      (callState s 17116 (wd (p + 64) :: f8K ret tail) M) 28 := by
  glam65_rreach [7012, 7013, 7014, 7015, 7016, 7017, 7018]
  simp only [Nat.add_comm, and_self]

theorem f8_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (M : ByteArray) :
    Reach (callState s 17232 (wd 0x6fc0 :: f8K ret tail) M) (callState s ret tail M) 44 := by
  have := hr.depth
  have hret := hr.small
  have hj := hr.jumpdest
  glam65_rreach [7012, 7013, 7014, 7015, 7016, 7017, 7018, 7019, 7020, 7021, 7022, 7023] with [hj]

theorem f8_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (M : ByteArray) :
    Reach (callState s 17053 (wd ret :: tail) M) (callState s 17116 (wd 0x5000 :: f8K ret tail) M) 13 := by
  have := hr.depth
  glam65_rreach [6918, 6919, 6920, 6921, 6922] with [M64]

/-- `(ACC + 0x2000)[t]`'s value as a function of `t`. -/
def f8f (m : ByteArray) (t : Nat) : Nat := f8v m (0x5000 + 32 * t)

/-- `f8v` of a memory that differs from `m` only in `(ACC + 0x2000)[0, n)`, `n ≤ t`. -/
theorem f8v_store (m : ByteArray) {n t : Nat} (hn : n ≤ t) (ht : t < 256) :
    f8v (storeWords m 0xe900 (f8f m) n) (0x5000 + 32 * t) = f8f m t := by
  unfold f8f f8v
  rw [word_storeWords_out (a := 0x5000 + 32 * t) (by omega),
    word_storeWords_out (a := 0x5000 + 32 * t + 0x3000) (by omega),
    word_storeWords_out (a := 0x5000 + 32 * t + 0x5000) (by omega),
    word_storeWords_out (a := 0x5000 + 32 * t + 0x9900) (by omega),
    word_storeWords_out (a := 0x5000 + 32 * t + 0x11700) (by omega)]

theorem f8_next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = 0x5000 + 32 * n) :
    MachineState.writeBytes (storeWords m 0xe900 (f8f m) n)
        (Data.Bytes.natToBytesPadded (f8v (storeWords m 0xe900 (f8f m) n) p) 32) (p + 0x9900) =
      storeWords m 0xe900 (f8f m) (n + 1) := by
  rw [storeWords_succ, hp, f8v_store m le_rfl hn]
  congr 1
  omega

theorem f8_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 17116 (wd (0x5000 + 64 * j) :: f8K ret tail) (storeWords m 0xe900 (f8f m) (2 * j)))
      (callState s 17232 (wd (0x5000 + 64 * j) :: f8K ret tail)
        (storeWords m 0xe900 (f8f m) (2 * j + 2))) 275 := by
  have hp : 0x5000 + 64 * j + 64 ≤ 0x7000 := by omega
  have w0 := f8_w0 hs htail (ret := ret) (storeWords m 0xe900 (f8f m) (2 * j)) hp
  rw [f8_next m (by omega) (by omega)] at w0
  have w1 := f8_w1 hs htail (ret := ret) (storeWords m 0xe900 (f8f m) (2 * j + 1)) hp
  rw [f8_next m (by omega) (by omega)] at w1
  exact w0.trans w1

theorem pass3f8_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (m : ByteArray) :
    Reach (callState s 17053 (wd ret :: tail) m)
      (callState s ret tail (storeWords m 0xe900 (f8f m) 256)) 38813 := by
  have htail : tail.length ≤ 960 := by have := hr.depth; omega
  let I : Nat → State := fun j =>
    callState s 17116 (wd (0x5000 + 64 * j) :: f8K ret tail) (storeWords m 0xe900 (f8f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 303 := by
    intro j hj
    have h := (f8_iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (f8_tail hs htail (storeWords m 0xe900 (f8f m) (2 * j + 2)) (p := 0x5000 + 64 * j) (ret := ret)
        (by omega))
    simp only [I]
    rw [show 0x5000 + 64 * (j + 1) = 0x5000 + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m 0xe900 (f8f m) 256)) 319 :=
    (f8_iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (f8_exit hs hr (storeWords m 0xe900 (f8f m) 256))
  have hentry : Reach (callState s 17053 (wd ret :: tail) m) (I 0) 13 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    exact f8_entry hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by omega)

/-- **pass3f8**, the body of `p3f8Word` with the layout constants as literals
(`ZH = 0x8000`, `ACC = 0xc900`, `SB = 0x16700`, `ABUF = 0x5000`). -/
theorem pass3f8_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (0xc900 + 8192 + 32 * t) =
        let z0 := word m (0x8000 + 32 * t)
        let z1 := word m (0x8000 + 8192 + 32 * t)
        (word m (0xc900 + 8192 + 32 * t) * z0 % 2 ^ 256 / 2 ^ 192 +
          (word m (0x16700 + 32 * t) * z0 % 2 ^ 256 &&& (M64 * 2 ^ 192)) / 2 ^ 128 +
          (word m (0x5000 + 32 * t) &&& (2 ^ 128 - 1)) * lane z1 0) % 2 ^ 256) ∧
      FrameExcept m m' [(0xc900 + 8192, 0xc900 + 8192 + 8192)] ∧
      Call s 17053 [] ret tail m [] m' 38813 := by
  have hv : ∀ t, f8f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m 0xe900 (f8f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [show 0xc900 + 8192 + 32 * t = 0xe900 + 32 * t by omega, word_storeWords (hv t) 256 ht]
    unfold f8f f8v
    rw [show 0x5000 + 32 * t + 0x3000 = 0x8000 + 32 * t by omega,
      show 0x5000 + 32 * t + 0x5000 = 0x8000 + 8192 + 32 * t by omega,
      show 0x5000 + 32 * t + 0x9900 = 0xc900 + 8192 + 32 * t by omega,
      show 0x5000 + 32 * t + 0x11700 = 0x16700 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m 0xe900 (f8f m) 256
  · rw [call_iff]
    simpa using pass3f8_reach hs hr m

end MlDsaOptGlam65.Proofs.Pack65
