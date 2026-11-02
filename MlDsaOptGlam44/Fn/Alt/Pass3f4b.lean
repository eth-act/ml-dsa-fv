import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam44.Fn.Group.Pass3f4
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Layout
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f4b`: the long-message schedule's fused accumulation pass

128 iterations at `p = CW + 64 j`, two words each: `ACC[t] := fbv m (CW + 32 t)`
(reads of the original memory: `ACC` is disjoint from every region read). The
loop is `pass3f4`'s (`Fn/Group/Pass3f4.lean`) with a fifth constant on the stack
(`2^192 − 1`, masking lane 3 off `SB`, `SB + 8192`) and the Kronecker pair read
from `ABUF`. Cost: entry 16, 127 × (214 + 219 + 28), the last pair 214 + 219,
exit 46: `59042 = Gas.pass3f4b`.
-/

namespace MlDsaOptGlam44.Proofs.AltP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

/-- Value stored at `p + 0x7900` by a word block reading `M` at `p + o` (`p` in `CW`). -/
def fbv (M : ByteArray) (p : Nat) : Nat :=
  let z := word M (p + 0x5000)
  (word M p * lane z 0 + word M (p + 0x9900) * lane z 1 +
    (word M (p + 0xd700) &&& (2 ^ 192 - 1)) * lane z 2 +
    (word M (p + 0xf700) &&& (2 ^ 192 - 1)) * lane z 3 +
    ((word M (p + 0x2000) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
      (M64 * 2 ^ 192))) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `glam44_rreach`) is `fbv`'s. -/
theorem fb_arith {z c h s1 s2 a : Nat} (hz : z < 2 ^ 256) :
    ((M64 * 2 ^ 192 &&& ((2 ^ 256 - 2 ^ 128) &&& a) * (z / 2 ^ 128)) +
      (((2 ^ 192 - 1) &&& s2) * (z / 2 ^ 192) +
        (((2 ^ 192 - 1) &&& s1) * (M64 &&& z / 2 ^ 128) +
          (h * (M64 &&& z / 2 ^ 64) + c * (M64 &&& z))))) % 2 ^ 256 =
    (c * lane z 0 + h * lane z 1 + (s1 &&& (2 ^ 192 - 1)) * lane z 2 +
      (s2 &&& (2 ^ 192 - 1)) * lane z 3 +
      ((a &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192))) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have h3 : z / 2 ^ 192 % 2 ^ 64 = z / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  rw [GroupP.and_mod_of_lt (by unfold M64; norm_num), hM, hM, hM]
  simp only [lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, h3]
  rw [Nat.and_comm (M64 * 2 ^ 192), Nat.and_comm (2 ^ 256 - 2 ^ 128), Nat.and_comm (2 ^ 192 - 1) s1,
    Nat.and_comm (2 ^ 192 - 1) s2]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev fbK (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd (M64 * 2 ^ 192) :: wd (2 ^ 256 - 2 ^ 128) :: wd (2 ^ 192 - 1) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fb_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 17401 (wd p :: fbK ret tail) M)
      (callState s 17486 (wd p :: fbK ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (fbv M p) 32) (p + 0x7900))) 214 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam44_rreach [6949, 6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006, 7007, 7008, 7009, 7010, 7011, 7012, 7013, 7014, 7015, 7016, 7017] with [fbv, M64]
  rw [show 30976 + p = p + 30976 by omega, show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega, show 63232 + p = p + 63232 by omega,
    show 55040 + p = p + 55040 by omega, show 39168 + p = p + 39168 by omega]
  congr 2
  exact fb_arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fb_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 17486 (wd p :: fbK ret tail) M)
      (callState s 17573 (wd p :: fbK ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (fbv M (p + 32)) 32) (p + 32 + 0x7900))) 219 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam44_rreach [7018, 7019, 7020, 7021, 7022, 7023, 7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038, 7039, 7040, 7041, 7042, 7043, 7044, 7045, 7046, 7047, 7048, 7049, 7050, 7051, 7052, 7053, 7054, 7055, 7056, 7057, 7058, 7059, 7060, 7061, 7062, 7063, 7064, 7065, 7066, 7067, 7068, 7069, 7070, 7071, 7072, 7073, 7074, 7075, 7076, 7077, 7078, 7079, 7080, 7081, 7082, 7083, 7084, 7085, 7086, 7087] with [fbv, M64]
  rw [show 31008 + p = p + 32 + 30976 by omega, show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega, show 63264 + p = p + 32 + 63232 by omega,
    show 55072 + p = p + 32 + 55040 by omega, show 39200 + p = p + 32 + 39168 by omega,
    show 32 + p = p + 32 by omega]
  congr 2
  exact fb_arith (word_lt M _)

theorem fb_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 17573 (wd p :: fbK ret tail) M)
      (callState s 17401 (wd (p + 64) :: fbK ret tail) M) 28 := by
  glam44_rreach [7088, 7089, 7090, 7091, 7092, 7093, 7094]
  simp only [Nat.add_comm, and_self]

theorem fb_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4b ret tail) (M : ByteArray) :
    Reach (callState s 17573 (wd 0x4fc0 :: fbK ret tail) M) (callState s ret tail M) 46 := by
  have := hr.depth; simp only [Stack.pass3f4b, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [7088, 7089, 7090, 7091, 7092, 7093, 7094, 7095, 7096, 7097, 7098, 7099, 7100] with [hj]

theorem fb_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4b ret tail) (M : ByteArray) :
    Reach (callState s 17297 (wd ret :: tail) M) (callState s 17401 (wd 0x3000 :: fbK ret tail) M) 16 := by
  have := hr.depth; simp only [Stack.pass3f4b, Stack.leaf] at this
  glam44_rreach [6943, 6944, 6945, 6946, 6947, 6948] with [M64]

/-- `ACC[t]`'s value as a function of `t`. -/
def fbf (m : ByteArray) (t : Nat) : Nat := fbv m (CW + 32 * t)

/-- `fbv` of a memory that differs from `m` only in `ACC[0, n)`. -/
theorem fbv_store (m : ByteArray) {n t : Nat} (hn : n ≤ 256) (ht : t < 256) :
    fbv (storeWords m ACC (fbf m) n) (CW + 32 * t) = fbf m t := by
  unfold fbf fbv
  simp only [CW, ACC] at *
  rw [WP4.word_storeWords_out (a := 12288 + 32 * t) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 20480) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0x9900) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0xd700) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0xf700) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0x2000) (by omega)]

theorem fb_next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m ACC (fbf m) n)
        (Data.Bytes.natToBytesPadded (fbv (storeWords m ACC (fbf m) n) p) 32) (p + 0x7900) =
      storeWords m ACC (fbf m) (n + 1) := by
  rw [storeWords_succ, hp, fbv_store m (by omega) hn]
  congr 1
  unfold CW ACC; omega

theorem fb_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 17401 (wd (CW + 64 * j) :: fbK ret tail) (storeWords m ACC (fbf m) (2 * j)))
      (callState s 17573 (wd (CW + 64 * j) :: fbK ret tail) (storeWords m ACC (fbf m) (2 * j + 2))) 433 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have w0 := fb_w0 hs htail (ret := ret) (storeWords m ACC (fbf m) (2 * j)) hp
  rw [fb_next m (by omega) (by omega)] at w0
  have w1 := fb_w1 hs htail (ret := ret) (storeWords m ACC (fbf m) (2 * j + 1)) hp
  rw [fb_next m (by omega) (by omega)] at w1
  exact w0.trans w1

theorem pass3f4b_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4b ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f4b (wd ret :: tail) m)
      (callState s ret tail (storeWords m ACC (fbf m) 256)) Gas.pass3f4b := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f4b, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 17401 (wd (CW + 64 * j) :: fbK ret tail) (storeWords m ACC (fbf m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 461 := by
    intro j hj
    have h := (fb_iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (fb_tail hs htail (storeWords m ACC (fbf m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m ACC (fbf m) 256)) 479 :=
    (fb_iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (fb_exit hs hr (storeWords m ACC (fbf m) 256))
  have hentry : Reach (callState s Entry.pass3f4b (wd ret :: tail) m) (I 0) 16 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW]
    exact fb_entry hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f4b; omega)

end MlDsaOptGlam44.Proofs.AltP

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f4b** with the post stated as the body of `altWord` (`Fn/Alt.lean`). -/
theorem pass3f4b_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4b ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        let z := word m (ZH + 32 * t)
        (word m (CW + 32 * t) * lane z 0 + word m (HP + 32 * t) * lane z 1 +
          (word m (SB + 32 * t) &&& (2 ^ 192 - 1)) * lane z 2 +
          (word m (SB + 8192 + 32 * t) &&& (2 ^ 192 - 1)) * lane z 3 +
          ((word m (ABUF + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
            (M64 * 2 ^ 192))) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f4b [] ret tail m [] m' Gas.pass3f4b := by
  have hv : ∀ t, AltP.fbf m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m ACC (AltP.fbf m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold AltP.fbf AltP.fbv
    simp only [CW, ZH, HP, SB, ABUF]
    rw [show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 0x9900 = 51456 + 32 * t by omega,
      show 12288 + 32 * t + 0xd700 = 67328 + 32 * t by omega,
      show 12288 + 32 * t + 0xf700 = 67328 + 8192 + 32 * t by omega,
      show 12288 + 32 * t + 0x2000 = 20480 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m ACC (AltP.fbf m) 256
  · exact AltP.pass3f4b_reach hs hr m

end MlDsaOptGlam44.Proofs
