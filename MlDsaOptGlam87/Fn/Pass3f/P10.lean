import MlDsaOpt87.Fn.Group.Defs
import MlDsaOptGlam87.Budget
import MlDsaOptGlam87.Layout
/- Ported from `MlDsaOpt87/Fn/Pass3f/P10.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f10` (ML-DSA-87): row group 1, columns 0 … 2 and column 3 rows 4 … 6 (stores)

128 iterations at `p = CW + 64 j`, two words each; `ACC + 0x2000` is disjoint
from every region read. `pass3f10_call_aux` states the post as the body of
`p3f10Word` with `bz`, `bzl` unfolded.
-/

namespace MlDsaOptGlam87.Proofs.Pass3fP10

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

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
    Reach (callState s 17742 (wd p :: K ret tail) M)
      (callState s 17808 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0xb900))) 164 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [7350, 7351, 7352, 7353, 7354, 7355, 7356, 7357, 7358, 7359, 7360, 7361, 7362, 7363, 7364, 7365, 7366, 7367, 7368, 7369, 7370, 7371, 7372, 7373, 7374, 7375, 7376, 7377, 7378, 7379, 7380, 7381, 7382, 7383, 7384, 7385, 7386, 7387, 7388, 7389, 7390, 7391, 7392, 7393, 7394, 7395, 7396, 7397, 7398, 7399, 7400, 7401, 7402] with [v, M64]
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
    Reach (callState s 17808 (wd p :: K ret tail) M)
      (callState s 17876 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0xb900))) 169 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [7403, 7404, 7405, 7406, 7407, 7408, 7409, 7410, 7411, 7412, 7413, 7414, 7415, 7416, 7417, 7418, 7419, 7420, 7421, 7422, 7423, 7424, 7425, 7426, 7427, 7428, 7429, 7430, 7431, 7432, 7433, 7434, 7435, 7436, 7437, 7438, 7439, 7440, 7441, 7442, 7443, 7444, 7445, 7446, 7447, 7448, 7449, 7450, 7451, 7452, 7453, 7454, 7455, 7456] with [v, M64]
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
    Reach (callState s 17876 (wd p :: K ret tail) M)
      (callState s 17742 (wd (p + 64) :: K ret tail) M) 28 := by
  glam87_rreach [7457, 7458, 7459, 7460, 7461, 7462, 7463]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 17876 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 42 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  glam87_rreach [7457, 7458, 7459, 7460, 7461, 7462, 7463, 7464, 7465, 7466, 7467] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 17704 (wd ret :: tail) M) (callState s 17742 (wd 0x3000 :: K ret tail) M) 10 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  glam87_rreach [7346, 7347, 7348, 7349] with [M64]

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
    Reach (callState s 17742 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j)))
      (callState s 17876 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j + 2))) 333 := by
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
    callState s 17742 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j))
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

end MlDsaOptGlam87.Proofs.Pass3fP10

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

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

end MlDsaOptGlam87.Proofs
