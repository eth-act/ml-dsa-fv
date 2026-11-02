import MlDsaOpt87.Fn.Group.Defs
import MlDsaOptGlam87.Budget
import MlDsaOptGlam87.Layout
/- Ported from `MlDsaOpt87/Fn/Pass3f/P14.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f14` (ML-DSA-87): row group 1, columns 4 … 6 rows 4 … 6, row 7 columns 3 … 6 (adds)

128 iterations at `p = CW + 64 j`, two words each: `ACC[2048 + t] += …`;
word `t` of `ACC + 0x2000` is read before it is written, so the post is about
the original memory. `pass3f14_call_aux` states the post as the body of
`p3f14Word` with `bzl`, `kron14` unfolded.
-/

namespace MlDsaOptGlam87.Proofs.Pass3fP14

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

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
    Reach (callState s 17963 (wd p :: K ret tail) M)
      (callState s 18052 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0xb900))) 218 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7482, 7483, 7484, 7485, 7486, 7487, 7488, 7489, 7490, 7491, 7492, 7493, 7494, 7495, 7496, 7497, 7498, 7499, 7500, 7501, 7502, 7503, 7504, 7505, 7506, 7507, 7508, 7509, 7510, 7511, 7512, 7513, 7514, 7515, 7516, 7517, 7518, 7519, 7520, 7521, 7522, 7523, 7524, 7525, 7526, 7527, 7528, 7529, 7530, 7531, 7532, 7533, 7534, 7535, 7536, 7537, 7538, 7539, 7540, 7541, 7542, 7543] with [v, M64]
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
    Reach (callState s 18052 (wd p :: K ret tail) M)
      (callState s 18143 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0xb900))) 223 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [7544, 7545, 7546, 7547, 7548, 7549, 7550, 7551, 7552, 7553, 7554, 7555, 7556, 7557, 7558, 7559, 7560, 7561, 7562, 7563, 7564, 7565, 7566, 7567, 7568, 7569, 7570, 7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7603, 7604, 7605, 7606, 7607, 7608, 7609, 7610, 7611, 7612, 7613, 7614, 7615] with [v, M64]
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
    Reach (callState s 18143 (wd p :: K ret tail) M)
      (callState s 17963 (wd (p + 64) :: K ret tail) M) 28 := by
  glam87_rreach [7616, 7617, 7618, 7619, 7620, 7621, 7622]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 18143 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  glam87_rreach [7616, 7617, 7618, 7619, 7620, 7621, 7622, 7623, 7624, 7625, 7626, 7627] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 17892 (wd ret :: tail) M) (callState s 17963 (wd 0x3000 :: K ret tail) M) 13 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  glam87_rreach [7468, 7469, 7470, 7471, 7472] with [M64]

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
    Reach (callState s 17963 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j)))
      (callState s 18143 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j + 2))) 441 := by
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
    callState s 17963 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j))
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

end MlDsaOptGlam87.Proofs.Pass3fP14

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

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

end MlDsaOptGlam87.Proofs
