import MlDsaOpt87.Fn.Group.Defs
import MlDsaOptGlam87.Budget
import MlDsaOptGlam87.Layout
/- Ported from `MlDsaOpt87/Fn/Pass3f/P4.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f4` (ML-DSA-87): row group 0, columns 0 … 4 (stores)

128 iterations at `p = CW + 64 j`, two words each:
`ACC[t] := Σ_c buf_c[t] · ẑ_c[t]`, reads of the original memory (`ACC` is
disjoint from every region read). Template: `MlDsaOpt44/Fn/Group/Pass3f4.lean`.
`pass3f4_call_aux` states the post as the body of `p3f4Word` (`Fn/Group.lean`)
with `bz` unfolded.
-/

namespace MlDsaOptGlam87.Proofs.Pass3fP4

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

/-- Value stored at `p + 0x9900` by a word block (`p` in `CW`). -/
def v (M : ByteArray) (p : Nat) : Nat :=
  let z := word M (p + 0x5000)
  (word M p * lane z 0 + word M (p + 0xd900) * lane z 1 + word M (p + 0xf900) * lane z 2 +
    word M (p + 0xb900) * lane z 3 + word M (p + 0x2000) * lane (word M (p + 0x7000)) 0) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `opt_reach`) is `v`'s. -/
theorem arith {z y a b c d e : Nat} (hz : z < 2 ^ 256) :
    (e * (M64 &&& y) + (d * (z / 2 ^ 192) + (c * (M64 &&& z / 2 ^ 128) +
      (b * (M64 &&& z / 2 ^ 64) + a * (M64 &&& z))))) % 2 ^ 256 =
    (a * lane z 0 + b * lane z 1 + c * lane z 2 + d * lane z 3 + e * lane y 0) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have h3 : z / 2 ^ 192 % 2 ^ 64 = z / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  simp only [hM, lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, h3]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev K (ret : Nat) (tail : List UInt256) : List UInt256 := wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 17403 (wd p :: K ret tail) M)
      (callState s 17484 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0x9900))) 199 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [7121, 7122, 7123, 7124, 7125, 7126, 7127, 7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139, 7140, 7141, 7142, 7143, 7144, 7145, 7146, 7147, 7148, 7149, 7150, 7151, 7152, 7153, 7154, 7155, 7156, 7157, 7158, 7159, 7160, 7161, 7162, 7163, 7164, 7165, 7166, 7167, 7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7181, 7182, 7183, 7184] with [v, M64]
  rw [show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega,
    show 28672 + p = p + 28672 by omega,
    show 39168 + p = p + 39168 by omega,
    show 47360 + p = p + 47360 by omega,
    show 55552 + p = p + 55552 by omega,
    show 63744 + p = p + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 17484 (wd p :: K ret tail) M)
      (callState s 17567 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0x9900))) 204 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [7185, 7186, 7187, 7188, 7189, 7190, 7191, 7192, 7193, 7194, 7195, 7196, 7197, 7198, 7199, 7200, 7201, 7202, 7203, 7204, 7205, 7206, 7207, 7208, 7209, 7210, 7211, 7212, 7213, 7214, 7215, 7216, 7217, 7218, 7219, 7220, 7221, 7222, 7223, 7224, 7225, 7226, 7227, 7228, 7229, 7230, 7231, 7232, 7233, 7234, 7235, 7236, 7237, 7238, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7247, 7248, 7249] with [v, M64]
  rw [show 32 + p = p + 32 by omega,
    show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega,
    show 28704 + p = p + 32 + 28672 by omega,
    show 39200 + p = p + 32 + 39168 by omega,
    show 47392 + p = p + 32 + 47360 by omega,
    show 55584 + p = p + 32 + 55552 by omega,
    show 63776 + p = p + 32 + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

theorem tl {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 17567 (wd p :: K ret tail) M)
      (callState s 17403 (wd (p + 64) :: K ret tail) M) 28 := by
  glam87_rreach [7250, 7251, 7252, 7253, 7254, 7255, 7256]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 17567 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 40 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  glam87_rreach [7250, 7251, 7252, 7253, 7254, 7255, 7256, 7257, 7258, 7259] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 17390 (wd ret :: tail) M) (callState s 17403 (wd 0x3000 :: K ret tail) M) 7 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  glam87_rreach [7118, 7119, 7120] with [M64]

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
    word_storeWords_out (a := 12288 + 32 * t + 20480) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 28672) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 47360) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 55552) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 63744) (by omega)]

theorem next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m ACC (f m) n)
        (Data.Bytes.natToBytesPadded (v (storeWords m ACC (f m) n) p) 32) (p + 0x9900) =
      storeWords m ACC (f m) (n + 1) := by
  rw [storeWords_succ, hp, v_store m (Nat.le_refl n) hn]
  congr 1
  unfold CW ACC; omega

theorem iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 17403 (wd (CW + 64 * j) :: K ret tail) (storeWords m ACC (f m) (2 * j)))
      (callState s 17567 (wd (CW + 64 * j) :: K ret tail) (storeWords m ACC (f m) (2 * j + 2))) 403 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have h0 := w0 hs htail (ret := ret) (storeWords m ACC (f m) (2 * j)) hp
  rw [next m (by omega) (by omega)] at h0
  have h1 := w1 hs htail (ret := ret) (storeWords m ACC (f m) (2 * j + 1)) hp
  rw [next m (by omega) (by omega)] at h1
  exact h0.trans h1

theorem reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f4 (wd ret :: tail) m)
      (callState s ret tail (storeWords m ACC (f m) 256)) Gas.pass3f4 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 17403 (wd (CW + 64 * j) :: K ret tail) (storeWords m ACC (f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 431 := by
    intro j hj
    have h := (iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (tl hs htail (storeWords m ACC (f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m ACC (f m) 256)) 443 :=
    (iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (ex hs hr (storeWords m ACC (f m) 256))
  have hentry : Reach (callState s Entry.pass3f4 (wd ret :: tail) m) (I 0) 7 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW, Entry.pass3f4]
    exact en hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f4; omega)

end MlDsaOptGlam87.Proofs.Pass3fP4

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f4** with the post stated as the body of `p3f4Word` (`Fn/Group.lean`). -/
theorem pass3f4_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
      (word m (CW + 32 * t) * zl m 0 t + word m (HP + 32 * t) * zl m 1 t +
        word m (HP + 8192 + 32 * t) * zl m 2 t + word m (ACC + 8192 + 32 * t) * zl m 3 t +
        word m (ABUF + 32 * t) * zl m 4 t) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f4 [] ret tail m [] m' Gas.pass3f4 := by
  have hv : ∀ t, Pass3fP4.f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m ACC (Pass3fP4.f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold Pass3fP4.f Pass3fP4.v
    simp only [zl, CW, ZH, HP, ACC, ABUF, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.add_zero, Nat.zero_add]
    rw [show 12288 + 32 * t + 8192 = 20480 + 32 * t by omega,
      show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 28672 = 40960 + 32 * t by omega,
      show 12288 + 32 * t + 47360 = 59648 + 32 * t by omega,
      show 12288 + 32 * t + 55552 = 67840 + 32 * t by omega,
      show 12288 + 32 * t + 63744 = 76032 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m ACC (Pass3fP4.f m) 256
  · exact Pass3fP4.reach hs hr m

end MlDsaOptGlam87.Proofs
