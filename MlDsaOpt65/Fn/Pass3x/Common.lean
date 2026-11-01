import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
import MlDsaOpt65.Fn.Group.Common
set_option warningAsError true
/-!
# Helpers for the `pass3x5 … pass3x8` loops

Lane-mask algebra closing the word equations that `opt65_reach` leaves after a
loop body (masks `2^a (2^k − 1)`, then shifts by multiples of 64), and the
shared loop skeleton `p3x_loop`: 256 iterations `o = 0, 32, …, 8160`, each
storing one word at `B + o`, so the memory after `j` iterations is
`storeWords m B (fun t => v m (32 t)) j`.
-/

namespace MlDsaOpt65.Proofs.Pass3xP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.GroupP (land_m64' storeWords_next)

/-- `AND` with a contiguous mask `2^a (2^k − 1)` keeps bits `[a, a + k)` in place. -/
theorem land_mask (x a k : Nat) : 2 ^ a * (2 ^ k - 1) &&& x = 2 ^ a * (x / 2 ^ a % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : a ≤ j
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
  · simp [h]

/-- The masked field `[a, a + k)` moved down by `a`, as SHR leaves it. -/
theorem land_mask_shr (x a k : Nat) (h : a + k ≤ 256) :
    (2 ^ a * (2 ^ k - 1) &&& x) % 2 ^ 256 / 2 ^ a = x / 2 ^ a % 2 ^ k := by
  rw [land_mask, Nat.mod_eq_of_lt, Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  calc 2 ^ a * (x / 2 ^ a % 2 ^ k) < 2 ^ a * 2 ^ k :=
        Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.two_pow_pos a)
    _ = 2 ^ (a + k) := (Nat.pow_add 2 a k).symm
    _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) h

/-- `x >> 192` of a word is its lane 3. -/
theorem lane3_of_lt {x : Nat} (hx : x < 2 ^ 256) : x / 2 ^ 192 = lane x 3 := by
  unfold lane
  rw [Nat.mod_eq_of_lt (by omega)]

/-! The word equations `opt65_reach` leaves for the four loop bodies
(`A = ACC₁[t]`, `X = ABUF[t]`, `Z = ZH[t]`, `Z' = ZH₂[t]`), in its literal form. -/

theorem alg5 (A X Z : Nat) :
    (18446744073709551615 &&& Z / 18446744073709551616) *
        ((6277101735386680763495507056286727952638980837032266301440 &&& X) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936 /
          340282366920938463463374607431768211456) +
      (A + (18446744073709551615 &&& Z) * (340282366920938463463374607431768211455 &&& X)) =
    A + X % 340282366920938463463374607431768211456 * lane Z 0 + lane X 2 * lane Z 1 := by
  rw [show (6277101735386680763495507056286727952638980837032266301440 : Nat) =
      2 ^ 128 * (2 ^ 64 - 1) by norm_num,
    show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 by norm_num,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 by norm_num,
    land_mask_shr X 128 64 (by norm_num),
    show (340282366920938463463374607431768211455 : Nat) = 2 ^ 128 - 1 by norm_num,
    Nat.and_comm (2 ^ 128 - 1), Nat.and_two_pow_sub_one_eq_mod, land_m64', land_m64']
  simp only [lane]
  norm_num
  ring

theorem alg6 (A X Z : Nat) :
    (18446744073709551615 &&& Z / 340282366920938463463374607431768211456) *
        ((6277101735386680763835789423207666416083908700390324961280 &&& X) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936 /
          18446744073709551616) +
      (A + (18446744073709551615 &&& Z / 18446744073709551616) *
          ((18446744073709551615 &&& X) * 18446744073709551616)) =
    A + lane X 0 * 18446744073709551616 * lane Z 1 +
      X / 18446744073709551616 % 340282366920938463463374607431768211456 * lane Z 2 := by
  rw [show (6277101735386680763835789423207666416083908700390324961280 : Nat) =
      2 ^ 64 * (2 ^ 128 - 1) by norm_num,
    show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 by norm_num,
    show (18446744073709551616 : Nat) = 2 ^ 64 by norm_num,
    land_mask_shr X 64 128 (by norm_num),
    show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num,
    Nat.and_comm (2 ^ 64 - 1), Nat.and_comm (2 ^ 64 - 1), Nat.and_comm (2 ^ 64 - 1),
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [lane]
  norm_num
  ring

theorem alg7 (A X Z Z' : Nat) (hZ : Z < 2 ^ 256) :
    (18446744073709551615 &&& Z') *
        ((6277101735386680763495507056286727952638980837032266301440 &&& X) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936 /
          340282366920938463463374607431768211456) +
      (A + Z / 6277101735386680763835789423207666416102355444464034512896 *
          (340282366920938463463374607431768211455 &&& X)) =
    A + X % 340282366920938463463374607431768211456 * lane Z 3 + lane X 2 * lane Z' 0 := by
  rw [show (6277101735386680763495507056286727952638980837032266301440 : Nat) =
      2 ^ 128 * (2 ^ 64 - 1) by norm_num,
    show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 by norm_num,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 by norm_num,
    show (6277101735386680763835789423207666416102355444464034512896 : Nat) = 2 ^ 192 by norm_num,
    land_mask_shr X 128 64 (by norm_num), lane3_of_lt hZ,
    show (340282366920938463463374607431768211455 : Nat) = 2 ^ 128 - 1 by norm_num,
    Nat.and_comm (2 ^ 128 - 1), Nat.and_two_pow_sub_one_eq_mod, land_m64']
  simp only [lane]
  norm_num
  ring

theorem alg8 (A X Z' : Nat) :
    (18446744073709551615 &&& Z') * ((18446744073709551615 &&& X) * 18446744073709551616) + A =
    A + lane X 0 * 18446744073709551616 * lane Z' 0 := by
  rw [land_m64', land_m64']
  simp only [lane]
  norm_num
  ring

/-- The `pass3x` loop: body lemmas for `o + 32 < 8192` (back edge taken) and
`o = 8160` (exit, through the `POP`), and the fact that iteration `j` reads
nothing the earlier iterations wrote. -/
theorem p3x_loop {s : State} {pc pcJ c ret B : Nat} {tail : List UInt256} (m : ByteArray)
    (v : ByteArray → Nat → Nat)
    (hread : ∀ j, j < 256 → v (storeWords m B (fun t => v m (32 * t)) j) (32 * j) = v m (32 * j))
    (hbody : ∀ M o, o + 32 < 8192 →
      Reach (callState s pc (wd o :: wd ret :: tail) M)
        (callState s pc (wd (o + 32) :: wd ret :: tail)
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M o) 32) (B + o))) c)
    (hexit : ∀ M,
      Reach (callState s pc (wd 8160 :: wd ret :: tail) M)
        (callState s pcJ (wd ret :: tail)
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M 8160) 32) (B + 8160))) (c + 2)) :
    Reach (callState s pc (wd 0 :: wd ret :: tail) m)
      (callState s pcJ (wd ret :: tail) (storeWords m B (fun t => v m (32 * t)) 256)) (256 * c + 2) := by
  have e : ∀ j, MachineState.writeBytes (storeWords m B (fun t => v m (32 * t)) j)
      (Data.Bytes.natToBytesPadded (v m (32 * j)) 32) (B + 32 * j) =
      storeWords m B (fun t => v m (32 * t)) (j + 1) := fun j => storeWords_next rfl rfl rfl
  have hstep : ∀ j, j < 255 →
      Reach (callState s pc (wd (32 * j) :: wd ret :: tail) (storeWords m B (fun t => v m (32 * t)) j))
        (callState s pc (wd (32 * (j + 1)) :: wd ret :: tail)
          (storeWords m B (fun t => v m (32 * t)) (j + 1))) c := by
    intro j hj
    have h := hbody (storeWords m B (fun t => v m (32 * t)) j) (32 * j) (by omega)
    rw [hread j (by omega), e j, show 32 * j + 32 = 32 * (j + 1) by ring] at h
    exact h
  have hl := Reach.loop (I := fun j => callState s pc (wd (32 * j) :: wd ret :: tail)
    (storeWords m B (fun t => v m (32 * t)) j)) 255 hstep
  have he := hexit (storeWords m B (fun t => v m (32 * t)) 255)
  rw [show (8160 : Nat) = 32 * 255 by norm_num, hread 255 (by norm_num), e 255] at he
  have h := hl.trans he
  rw [show 255 * c + (c + 2) = 256 * c + 2 by ring] at h
  exact h

end MlDsaOpt65.Proofs.Pass3xP
