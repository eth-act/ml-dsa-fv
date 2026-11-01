import MlDsaOpt44.Fn.Sponge.Fold
import MlDsaOpt44.Fn.Sponge.Defs
import MlDsaOpt44.Fn.Sponge.Mem
set_option warningAsError true
/-!
# Lane extraction from byte-swapped calldata words (`absorb17`, `trabs`)

The four lane extractions the code performs on a word `x` (in `opt44_block`
normal form) are `x / 2^(192 − 64 j) mod 2^64`; on `bswapNet (word cd a)`
they are `le64 cd (a + 8 j)`.
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

theorem ext0 {x : Nat} (hx : x < 2 ^ 256) :
    x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 /
      6277101735386680763835789423207666416102355444464034512896 = x / 2 ^ (192 - 64 * 0) % 2 ^ 64 := by
  norm_num; omega

theorem ext1 {x : Nat} (hx : x < 2 ^ 256) :
    (18446744073709551615 &&&
      x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 /
        340282366920938463463374607431768211456) = x / 2 ^ (192 - 64 * 1) % 2 ^ 64 := by
  rw [Nat.and_comm, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num; omega

theorem ext2 {x : Nat} (hx : x < 2 ^ 256) :
    (18446744073709551615 &&&
      x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 /
        18446744073709551616) = x / 2 ^ (192 - 64 * 2) % 2 ^ 64 := by
  rw [Nat.and_comm, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num; omega

theorem ext3 (x : Nat) :
    (18446744073709551615 &&& x) = x / 2 ^ (192 - 64 * 3) % 2 ^ 64 := by
  rw [Nat.and_comm, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num

theorem bsw_eq (cd : ByteArray) (a : Nat) : bsw cd a = bswapNet (word cd a) :=
  (bswapNet_word cd a).symm

theorem bsw_lane (cd : ByteArray) (a : Nat) {j : Nat} (hj : j < 4) :
    bswapNet (word cd a) / 2 ^ (192 - 64 * j) % 2 ^ 64 = le64 cd (a + 8 * j) := by
  have := lane_bswapNet cd a (k := 3 - j) (by omega)
  unfold lane at this
  rwa [show 64 * (3 - j) = 192 - 64 * j by omega, show 3 - (3 - j) = j by omega] at this

theorem REP_eq : REP = 6277101735386680764176071790128604879584176795969512275969 := by
  unfold REP pack4; norm_num

theorem rep_lt {v : Nat} (hv : v < 2 ^ 64) : rep v < 2 ^ 256 := by
  unfold rep; rw [REP_eq]; omega

theorem rep_val {w v : Nat} (hw : w < 2 ^ 256) (hv : v < 2 ^ 64) :
    (w ^^^ 6277101735386680764176071790128604879584176795969512275969 * v) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      w ^^^ rep v := by
  have h : 6277101735386680764176071790128604879584176795969512275969 * v = rep v := by
    unfold rep; rw [REP_eq, Nat.mul_comm]
  rw [h, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw (rep_lt hv))]

theorem le64_lt' (b : ByteArray) (a : Nat) : le64 b a < 2 ^ 64 := (le64_partial b a 8).1

/-- `absorb17`'s lane `j` of the group at `b`. -/
theorem absorb_lane {m M cd : ByteArray} {off x a b : Nat} (j : Nat) (hj : j < 4)
    (hw : word M a = word m (32 * x)) (hb : b + 8 * j = off + 8 * x)
    (L : Nat) (hL : L = bswapNet (word cd b) / 2 ^ (192 - 64 * j) % 2 ^ 64) :
    (word M a ^^^ 6277101735386680764176071790128604879584176795969512275969 * L) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      word m (32 * x) ^^^ rep (le64 cd (off + 8 * x)) := by
  rw [hw, hL, bsw_lane cd b hj, hb, rep_val (word_lt _ _) (le64_lt' _ _)]

/-- Lane `4 i + j` absorbed by `trabs`, as the code extracts it. -/
theorem trLane_eq (cd : ByteArray) (off lm n4 i : Nat) {j : Nat} (hj : j < 4) :
    trLane cd off lm n4 (4 * i + j) =
      (if i + 1 = n4 then lm &&& bswapNet (word cd (off + 32 * i))
        else bswapNet (word cd (off + 32 * i))) / 2 ^ (192 - 64 * j) % 2 ^ 64 := by
  unfold trLane
  rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega, bsw_eq]
  split <;> simp only [Nat.and_comm]

theorem trLane_lt (cd : ByteArray) (off lm n4 u : Nat) : trLane cd off lm n4 u < 2 ^ 64 := by
  unfold trLane; exact Nat.mod_lt _ (by norm_num)

theorem spread_lt253 (v : Nat) : spread v < 2 ^ 253 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_spread]
  by_cases h : i % 4 = 0
  · simp [h, show ¬ i / 4 < 64 by omega]
  · simp [h]

theorem spread_sh_lt {v sh : Nat} (hsh : sh < 4) : spread v * 2 ^ sh < 2 ^ 256 := by
  have h1 := spread_lt253 v
  have h2 : 2 ^ sh ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc spread v * 2 ^ sh < 2 ^ 253 * 2 ^ 3 :=
        Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
    _ = 2 ^ 256 := by norm_num

/-- `trabs`'s lane `j` of group `i`: `w = (lm &&&)? bswapNet …`. -/
theorem trabs_lane {m M cd : ByteArray} {off lm n4 sh kp i a : Nat} (j : Nat) (hj : j < 4)
    (hsh : sh < 4) (hw : word M a = word m (kp + 32 * (4 * i + j)))
    (L : Nat) (hL : L = (if i + 1 = n4 then lm &&& bswapNet (word cd (off + 32 * i))
        else bswapNet (word cd (off + 32 * i))) / 2 ^ (192 - 64 * j) % 2 ^ 64) :
    (sprNet L * 2 ^ sh ^^^ word M a) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      word m (kp + 32 * (4 * i + j)) ^^^ spread (trLane cd off lm n4 (4 * i + j)) * 2 ^ sh := by
  rw [← trLane_eq cd off lm n4 i hj] at hL
  rw [hL, sprNet_eq (trLane_lt _ _ _ _ _), hw, Nat.xor_comm,
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (word_lt _ _) (spread_sh_lt hsh))]

theorem wbc {M M' : ByteArray} {e v a a' : Nat} (hM : M = M') (he : e = v) (ha : a = a') :
    MachineState.writeBytes M (Data.Bytes.natToBytesPadded e 32) a =
      MachineState.writeBytes M' (Data.Bytes.natToBytesPadded v 32) a' := by
  subst hM he ha; rfl

end MlDsaOpt44.Proofs.WP4
