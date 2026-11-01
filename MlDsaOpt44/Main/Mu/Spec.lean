import MlDsaOpt44.Main.Mu.Lemmas
set_option warningAsError true
/-!
# The SHAKE256 input of μ and its lanes

`muMsg cd = tr ‖ 0 ‖ 0 ‖ M`; its bytes past `tr` are calldata bytes
(`le64_muMsg_hi`), except that the two zero bytes are the masked low bytes of
the calldata lane at `3730` (`le64_muMsg_64`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

def muMsg (cd : ByteArray) : ByteArray := trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)

def muPad (cd : ByteArray) : ByteArray := Fips202.pad 136 0x1F (muMsg cd)

theorem shake_size (msg : ByteArray) {n : Nat} (hn : n ≤ 136) : (Fips202.shake 136 msg n).size = n := by
  unfold Fips202.shake
  rw [ByteArray.size_extract, MlDsa44.Proofs.Math.squeeze_size_of_rate _ _ _ (Or.inl rfl)]
  have : (n + 136 - 1) / 136 * 136 ≥ n := by omega
  omega

theorem trOf_size (cd : ByteArray) : (trOf cd).size = 64 := shake_size _ (by norm_num)

theorem muMsg_size (cd : ByteArray) (hcd : HDR ≤ cd.size) :
    (muMsg cd).size = 66 + (cd.size - 3732) := by
  unfold muMsg msgOf
  rw [ByteArray.size_append, ByteArray.size_append, trOf_size, ByteArray.size_extract]
  change 64 + (2 + _) = _
  unfold HDR at hcd
  omega

theorem byteAt_pair0 (j : Nat) : byteAt (ByteArray.mk #[0, 0]) j = 0 := by
  unfold byteAt
  split
  · rename_i h
    change j < 2 at h
    interval_cases j <;> rfl
  · rfl

theorem byteAt_muMsg (cd : ByteArray) (k : Nat) :
    byteAt (muMsg cd) k =
      if k < 64 then byteAt (trOf cd) k else if k < 66 then 0 else byteAt cd (3666 + k) := by
  unfold muMsg
  rw [byteAt_append, trOf_size]
  split
  · rfl
  · rw [byteAt_append, show (ByteArray.mk #[(0 : UInt8), 0]).size = 2 from rfl]
    split
    · rw [if_pos (by omega)]; exact byteAt_pair0 _
    · rw [if_neg (by omega)]
      unfold msgOf
      rw [byteAt_extract _ _ _ _ le_rfl]
      split
      · congr 1; omega
      · unfold byteAt; rw [dif_neg (by omega)]

theorem le64_muMsg_lo (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (muMsg cd) (8 * x) = le64 (trOf cd) (8 * x) :=
  le64_congr fun k hk => by rw [byteAt_muMsg cd, if_pos (by omega)]

theorem le64_muMsg_hi (cd : ByteArray) {a : Nat} (ha : 66 ≤ a) :
    le64 (muMsg cd) a = le64 cd (3666 + a) :=
  le64_congr fun k hk => by
    rw [byteAt_muMsg cd, if_neg (by omega), if_neg (by omega), Nat.add_assoc]

theorem byteN_and (a b i : Nat) : byteN (a &&& b) i = byteN a i &&& byteN b i := by
  unfold byteN
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  cases decide (j < 8) <;> simp

theorem le64_muMsg_64 (cd : ByteArray) :
    le64 (muMsg cd) 64 = 18446744073709486080 &&& le64 cd 3730 := by
  apply eq_of_byteN64 (le64_lt _ _) (mask48_lt _)
  intro i hi
  rw [byteN_le64 _ _ hi, byteN_and, byteN_le64 _ _ hi, byteAt_muMsg cd, if_neg (by omega)]
  have hb := byteAt_lt cd (3730 + i)
  have hm : byteN 18446744073709486080 i = if i < 2 then 0 else 255 := by
    unfold byteN; interval_cases i <;> norm_num
  rw [hm]
  split
  · rw [if_pos (by omega), Nat.zero_and]
  · rw [if_neg (by omega), show 3666 + (64 + i) = 3730 + i by omega]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hb]

/-- `μ`'s lanes are the first lanes of the absorbed state. -/
theorem le64_muOf (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (muOf cd) (8 * x) = laneOf (Fips202.absorb 136 (muPad cd)) x := by
  have := le64_shake256 (muMsg cd) (n := 64) (j := 0) (x := x) (by omega) (by omega)
  simpa [muOf, muMsg, muPad, Fips204.H, Fips202.shake256] using this

end MlDsaOpt44.Proofs
