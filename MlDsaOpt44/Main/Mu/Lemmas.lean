import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Bswap
import MlDsaOpt44.Math.SpongeBits
import MlDsaOpt44.Math.SpongeBytes
set_option warningAsError true
/-!
# Pure lemmas for the `kf1` hashes of `seg_mu` and `seg_fin`

* memory: `word_wr` (read after one `MSTORE`, any address);
* replicated lanes: `rep_xor`, `not_rep`, `rep_cpl_xor`, `not_rep_cpl`, `lane_rep`;
* SHAKE256 padding: `le64_pad_full`, `le64_pad_last` (the last block is the raw
  message lanes xor `padLane`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-! ## Memory -/

theorem word_wr (m : ByteArray) {v a b : Nat} (hv : v < 2 ^ 256)
    (h : a = b ∨ a + 32 ≤ b ∨ b + 32 ≤ a) :
    word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) b) a =
      if a = b then v else word m a := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl, word_mstore _ _ _ hv]
  · rw [if_neg hab, word_mstore_disjoint _ _ (by omega)]

theorem word_wrL (m : ByteArray) {v a b : Nat} (hv : v < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (h : a = b ∨ a + 32 ≤ b ∨ b + 32 ≤ a) :
    word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) b) a =
      if a = b then v else word m a := word_wr m (by norm_num; exact hv) h

/-- One more `MSTORE` inside the frame range. -/
theorem frame_wr {m m' : ByteArray} {lo hi v b : Nat} (hb1 : lo ≤ b) (hb2 : b + 32 ≤ hi)
    (h : FrameExcept m m' [(lo, hi)]) :
    FrameExcept m (MachineState.writeBytes m' (Data.Bytes.natToBytesPadded v 32) b) [(lo, hi)] := by
  apply (h.trans (FrameExcept.mstore m' b v)).mono
  intro r hr
  refine ⟨(lo, hi), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

/-! ## Replicated lanes -/

theorem testBit_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {j : Nat} (hj : j < 256) :
    (pack4 v).testBit j = (v (j / 64)).testBit (j % 64) := by
  rw [← pack4_div_mod h (k := j / 64) (by omega), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [Nat.mod_lt j (by omega : 64 > 0), decide_true, Bool.true_and]
  congr 1; omega

theorem rep_eq_pack4 (v : Nat) : rep v = pack4 fun _ => v := by
  unfold rep REP pack4; ring

theorem rep_lt {v : Nat} (hv : v < 2 ^ 64) : rep v < 2 ^ 256 := by
  rw [rep_eq_pack4]; exact pack4_lt' fun _ _ => hv

theorem lane_rep {v : Nat} (hv : v < 2 ^ 64) {k : Nat} (hk : k < 4) :
    rep v / 2 ^ (64 * k) % 2 ^ 64 = v := by
  rw [rep_eq_pack4]; exact pack4_div_mod (fun _ _ => hv) hk

theorem rep_xor {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : rep a ^^^ rep b = rep (a ^^^ b) := by
  have hab : a ^^^ b < 2 ^ 64 := Nat.xor_lt_two_pow ha hb
  apply eq_of_testBit_lt (Nat.xor_lt_two_pow (rep_lt ha) (rep_lt hb)) (rep_lt hab)
  intro j hj
  rw [Nat.testBit_xor, rep_eq_pack4, rep_eq_pack4, rep_eq_pack4,
    testBit_pack4 (fun _ _ => ha) hj, testBit_pack4 (fun _ _ => hb) hj,
    testBit_pack4 (fun _ _ => hab) hj, Nat.testBit_xor]

theorem not_rep {v : Nat} (hv : v < 2 ^ 64) : 2 ^ 256 - 1 - rep v = rep (2 ^ 64 - 1 - v) := by
  unfold rep REP pack4; norm_num; omega

theorem rep_cpl_xor (x : Nat) {v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) :
    rep (cpl x v) ^^^ rep w = rep (cpl x (v ^^^ w)) := by
  rw [rep_xor (cpl_lt hv) hw, cpl_eq hv, cpl_eq (Nat.xor_lt_two_pow hv hw)]
  split
  · rw [Nat.xor_assoc, Nat.xor_comm M64 w, ← Nat.xor_assoc]
  · rfl

theorem not_rep_cpl {x v : Nat} (hx : x ∈ complemented) (hv : v < 2 ^ 64) :
    2 ^ 256 - 1 - rep (cpl x v) = rep v := by
  rw [not_rep (cpl_lt hv)]; unfold cpl; rw [if_pos hx]; congr 1; omega

theorem rep_cpl_lt (x : Nat) {v : Nat} (hv : v < 2 ^ 64) : rep (cpl x v) < 2 ^ 256 :=
  rep_lt (cpl_lt hv)

/-- `MUL` by the literal `REP` of a 64-bit value, as `opt44_block` leaves it. -/
theorem rep_lit {w : Nat} (hw : w < 2 ^ 64) :
    6277101735386680764176071790128604879584176795969512275969 * w %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = rep w := by
  have h := rep_lt hw
  rw [show rep w = 6277101735386680764176071790128604879584176795969512275969 * w by
    unfold rep REP pack4; norm_num; ring] at h ⊢
  exact Nat.mod_eq_of_lt h

theorem not_rep_lit {w : Nat} (hw : w < 2 ^ 64) :
    115792089237316195423570985008687907853269984665640564039457584007913129639935 -
      6277101735386680764176071790128604879584176795969512275969 * w %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      rep (2 ^ 64 - 1 - w) := by
  rw [rep_lit hw, ← not_rep hw]; norm_num

theorem rep_lit' (w : Nat) : 6277101735386680764176071790128604879584176795969512275969 * w = rep w := by
  unfold rep REP pack4; norm_num; ring

theorem not_rep_lit' {w : Nat} (hw : w < 2 ^ 64) :
    115792089237316195423570985008687907853269984665640564039457584007913129639935 -
      6277101735386680764176071790128604879584176795969512275969 * w = rep (2 ^ 64 - 1 - w) := by
  rw [rep_lit', ← not_rep hw]; norm_num

theorem word_lt_lit (m : ByteArray) (a : Nat) : word m a < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := word_lt m a

theorem xor_mod_lit {u v : Nat} (hu : u < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (hv : v < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    (u ^^^ v) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = u ^^^ v := by
  have h := Nat.xor_lt_two_pow (n := 256) (by norm_num; exact hu) (by norm_num; exact hv)
  norm_num at h
  exact Nat.mod_eq_of_lt h

theorem nxor_left_comm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem rep_zero : rep 0 = 0 := by unfold rep; simp

theorem rep_lt_lit {v : Nat} (hv : v < 2 ^ 64) : rep v < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := rep_lt hv

theorem lane_lt64 (x k : Nat) : lane x k < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem land_M64 (y : Nat) : 18446744073709551615 &&& y = y % 18446744073709551616 := by
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]

theorem mask48_lt (y : Nat) : 18446744073709486080 &&& y < 18446744073709551616 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

theorem mask48_lt64 (y : Nat) : 18446744073709486080 &&& y < 2 ^ 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

theorem div_mod64 {y c : Nat} (h : y / c < 18446744073709551616) :
    y / c % 18446744073709551616 = y / c := Nat.mod_eq_of_lt h

theorem xor_rep_mod {w v : Nat} (hw : w < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (hv : v < 18446744073709551616) :
    (w ^^^ rep v) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = w ^^^ rep v :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw (rep_lt hv))

/-- Normalise `(w ^^^ rep X) % 2^256` against `w ^^^ rep (lane Y k)`. -/
macro "xor_mod" : tactic => `(tactic| (
  simp only [land_M64, lane, Nat.reducePow, Nat.reduceMul, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  simp (disch := first | omega | exact mask48_lt _ | exact word_lt_lit _ _) only [div_mod64, xor_rep_mod]))

/-! ## Bytes of 64-bit values -/

theorem byteN_xor (a b i : Nat) : byteN (a ^^^ b) i = byteN a i ^^^ byteN b i := by
  unfold byteN
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (j < 8) <;> simp

theorem eq_of_byteN64 {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : ∀ p, p < 8 → byteN x p = byteN y p) : x = y :=
  eq_of_testBit_lt hx hy fun j hj => by
    rw [testBit_byteN x j, testBit_byteN y j, h (j / 8) (by omega)]

/-- The SHAKE padding bits of the last block as lanes: `0x1F` at byte `r`, `0x80`
at byte 135. -/
def padLane (r x : Nat) : Nat :=
  (if x = r / 8 then 31 * 2 ^ (8 * (r % 8)) else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)

theorem padLane_lt (r x : Nat) : padLane r x < 2 ^ 64 := by
  unfold padLane
  apply Nat.xor_lt_two_pow
  · split
    · have : r % 8 < 8 := Nat.mod_lt _ (by omega)
      interval_cases (r % 8) <;> norm_num
    · norm_num
  · split <;> norm_num

private theorem byteN_31 {q i : Nat} (hq : q < 8) (hi : i < 8) :
    byteN (31 * 2 ^ (8 * q)) i = if i = q then 31 else 0 := by
  unfold byteN
  interval_cases q <;> interval_cases i <;> norm_num

private theorem byteN_top {i : Nat} (hi : i < 8) : byteN (2 ^ 63) i = if i = 7 then 128 else 0 := by
  unfold byteN
  interval_cases i <;> norm_num

private theorem byteN_zero (i : Nat) : byteN 0 i = 0 := by unfold byteN; simp

theorem byteN_padLane (r x : Nat) {i : Nat} (hi : i < 8) :
    byteN (padLane r x) i =
      (if 8 * x + i = r then 31 else 0) ^^^ (if 8 * x + i = 135 then 128 else 0) := by
  unfold padLane
  rw [byteN_xor]
  congr 1
  · split
    · rw [byteN_31 (Nat.mod_lt _ (by omega)) hi]
      split <;> split <;> first | rfl | omega
    · rw [byteN_zero]; split
      · omega
      · rfl
  · split
    · rw [byteN_top hi]; split <;> split <;> first | rfl | omega
    · rw [byteN_zero]; split
      · omega
      · rfl

private theorem le64_byteN (b : ByteArray) (a : Nat) {i : Nat} (hi : i < 8) :
    byteN (le64 b a) i = byteAt b (a + i) := byteN_le64 b a hi

/-- Full blocks of the padded message are message bytes. -/
theorem le64_pad_full (msg : ByteArray) {a : Nat} (ha : a + 8 ≤ msg.size) :
    le64 (Fips202.pad 136 0x1F msg) a = le64 msg a :=
  le64_congr fun k hk => byteAt_pad_lt 136 msg (a + k) (by omega)

/-- The last block of the padded message: the raw message lanes (zero past the
end) xor the padding bits. -/
theorem le64_pad_last (msg : ByteArray) {x : Nat} (hx : x < 17) :
    le64 (Fips202.pad 136 0x1F msg) (msg.size / 136 * 136 + 8 * x) =
      le64 msg (msg.size / 136 * 136 + 8 * x) ^^^ padLane (msg.size % 136) x := by
  have hr := Nat.mod_lt msg.size (show 136 > 0 by omega)
  have hmd := Nat.mod_add_div msg.size 136
  apply eq_of_byteN64 (le64_lt _ _)
    (Nat.xor_lt_two_pow (le64_lt _ _) (padLane_lt _ _))
  intro i hi
  rw [le64_byteN _ _ hi, byteN_xor, le64_byteN _ _ hi, byteN_padLane _ _ hi, Nat.add_assoc,
    byteAt_pad_last 136 msg (by omega) (8 * x + i) (by omega)]
  split
  · rename_i h
    rw [if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero]
  · rename_i h
    have hz : byteAt msg (msg.size / 136 * 136 + (8 * x + i)) = 0 := by
      unfold byteAt; rw [dif_neg (by omega)]
    rw [hz, Nat.zero_xor]
    split <;> split <;> rfl

end MlDsaOpt44.Proofs
