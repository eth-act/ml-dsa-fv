import MlDsaOpt44.Math.SpongeBits
set_option linter.unusedSectionVars false
/-!
# `blk`: bit-level facts (WP3)

* `swm c u x`: one delta swap of the de-interleave network, in the operand
  order the code computes it (`c = 2^d`), truncated to 256 bits;
  `testBit_swm` reads bit `p` of it from bit `src d u p` of `x`.
* `unz`: the six swaps; `testBit_unz`: bit `p` comes from bit
  `4 (p % 64) + p / 64`, so `unz (il v) = pack4 v` (`unz_il`).
* `c0 … c7`, `lfv`: the candidate words and the flag accumulator as the code
  computes them from the three de-interleaved words; `c_pack4` and `lfv_pack4`
  turn them into lane form.
-/

namespace MlDsaOpt44.Proofs.Blk

open MlDsaOptCommon
open MlDsa44

/-! ## Delta swaps -/

/-- One delta swap `x ^ t ^ (t << d)`, `t = ((x >> d) ^ x) & u`, `c = 2^d`. -/
def swm (c u x : Nat) : Nat := ((u &&& (x ^^^ x / c)) * c ^^^ u &&& (x ^^^ x / c) ^^^ x) % 2 ^ 256

/-- The source bit of output bit `p` of a delta swap. -/
def src (d u p : Nat) : Nat :=
  if u.testBit p then p + d else if d ≤ p ∧ u.testBit (p - d) then p - d else p

theorem swm_lt (c u x : Nat) : swm c u x < 2 ^ 256 := Nat.mod_lt _ (by positivity)

theorem testBit_swm (d u x p : Nat) (hu : ∀ q, u.testBit q = true → ¬ (d ≤ q ∧ u.testBit (q - d) = true)) :
    (swm (2 ^ d) u x).testBit p = (decide (p < 256) && x.testBit (src d u p)) := by
  unfold swm src
  rw [Nat.testBit_mod_two_pow]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases hp : p < 256
  · simp only [hp, decide_true, Bool.true_and]
    by_cases h1 : u.testBit p = true
    · have h2 := hu p h1
      by_cases hdp : d ≤ p
      · have h3 : u.testBit (p - d) = false := by simpa [hdp] using h2
        simp only [h1, hdp, h3, decide_true, Bool.true_and, Bool.false_and, Bool.and_false,
          Bool.false_xor, if_true]
        cases x.testBit p <;> cases x.testBit (p + d) <;> rfl
      · simp only [h1, hdp, decide_false, Bool.true_and, Bool.false_and, Bool.false_xor, if_true]
        cases x.testBit p <;> cases x.testBit (p + d) <;> rfl
    · have h1' : u.testBit p = false := by simpa using h1
      by_cases h4 : d ≤ p ∧ u.testBit (p - d) = true
      · obtain ⟨hdp, h5⟩ := h4
        have e : p - d + d = p := Nat.sub_add_cancel hdp
        simp only [h1', hdp, h5, e, decide_true, Bool.true_and, Bool.false_and, Bool.xor_false,
          and_self, if_true, Bool.false_eq_true, if_false]
        cases x.testBit p <;> cases x.testBit (p - d) <;> rfl
      · have h6 : (decide (d ≤ p) && u.testBit (p - d)) = false := by
          by_cases hdp : d ≤ p
          · simp only [hdp, decide_true, Bool.true_and]; simpa [hdp] using h4
          · simp [hdp]
        simp only [h1', Bool.false_and, Bool.xor_false, Bool.false_eq_true, if_false, h4]
        have : ((decide (d ≤ p) && (u.testBit (p - d) && (x.testBit (p - d) ^^ x.testBit (p - d + d))))) =
            false := by
          cases hdp : decide (d ≤ p) <;> cases hu' : u.testBit (p - d) <;> simp_all
        rw [this, Bool.false_xor]
  · simp [hp]

/-- A delta-swap mask never has both bit `q` and bit `q - d` set. -/
theorem disj_of_lt {u d : Nat} (hu : u < 2 ^ 256)
    (h : ∀ q, q < 256 → u.testBit q = true → ¬ (d ≤ q ∧ u.testBit (q - d) = true)) :
    ∀ q, u.testBit q = true → ¬ (d ≤ q ∧ u.testBit (q - d) = true) := by
  intro q hq
  by_cases hq' : q < 256
  · exact h q hq' hq
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega)))] at hq
    exact absurd hq (by simp)

/-! ## The six masks (`UNZIP` in `gen_opt.py`) -/

def U0 : Nat := 0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
def U1 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def U2 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def U3 : Nat := 0xcccccccccccccccccccccccccccccccc
def U4 : Nat := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def U5 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc

/-- The de-interleave network with masks `u0 … u5` (the code's order). -/
def unz (u0 u1 u2 u3 u4 u5 x : Nat) : Nat :=
  swm (2 ^ 6) u5 (swm (2 ^ 30) u4 (swm (2 ^ 126) u3 (swm (2 ^ 3) u2 (swm (2 ^ 15) u1 (swm (2 ^ 63) u0 x)))))

theorem unz_lt (u0 u1 u2 u3 u4 u5 x : Nat) : unz u0 u1 u2 u3 u4 u5 x < 2 ^ 256 := swm_lt _ _ _

theorem disjU0 : ∀ q, U0.testBit q = true → ¬ (63 ≤ q ∧ U0.testBit (q - 63) = true) :=
  disj_of_lt (by unfold U0; norm_num) (by unfold U0; decide +kernel)
theorem disjU1 : ∀ q, U1.testBit q = true → ¬ (15 ≤ q ∧ U1.testBit (q - 15) = true) :=
  disj_of_lt (by unfold U1; norm_num) (by unfold U1; decide +kernel)
theorem disjU2 : ∀ q, U2.testBit q = true → ¬ (3 ≤ q ∧ U2.testBit (q - 3) = true) :=
  disj_of_lt (by unfold U2; norm_num) (by unfold U2; decide +kernel)
theorem disjU3 : ∀ q, U3.testBit q = true → ¬ (126 ≤ q ∧ U3.testBit (q - 126) = true) :=
  disj_of_lt (by unfold U3; norm_num) (by unfold U3; decide +kernel)
theorem disjU4 : ∀ q, U4.testBit q = true → ¬ (30 ≤ q ∧ U4.testBit (q - 30) = true) :=
  disj_of_lt (by unfold U4; norm_num) (by unfold U4; decide +kernel)
theorem disjU5 : ∀ q, U5.testBit q = true → ¬ (6 ≤ q ∧ U5.testBit (q - 6) = true) :=
  disj_of_lt (by unfold U5; norm_num) (by unfold U5; decide +kernel)

/-- The composed source map of the network: bit `4b + k ↦ 64k + b`. -/
theorem src_chain : ∀ p, p < 256 →
    src 6 U5 p < 256 ∧ src 30 U4 (src 6 U5 p) < 256 ∧
    src 126 U3 (src 30 U4 (src 6 U5 p)) < 256 ∧
    src 3 U2 (src 126 U3 (src 30 U4 (src 6 U5 p))) < 256 ∧
    src 15 U1 (src 3 U2 (src 126 U3 (src 30 U4 (src 6 U5 p)))) < 256 ∧
    src 63 U0 (src 15 U1 (src 3 U2 (src 126 U3 (src 30 U4 (src 6 U5 p))))) =
      4 * (p % 64) + p / 64 := by
  unfold src U0 U1 U2 U3 U4 U5; decide +kernel

theorem testBit_unz (x p : Nat) :
    (unz U0 U1 U2 U3 U4 U5 x).testBit p = (decide (p < 256) && x.testBit (4 * (p % 64) + p / 64)) := by
  unfold unz
  by_cases hp : p < 256
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := src_chain p hp
    rw [testBit_swm _ _ _ _ disjU5, testBit_swm _ _ _ _ disjU4, testBit_swm _ _ _ _ disjU3,
      testBit_swm _ _ _ _ disjU2, testBit_swm _ _ _ _ disjU1, testBit_swm _ _ _ _ disjU0]
    simp only [hp, h1, h2, h3, h4, h5, h6, decide_true, Bool.true_and]
  · rw [testBit_swm _ _ _ _ disjU5]; simp [hp]

/-! ## Lanes -/

theorem testBit_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) (p : Nat) :
    (pack4 v).testBit p = (decide (p < 256) && (v (p / 64)).testBit (p % 64)) := by
  have e : pack4 v = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v 3 + v 2) + v 1) + v 0 := by unfold pack4; ring
  rw [e, Nat.testBit_two_pow_mul_add _ (h 0 (by omega))]
  split
  · rename_i hp; rw [show p / 64 = 0 by omega, show p % 64 = p by omega]; simp [show p < 256 by omega]
  rw [Nat.testBit_two_pow_mul_add _ (h 1 (by omega))]
  split
  · rename_i _ hp; rw [show p / 64 = 1 by omega, show p % 64 = p - 64 by omega]
    simp [show p < 256 by omega]
  rw [Nat.testBit_two_pow_mul_add _ (h 2 (by omega))]
  split
  · rename_i _ _ hp; rw [show p / 64 = 2 by omega, show p % 64 = p - 64 - 64 by omega]
    simp [show p < 256 by omega]
  by_cases hp : p < 256
  · rw [show p / 64 = 3 by omega, show p % 64 = p - 64 - 64 - 64 by omega]; simp [hp]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (h 3 (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hp]

/-- De-interleaving an interleaved word gives the lanes. -/
theorem unz_il {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) :
    unz U0 U1 U2 U3 U4 U5 (il v) = pack4 v := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [testBit_unz, testBit_il, testBit_pack4 h]
  by_cases hp : p < 256
  · have e1 : (4 * (p % 64) + p / 64) % 4 = p / 64 := by omega
    have e2 : (4 * (p % 64) + p / 64) / 4 = p % 64 := by omega
    simp [hp, e1, e2, show 4 * (p % 64) + p / 64 < 256 by omega]
  · simp [hp]

/-- Bits of a complemented 64-bit value. -/
theorem testBit_sub64 {v : Nat} (hv : v < 2 ^ 64) {i : Nat} (hi : i < 64) :
    (2 ^ 64 - 1 - v).testBit i = !v.testBit i := by
  have h1 : (~~~(BitVec.ofNat 64 v)).toNat = 2 ^ 64 - 1 - v := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  rw [← h1, BitVec.testBit_toNat, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  simp [hi]

/-- Complementing every bit of `il` of complemented lanes gives `il` of the lanes. -/
theorem not_il {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) :
    2 ^ 256 - 1 - il (fun k => 2 ^ 64 - 1 - v k) = il v := by
  apply Nat.eq_of_testBit_eq; intro p
  have hl := il_lt (fun k => 2 ^ 64 - 1 - v k)
  have h1 : (~~~(BitVec.ofNat 256 (il fun k => 2 ^ 64 - 1 - v k))).toNat =
      2 ^ 256 - 1 - il (fun k => 2 ^ 64 - 1 - v k) := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  rw [← h1, BitVec.testBit_toNat, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, testBit_il, testBit_il]
  by_cases hp : p < 256
  · have hk : p % 4 < 4 := Nat.mod_lt _ (by omega)
    simp only [hp, decide_true, Bool.true_and, testBit_sub64 (h _ hk) (show p / 4 < 64 by omega),
      Bool.not_not]
  · simp [hp]

/-! ## Lane masks and candidate extraction -/

/-- Bit pattern of a lane mask `lanemask n` (low `n` bits of every lane). -/
def LM (M n : Nat) : Prop := ∀ q, M.testBit q = (decide (q < 256) && decide (q % 64 < n))

theorem LM_of {M n : Nat} (hM : M < 2 ^ 256) (h : ∀ q, q < 256 → M.testBit q = decide (q % 64 < n)) :
    LM M n := by
  intro q
  by_cases hq : q < 256
  · rw [h q hq]; simp [hq]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hq]

def M23 : Nat := 0x7fffff00000000007fffff00000000007fffff00000000007fffff
def M16 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def M7 : Nat := 0x7f000000000000007f000000000000007f000000000000007f
def M15 : Nat := 0x7fff0000000000007fff0000000000007fff0000000000007fff
def M8 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
/-- `2^23 − q` in every lane. -/
def CF : Nat := 0x1fff0000000000001fff0000000000001fff0000000000001fff

theorem LM23 : LM M23 23 := LM_of (by unfold M23; norm_num) (by unfold M23; decide +kernel)
theorem LM16 : LM M16 16 := LM_of (by unfold M16; norm_num) (by unfold M16; decide +kernel)
theorem LM7 : LM M7 7 := LM_of (by unfold M7; norm_num) (by unfold M7; decide +kernel)
theorem LM15 : LM M15 15 := LM_of (by unfold M15; norm_num) (by unfold M15; decide +kernel)
theorem LM8 : LM M8 8 := LM_of (by unfold M8; norm_num) (by unfold M8; decide +kernel)

theorem CF_eq : CF = pack4 fun _ => 8191 := by unfold CF pack4; norm_num

theorem and_pack4_div {v : Nat → Nat} (hv : ∀ k, k < 4 → v k < 2 ^ 64) {M n : Nat} (hM : LM M n)
    (s : Nat) (hns : n + s ≤ 64) :
    (M &&& pack4 v / 2 ^ s) = pack4 fun k => v k / 2 ^ s % 2 ^ n := by
  have hv' : ∀ k, k < 4 → v k / 2 ^ s % 2 ^ n < 2 ^ 64 := fun k _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega))
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_and, hM, Nat.testBit_div_two_pow, testBit_pack4 hv, testBit_pack4 hv',
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hp : p < 256
  · by_cases hn : p % 64 < n
    · have e1 : (p + s) / 64 = p / 64 := by omega
      have e2 : (p + s) % 64 = p % 64 + s := by omega
      simp [hp, hn, e1, e2, show p + s < 256 by omega]
    · simp [hn]
  · simp [hp]

theorem and_pack4 {v : Nat → Nat} (hv : ∀ k, k < 4 → v k < 2 ^ 64) {M n : Nat} (hM : LM M n)
    (hn : n ≤ 64) : (M &&& pack4 v) = pack4 fun k => v k % 2 ^ n := by
  have := and_pack4_div hv hM 0 (by omega)
  simpa using this

theorem split_pack4 {u v : Nat → Nat} (hu : ∀ k, k < 4 → u k < 2 ^ 64)
    (hv : ∀ k, k < 4 → v k < 2 ^ 64) {Ma Mb a b : Nat} (hMa : LM Ma a) (hMb : LM Mb b)
    (s : Nat) (hs : s + b = 64) (hab : a + b ≤ 64) :
    ((Ma &&& pack4 u) * 2 ^ b ||| Mb &&& pack4 v / 2 ^ s) =
      pack4 fun k => v k / 2 ^ s % 2 ^ b + 2 ^ b * (u k % 2 ^ a) := by
  have hlt : ∀ k, v k / 2 ^ s % 2 ^ b < 2 ^ b := fun k => Nat.mod_lt _ (by positivity)
  have hv' : ∀ k, k < 4 → v k / 2 ^ s % 2 ^ b + 2 ^ b * (u k % 2 ^ a) < 2 ^ 64 := by
    intro k _
    have h1 := hlt k
    have h2 : u k % 2 ^ a < 2 ^ a := Nat.mod_lt _ (by positivity)
    have h3 : 2 ^ b * (u k % 2 ^ a) + 2 ^ b ≤ 2 ^ b * 2 ^ a := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
    have h4 : 2 ^ b * 2 ^ a ≤ 2 ^ 64 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_or, Nat.testBit_mul_two_pow, Nat.testBit_and, Nat.testBit_and, hMa, hMb,
    Nat.testBit_div_two_pow, testBit_pack4 hu, testBit_pack4 hv, testBit_pack4 hv']
  rw [Nat.add_comm (v (p / 64) / 2 ^ s % 2 ^ b), Nat.testBit_two_pow_mul_add _ (hlt _)]
  by_cases hp : p < 256
  · by_cases hb : p % 64 < b
    · have e1 : (p + s) / 64 = p / 64 := by omega
      have e2 : (p + s) % 64 = p % 64 + s := by omega
      have hpb : ¬ (b ≤ p ∧ (p - b) % 64 < a) := by omega
      simp only [hp, hb, decide_true, Bool.true_and, if_true, Nat.testBit_mod_two_pow,
        Nat.testBit_div_two_pow, e1, e2, show p + s < 256 by omega]
      have : (decide (b ≤ p) && (decide (p - b < 256) && decide ((p - b) % 64 < a) &&
          (decide (p - b < 256) && (u ((p - b) / 64)).testBit ((p - b) % 64)))) = false := by
        by_cases h1 : b ≤ p
        · have : ¬ ((p - b) % 64 < a) := by omega
          simp [this]
        · simp [h1]
      rw [this, Bool.false_or]
    · have e1 : (p - b) / 64 = p / 64 := by omega
      have e2 : (p - b) % 64 = p % 64 - b := by omega
      simp only [hp, hb, decide_false, Bool.false_and, Bool.or_false, if_false, Bool.true_and,
        decide_true, show b ≤ p by omega, show p - b < 256 by omega, e1, e2,
        Nat.testBit_mod_two_pow]
  · have h1 : (decide (b ≤ p) && (decide (p - b < 256) && decide ((p - b) % 64 < a) &&
        (decide (p - b < 256) && (u ((p - b) / 64)).testBit ((p - b) % 64)))) = false := by
      by_cases h2 : p - b < 256
      · have : ¬ ((p - b) % 64 < a) := by omega
        simp [this]
      · simp [h2]
    rw [h1]; simp [hp]

/-! ## The candidate words and the flag accumulator, as computed by the code -/

def c0 (d0 _d1 _d2 : Nat) : Nat := M23 &&& d0
def c1 (d0 _d1 _d2 : Nat) : Nat := M23 &&& d0 / 2 ^ 24
def c2 (d0 d1 _d2 : Nat) : Nat := (M7 &&& d1) * 2 ^ 16 ||| M16 &&& d0 / 2 ^ 48
def c3 (_d0 d1 _d2 : Nat) : Nat := M23 &&& d1 / 2 ^ 8
def c4 (_d0 d1 _d2 : Nat) : Nat := M23 &&& d1 / 2 ^ 32
def c5 (_d0 d1 d2 : Nat) : Nat := (M15 &&& d2) * 2 ^ 8 ||| M8 &&& d1 / 2 ^ 56
def c6 (_d0 _d1 d2 : Nat) : Nat := M23 &&& d2 / 2 ^ 16
def c7 (_d0 _d1 d2 : Nat) : Nat := M23 &&& d2 / 2 ^ 40

/-- The flag accumulator: `lf ← (CF + c_k) | lf` for `k = 0 … 7`. -/
def lfv (d0 d1 d2 : Nat) : Nat :=
  CF + c7 d0 d1 d2 ||| (CF + c6 d0 d1 d2 ||| (CF + c5 d0 d1 d2 ||| (CF + c4 d0 d1 d2 |||
    (CF + c3 d0 d1 d2 ||| (CF + c2 d0 d1 d2 ||| (CF + c1 d0 d1 d2 ||| (CF + c0 d0 d1 d2 ||| 0)))))))

/-! ## Lane form of the candidate words -/

section lanes
variable {v0 v1 v2 : Nat → Nat} (h0 : ∀ k, k < 4 → v0 k < 2 ^ 64) (h1 : ∀ k, k < 4 → v1 k < 2 ^ 64)
  (h2 : ∀ k, k < 4 → v2 k < 2 ^ 64)
include h0 h1 h2

theorem c0_pack4 : c0 (pack4 v0) (pack4 v1) (pack4 v2) = pack4 fun k => v0 k % 2 ^ 23 :=
  and_pack4 h0 LM23 (by omega)
theorem c1_pack4 : c1 (pack4 v0) (pack4 v1) (pack4 v2) = pack4 fun k => v0 k / 2 ^ 24 % 2 ^ 23 :=
  and_pack4_div h0 LM23 24 (by omega)
theorem c2_pack4 : c2 (pack4 v0) (pack4 v1) (pack4 v2) =
    pack4 fun k => v0 k / 2 ^ 48 % 2 ^ 16 + 2 ^ 16 * (v1 k % 2 ^ 7) :=
  split_pack4 h1 h0 LM7 LM16 48 (by omega) (by omega)
theorem c3_pack4 : c3 (pack4 v0) (pack4 v1) (pack4 v2) = pack4 fun k => v1 k / 2 ^ 8 % 2 ^ 23 :=
  and_pack4_div h1 LM23 8 (by omega)
theorem c4_pack4 : c4 (pack4 v0) (pack4 v1) (pack4 v2) = pack4 fun k => v1 k / 2 ^ 32 % 2 ^ 23 :=
  and_pack4_div h1 LM23 32 (by omega)
theorem c5_pack4 : c5 (pack4 v0) (pack4 v1) (pack4 v2) =
    pack4 fun k => v1 k / 2 ^ 56 % 2 ^ 8 + 2 ^ 8 * (v2 k % 2 ^ 15) :=
  split_pack4 h2 h1 LM15 LM8 56 (by omega) (by omega)
theorem c6_pack4 : c6 (pack4 v0) (pack4 v1) (pack4 v2) = pack4 fun k => v2 k / 2 ^ 16 % 2 ^ 23 :=
  and_pack4_div h2 LM23 16 (by omega)
theorem c7_pack4 : c7 (pack4 v0) (pack4 v1) (pack4 v2) = pack4 fun k => v2 k / 2 ^ 40 % 2 ^ 23 :=
  and_pack4_div h2 LM23 40 (by omega)

end lanes

theorem CF_add_pack4 (a : Nat → Nat) : CF + pack4 a = pack4 fun k => a k + 8191 := by
  rw [CF_eq]; unfold pack4; ring

theorem lor8 (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) :
    (a7 ||| (a6 ||| (a5 ||| (a4 ||| (a3 ||| (a2 ||| (a1 ||| (a0 ||| 0)))))))) =
      orList [a0, a1, a2, a3, a4, a5, a6, a7] := by
  unfold orList
  apply Nat.eq_of_testBit_eq; intro p
  simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_or, Nat.zero_testBit, Bool.or_false,
    Bool.false_or]
  cases a0.testBit p <;> cases a1.testBit p <;> cases a2.testBit p <;> cases a3.testBit p <;>
    cases a4.testBit p <;> cases a5.testBit p <;> cases a6.testBit p <;> cases a7.testBit p <;> rfl

/-- Lane-wise byte decomposition of a 23-bit field inside one lane. -/
theorem field23 (L s : Nat) :
    L / 2 ^ s % 2 ^ 23 = L / 2 ^ s % 256 + 256 * (L / 2 ^ (s + 8) % 256) +
      65536 * (L / 2 ^ (s + 16) % 256 % 128) := by
  rw [show s + 8 = s + 8 from rfl, Nat.pow_add, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul]
  generalize L / 2 ^ s = x
  omega

/-! ## Memory transformers of the blocks -/

section mem
open EvmSemantics EvmSemantics.EVM

/-- `MSTORE (NOT (MLOAD a)) a`. -/
def flipW (M : ByteArray) (a : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded (2 ^ 256 - 1 - word M a) 32) a

/-- The six complemented rate lanes `1, 2, 8, 12, 17, 20` of `KS` inverted in place. -/
def flip6 (M : ByteArray) : ByteArray :=
  flipW (flipW (flipW (flipW (flipW (flipW M 32) 64) 256) 384) 544) 640

/-- The eight candidate-word stores of one loop iteration. -/
def candMem (M : ByteArray) (abp d0 d1 d2 : Nat) : ByteArray :=
  let w := fun (M : ByteArray) (v a : Nat) =>
    MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v % 2 ^ 256) 32) a
  w (w (w (w (w (w (w (w M (c0 d0 d1 d2) abp) (c1 d0 d1 d2) (32 + abp)) (c2 d0 d1 d2) (64 + abp))
    (c3 d0 d1 d2) (96 + abp)) (c4 d0 d1 d2) (128 + abp)) (c5 d0 d1 d2) (160 + abp))
    (c6 d0 d1 d2) (192 + abp)) (c7 d0 d1 d2) (224 + abp)

theorem ofNat_swm (c u x : Nat) :
    UInt256.ofNat ((u &&& (x ^^^ x / c)) * c ^^^ u &&& (x ^^^ x / c) ^^^ x) =
      UInt256.ofNat (swm c u x) := by
  rw [swm, ofNat_mod]

theorem swm_mod (c u x : Nat) :
    swm c u x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      swm c u x := by
  rw [swm]; exact Nat.mod_mod _ _

end mem

end MlDsaOpt44.Proofs.Blk
