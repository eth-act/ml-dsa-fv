import MlDsaOpt44.Fn.Sponge.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `trabs` (v4): the byte-swap-and-zip delta-swap network (R4-2)

v4's `trabs` applies seven delta swaps (`TRZIP` in `gen_opt.py`) to the
`CALLDATALOAD` word `W`: bit `64 k + q` of `W` lands at bit `4 n + k`, where
`n` is the little-endian position of that bit in the byte-swapped lane `k`.
So `S0 &&& Z / 2^(3 − j)` is `spread` of calldata lane `j`
(`trabsNet_lane`). The mask of the last group is applied to `W` before the
network; for lane-aligned masks this is the mask after the byte swap
(`bswapNet_and_lane`).

A delta swap `dsw d U x` is in the exact form `opt44_block` leaves it; its bit
map (`dswMap`) is checked per stage and composed by `decide +kernel`.
-/

namespace MlDsaOpt44.Proofs.WP4

open MlDsaOptCommon

/-- One delta swap `t = U & (x ^ x >> d); x ^ t ^ t << d` (block normal form). -/
def dsw (d U x : Nat) : Nat :=
  (U &&& (x ^^^ x % 2 ^ 256 / 2 ^ d)) * 2 ^ d ^^^ U &&& (x ^^^ x % 2 ^ 256 / 2 ^ d) ^^^ x

/-- The source bit of output bit `j` of `dsw d U`. -/
def dswMap (d U j : Nat) : Nat :=
  if U.testBit j then j + d else if d ≤ j ∧ U.testBit (j - d) = true then j - d else j

/-- A delta swap's mask is well formed on bit `j`. -/
def dswOK (d U j : Nat) : Bool :=
  (!U.testBit j || decide (j + d < 256)) && (!(decide (d ≤ j) && U.testBit (j - d)) || !U.testBit j)

theorem dsw_testBit {d U x j : Nat} (hx : x < 2 ^ 256) (hj : j < 256) (hok : dswOK d U j = true) :
    (dsw d U x).testBit j = x.testBit (dswMap d U j) := by
  unfold dswOK at hok
  unfold dsw dswMap
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_mod_two_pow, Nat.mod_eq_of_lt hx]
  have hge : ∀ i, 256 ≤ i → x.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi))
  by_cases hU : U.testBit j = true
  · simp only [hU, if_true]
    have h1 : j + d < 256 := by simp [hU] at hok; omega
    by_cases hd : d ≤ j
    · have h2 : U.testBit (j - d) = false := by
        simp only [hU, decide_eq_true hd, Bool.true_and, Bool.not_true, Bool.false_or,
          Bool.and_true, decide_true, Bool.true_or] at hok
        simp only [Bool.or_false, Bool.and_eq_true, Bool.not_eq_true'] at hok
        exact hok.2
      simp [hd, h2, Nat.testBit_lt_two_pow, show j + d < 256 by omega]
      cases x.testBit j <;> cases x.testBit (j + d) <;> rfl
    · simp [hd, show j + d < 256 by omega]
      cases x.testBit j <;> cases x.testBit (j + d) <;> rfl
  · have hU' : U.testBit j = false := by simpa using hU
    simp only [hU', Bool.false_and, Bool.false_xor, Bool.false_eq_true, if_false]
    by_cases hd : d ≤ j ∧ U.testBit (j - d) = true
    · rw [if_pos hd]
      simp only [decide_eq_true hd.1, hd.2, Bool.true_and, Nat.sub_add_cancel hd.1,
        show j < 2 ^ 256 from by omega]
      by_cases hj' : j < 256
      · simp [hj']
      · omega
    · rw [if_neg hd]
      by_cases hd' : d ≤ j
      · have : U.testBit (j - d) = false := by simpa [hd'] using hd
        simp [hd', this]
      · simp [hd']

/-! ## The network -/

def tzU0 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def tzU1 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def tzU2 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def tzU3 : Nat := 0xcccccccccccccccccccccccccccccccc
def tzU4 : Nat := 0x0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def tzU5 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def tzU6 : Nat := 0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
def tzS0 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111

/-- `trabs`'s network on the (masked) calldata word. -/
def trabsNet (x : Nat) : Nat :=
  dsw 63 tzU6 (dsw 15 tzU5 (dsw 3 tzU4 (dsw 126 tzU3 (dsw 34 tzU2 (dsw 6 tzU1 (dsw 16 tzU0 x))))))

/-- The composed source map (outermost stage first). -/
def trabsMap (j : Nat) : Nat :=
  dswMap 16 tzU0 (dswMap 6 tzU1 (dswMap 34 tzU2 (dswMap 126 tzU3 (dswMap 3 tzU4
    (dswMap 15 tzU5 (dswMap 63 tzU6 j))))))

/-- Every stage is well formed on every bit it is asked about. -/
theorem trabs_ok : ∀ j, j < 256 →
    dswOK 63 tzU6 j = true ∧ dswMap 63 tzU6 j < 256 ∧
    dswOK 15 tzU5 (dswMap 63 tzU6 j) = true ∧
    dswMap 15 tzU5 (dswMap 63 tzU6 j) < 256 ∧
    dswOK 3 tzU4 (dswMap 15 tzU5 (dswMap 63 tzU6 j)) = true ∧
    dswMap 3 tzU4 (dswMap 15 tzU5 (dswMap 63 tzU6 j)) < 256 ∧
    dswOK 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5 (dswMap 63 tzU6 j))) = true ∧
    dswMap 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5 (dswMap 63 tzU6 j))) < 256 ∧
    dswOK 34 tzU2 (dswMap 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5 (dswMap 63 tzU6 j)))) = true ∧
    dswMap 34 tzU2 (dswMap 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5 (dswMap 63 tzU6 j)))) < 256 ∧
    dswOK 6 tzU1 (dswMap 34 tzU2 (dswMap 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5
      (dswMap 63 tzU6 j))))) = true ∧
    dswMap 6 tzU1 (dswMap 34 tzU2 (dswMap 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5
      (dswMap 63 tzU6 j))))) < 256 ∧
    dswOK 16 tzU0 (dswMap 6 tzU1 (dswMap 34 tzU2 (dswMap 126 tzU3 (dswMap 3 tzU4 (dswMap 15 tzU5
      (dswMap 63 tzU6 j)))))) = true := by
  decide +kernel

/-- The permutation: output bit `4 b + k` is bit `64 k + 8 (7 − b/8) + b mod 8` of the input. -/
theorem trabsMap_eq : ∀ b, b < 64 → ∀ k, k < 4 →
    trabsMap (4 * b + k) = 64 * k + 8 * (7 - b / 8) + b % 8 := by
  decide +kernel

theorem tzS0_testBit : ∀ p, p < 256 → tzS0.testBit p = decide (p % 4 = 0) := by
  decide +kernel

theorem dsw_lt {d U x : Nat} (hx : x < 2 ^ 256) (hok : ∀ j, j < 256 → dswOK d U j = true)
    (hU : U < 2 ^ 256) : dsw d U x < 2 ^ 256 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold dsw
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_mul_two_pow]
  have hUj : U.testBit j = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hU (Nat.pow_le_pow_right (by omega) hj))
  have hxj : x.testBit j = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
  simp only [hUj, hxj, Bool.false_and, Bool.xor_false]
  by_cases hd : d ≤ j
  · by_cases hU' : U.testBit (j - d) = true
    · by_cases hjd : j - d < 256
      · have := hok (j - d) hjd
        simp [dswOK, hU'] at this; omega
      · exact absurd hU' (by
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hU (Nat.pow_le_pow_right (by omega) (by omega)))]
          simp)
    · simp [hd, hU']
  · simp [hd]

theorem trabs_okall : ∀ j, j < 256 → dswOK 16 tzU0 j = true ∧ dswOK 6 tzU1 j = true ∧
    dswOK 34 tzU2 j = true ∧ dswOK 126 tzU3 j = true ∧ dswOK 3 tzU4 j = true ∧
    dswOK 15 tzU5 j = true ∧ dswOK 63 tzU6 j = true := by decide +kernel

theorem trabsNet_lt {x : Nat} (hx : x < 2 ^ 256) : trabsNet x < 2 ^ 256 := by
  have b0 := dsw_lt hx (fun j hj => (trabs_okall j hj).1) (by decide : tzU0 < 2 ^ 256)
  have b1 := dsw_lt b0 (fun j hj => (trabs_okall j hj).2.1) (by decide : tzU1 < 2 ^ 256)
  have b2 := dsw_lt b1 (fun j hj => (trabs_okall j hj).2.2.1) (by decide : tzU2 < 2 ^ 256)
  have b3 := dsw_lt b2 (fun j hj => (trabs_okall j hj).2.2.2.1) (by decide : tzU3 < 2 ^ 256)
  have b4 := dsw_lt b3 (fun j hj => (trabs_okall j hj).2.2.2.2.1) (by decide : tzU4 < 2 ^ 256)
  have b5 := dsw_lt b4 (fun j hj => (trabs_okall j hj).2.2.2.2.2.1) (by decide : tzU5 < 2 ^ 256)
  exact dsw_lt b5 (fun j hj => (trabs_okall j hj).2.2.2.2.2.2) (by decide : tzU6 < 2 ^ 256)

theorem trabsNet_testBit {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : j < 256) :
    (trabsNet x).testBit j = x.testBit (trabsMap j) := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6', h7⟩ := trabs_ok j hj
  have b0 := dsw_lt hx (fun j hj => (trabs_okall j hj).1) (by decide : tzU0 < 2 ^ 256)
  have b1 := dsw_lt b0 (fun j hj => (trabs_okall j hj).2.1) (by decide : tzU1 < 2 ^ 256)
  have b2 := dsw_lt b1 (fun j hj => (trabs_okall j hj).2.2.1) (by decide : tzU2 < 2 ^ 256)
  have b3 := dsw_lt b2 (fun j hj => (trabs_okall j hj).2.2.2.1) (by decide : tzU3 < 2 ^ 256)
  have b4 := dsw_lt b3 (fun j hj => (trabs_okall j hj).2.2.2.2.1) (by decide : tzU4 < 2 ^ 256)
  have b5 := dsw_lt b4 (fun j hj => (trabs_okall j hj).2.2.2.2.2.1) (by decide : tzU5 < 2 ^ 256)
  unfold trabsNet trabsMap
  rw [dsw_testBit b5 hj h1, dsw_testBit b4 h1' h2, dsw_testBit b3 h2' h3, dsw_testBit b2 h3' h4,
    dsw_testBit b1 h4' h5, dsw_testBit b0 h5' h6, dsw_testBit hx h6' h7]

/-- Lane `j` of the zipped word, as the code extracts it. -/
theorem trabsNet_lane {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : j < 4) :
    (tzS0 &&& trabsNet x % 2 ^ 256 / 2 ^ (3 - j)) = spread (bswapNet x / 2 ^ (192 - 64 * j) % 2 ^ 64) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_spread, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases hp : p < 256
  · rw [tzS0_testBit p hp]
    by_cases h4 : p % 4 = 0
    · have hb : p / 4 < 64 := by omega
      simp only [h4, decide_true, Bool.true_and, hb]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, bswapNet_testBit hx (by omega)]
      by_cases h3 : p + (3 - j) < 256
      · simp only [h3, decide_true, Bool.true_and, hb]
        rw [trabsNet_testBit hx h3, show p + (3 - j) = 4 * (p / 4) + (3 - j) by omega,
          trabsMap_eq (p / 4) hb (3 - j) (by omega)]
        congr 1; omega
      · omega
    · simp [h4]
  · have : ¬ p / 4 < 64 := by omega
    simp only [this, decide_false, Bool.and_false, Bool.false_and]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by unfold tzS0; norm_num : tzS0 < 2 ^ 256)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp

/-- A lane-aligned mask commutes with the per-lane byte swap. -/
theorem bswapNet_and_lane {lm x : Nat} (hx : x < 2 ^ 256) (hlm : lm < 2 ^ 256)
    (hL : ∀ k, k < 4 → lane lm k = 0 ∨ lane lm k = M64) :
    bswapNet (lm &&& x) = lm &&& bswapNet x := by
  have hax : lm &&& x < 2 ^ 256 := Nat.lt_of_le_of_lt Nat.and_le_left hlm
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 256
  · rw [bswapNet_testBit hax hj, Nat.testBit_and, Nat.testBit_and, bswapNet_testBit hx hj]
    congr 1
    have hbit : ∀ i, i < 256 → lm.testBit i = (lane lm (i / 64)).testBit (i % 64) := by
      intro i hi
      unfold lane
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true (Nat.mod_lt _ (by omega)),
        Bool.true_and]
      congr 1; omega
    rw [hbit _ (by omega), hbit j hj, show (64 * (j / 64) + 8 * (7 - j % 64 / 8) + j % 8) / 64 = j / 64 by omega]
    rcases hL (j / 64) (by omega) with h | h
    · rw [h]; simp
    · rw [h, M64, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_true (Nat.mod_lt _ (by omega : 64 > 0))]
  · have hge : ∀ y, y < 2 ^ 256 → y.testBit j = false := fun y hy =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hge _ (bswapNet_lt _), Nat.testBit_and, hge _ hlm]; rfl

end MlDsaOpt44.Proofs.WP4
