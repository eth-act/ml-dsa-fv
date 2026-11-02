import MlDsaOpt44.Math.Bswap
set_option warningAsError true
/-!
# Bit-level lemmas for the sponge glue (WP4)

* `testBit_spread`, `testBit_compress`, `testBit_le64`, `testBit_word`,
  `testBit_pack4`: the bit layout of the representations.
* `sprNet` (the `spr` shift-or-mask network, in `opt44_block` normal form) is
  `spread` on 64-bit inputs (`sprNet_eq`); `compNet` (the `cext` network) is
  `compress` of the slot bits (`compNet_eq`).
-/

namespace MlDsaOpt44.Proofs.WP4

open MlDsaOptCommon

/-! ## Generic sums of disjoint bit fields -/

theorem testBit_add_two_pow_mul {S c n : Nat} (hS : S < 2 ^ n) (j : Nat) :
    (S + c * 2 ^ n).testBit j = if j < n then S.testBit j else c.testBit (j - n) := by
  rw [show S + c * 2 ^ n = 2 ^ n * c + S by ring, Nat.testBit_two_pow_mul_add _ hS]

theorem testBit_mod_two (v b k : Nat) :
    (v / 2 ^ b % 2).testBit k = (decide (k = 0) && v.testBit b) := by
  rw [show v / 2 ^ b % 2 = v / 2 ^ b % 2 ^ 1 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, decide_false, Bool.false_and]
    rw [decide_eq_false (by omega), Bool.false_and]

/-- Partial sums of `spread`. -/
theorem spread_partial (v : Nat) : ∀ n,
    ((List.range n).map fun b => v / 2 ^ b % 2 * 2 ^ (4 * b)).sum < 2 ^ (4 * n) ∧
    ∀ j, ((List.range n).map fun b => v / 2 ^ b % 2 * 2 ^ (4 * b)).sum.testBit j =
      (decide (j % 4 = 0) && decide (j / 4 < n) && v.testBit (j / 4))
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hlt, hbit⟩ := spread_partial v n
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hc : v / 2 ^ n % 2 < 2 := Nat.mod_lt _ (by omega)
    constructor
    · have : 2 ^ (4 * (n + 1)) = 2 ^ (4 * n) * 16 := by rw [Nat.mul_add, Nat.pow_add]
      rw [this]
      have : v / 2 ^ n % 2 * 2 ^ (4 * n) ≤ 1 * 2 ^ (4 * n) := Nat.mul_le_mul_right _ (by omega)
      omega
    · intro j
      rw [testBit_add_two_pow_mul hlt, testBit_mod_two]
      split
      · rw [hbit]
        simp [show j / 4 < n by omega, show j / 4 < n + 1 by omega]
      · by_cases hj : j = 4 * n
        · subst hj; simp
        · have : j - 4 * n ≠ 0 := by omega
          simp only [this, decide_false, Bool.false_and]
          by_cases h4 : j % 4 = 0
          · simp [h4, show ¬ j / 4 < n + 1 by omega]
          · simp [h4]

theorem testBit_spread (v j : Nat) :
    (spread v).testBit j = (decide (j % 4 = 0) && decide (j / 4 < 64) && v.testBit (j / 4)) :=
  (spread_partial v 64).2 j

theorem spread_lt (v : Nat) : spread v < 2 ^ 256 := (spread_partial v 64).1

/-- Partial sums of `compress`. -/
theorem compress_partial (w : Nat) : ∀ n,
    ((List.range n).map fun b => w / 2 ^ (4 * b) % 2 * 2 ^ b).sum < 2 ^ n ∧
    ∀ j, ((List.range n).map fun b => w / 2 ^ (4 * b) % 2 * 2 ^ b).sum.testBit j =
      (decide (j < n) && w.testBit (4 * j))
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hlt, hbit⟩ := compress_partial w n
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hc : w / 2 ^ (4 * n) % 2 < 2 := Nat.mod_lt _ (by omega)
    constructor
    · rw [Nat.pow_succ]
      have : w / 2 ^ (4 * n) % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      omega
    · intro j
      rw [testBit_add_two_pow_mul hlt, testBit_mod_two]
      split
      · rw [hbit]; simp [show j < n + 1 by omega, *]
      · by_cases hj : j = n
        · subst hj; simp
        · have : j - n ≠ 0 := by omega
          simp [this, show ¬ j < n + 1 by omega]

theorem testBit_compress (w j : Nat) :
    (compress w).testBit j = (decide (j < 64) && w.testBit (4 * j)) :=
  (compress_partial w 64).2 j

theorem compress_lt (w : Nat) : compress w < 2 ^ 64 := (compress_partial w 64).1

/-! ## Bytes -/

theorem testBit_byte_add {S b n : Nat} (hS : S < 2 ^ n) (j : Nat) :
    (S + b * 2 ^ n).testBit j = if j < n then S.testBit j else b.testBit (j - n) :=
  testBit_add_two_pow_mul hS j

/-- Partial sums of `le64`. -/
theorem le64_partial (b : ByteArray) (a : Nat) : ∀ n,
    ((List.range n).map fun i => byteAt b (a + i) * 256 ^ i).sum < 2 ^ (8 * n) ∧
    ∀ j, ((List.range n).map fun i => byteAt b (a + i) * 256 ^ i).sum.testBit j =
      (decide (j / 8 < n) && (byteAt b (a + j / 8)).testBit (j % 8))
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hlt, hbit⟩ := le64_partial b a n
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hb := byteAt_lt b (a + n)
    have hp : (256 : Nat) ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
    rw [hp]
    constructor
    · have : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 := by rw [Nat.mul_add, Nat.pow_add]
      rw [this]
      have : byteAt b (a + n) * 2 ^ (8 * n) ≤ 255 * 2 ^ (8 * n) := Nat.mul_le_mul_right _ (by omega)
      omega
    · intro j
      rw [testBit_add_two_pow_mul hlt]
      split
      · rw [hbit]; simp [show j / 8 < n by omega, show j / 8 < n + 1 by omega]
      · by_cases hj : j < 8 * (n + 1)
        · have h1 : j / 8 = n := by omega
          have h2 : j - 8 * n = j % 8 := by omega
          rw [h1, h2]; simp
        · have h8 : 2 ^ 8 ≤ 2 ^ (j - 8 * n) := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb h8)]
          simp [show ¬ j / 8 < n + 1 by omega]

theorem testBit_le64 (b : ByteArray) (a j : Nat) :
    (le64 b a).testBit j = (decide (j < 64) && (byteAt b (a + j / 8)).testBit (j % 8)) := by
  rw [le64, (le64_partial b a 8).2 j]
  congr 1; simp; omega


/-- Big-endian prefixes (`word`). -/
theorem beNat_partial (m : ByteArray) (a : Nat) : ∀ w,
    beNat m a w < 2 ^ (8 * w) ∧
    ∀ j, (beNat m a w).testBit j =
      (decide (j / 8 < w) && (byteAt m (a + (w - 1 - j / 8))).testBit (j % 8))
  | 0 => by simp [beNat]
  | w + 1 => by
    obtain ⟨hlt, hbit⟩ := beNat_partial m a w
    have hb := byteAt_lt m (a + w)
    simp only [beNat]
    constructor
    · have : 2 ^ (8 * (w + 1)) = 2 ^ (8 * w) * 256 := by rw [Nat.mul_add, Nat.pow_add]
      omega
    · intro j
      rw [show beNat m a w * 256 + byteAt m (a + w) = 2 ^ 8 * beNat m a w + byteAt m (a + w) by
        ring, Nat.testBit_two_pow_mul_add _ hb]
      split
      · have h1 : j / 8 = 0 := by omega
        have h2 : j % 8 = j := by omega
        rw [h1, h2]; simp
      · rw [hbit]
        have h1 : (j - 8) / 8 = j / 8 - 1 := by omega
        have h2 : (j - 8) % 8 = j % 8 := by omega
        rw [h1, h2]
        by_cases hj : j / 8 < w + 1
        · rw [show w - 1 - (j / 8 - 1) = w + 1 - 1 - j / 8 by omega]; simp [hj]; omega
        · simp [hj]; omega

theorem testBit_word (m : ByteArray) (a j : Nat) :
    (word m a).testBit j =
      (decide (j < 256) && (byteAt m (a + (31 - j / 8))).testBit (j % 8)) := by
  rw [word_eq_beNat, (beNat_partial m a 32).2 j]
  congr 1; simp; omega

/-! ## Lanes -/

theorem testBit_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) (j : Nat) :
    (pack4 v).testBit j =
      if j < 64 then (v 0).testBit j else if j < 128 then (v 1).testBit (j - 64)
      else if j < 192 then (v 2).testBit (j - 128) else (v 3).testBit (j - 192) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  rw [show pack4 v = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v 3 + v 2) + v 1) + v 0 by unfold pack4; ring,
    Nat.testBit_two_pow_mul_add _ h0]
  split
  · rfl
  · rw [Nat.testBit_two_pow_mul_add _ h1]
    split
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), Nat.testBit_two_pow_mul_add _ h2]
      split
      · rw [if_pos (by omega), show j - 64 - 64 = j - 128 by omega]
      · rw [if_neg (by omega), show j - 64 - 64 - 64 = j - 192 by omega]

/-! ## The `spr` network -/

/-- One spreading stage: `M & (y | y << k)`. -/
def sstage (k M y : Nat) : Nat := M &&& (y * 2 ^ k ||| y)

/-- The `spr` network (also inlined in `trabs`). -/
def sprNet (v : Nat) : Nat :=
  sstage 3 0x1111111111111111111111111111111111111111111111111111111111111111
    (sstage 6 0x0303030303030303030303030303030303030303030303030303030303030303
      (sstage 12 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
        (sstage 24 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
          (sstage 48 0xffff000000000000ffff000000000000ffff000000000000ffff
            (sstage 96 0xffffffff000000000000000000000000ffffffff v)))))

theorem sprNet_lt (v : Nat) : sprNet v < 2 ^ 256 := by
  unfold sprNet sstage
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

/-! ## Shift-and-mask networks on symbolic bits

A network value is described bit by bit: bit `j` is the OR of the input bits listed
in `s j`. The stage functions below compute these lists, so a network's bit layout
is checked by evaluating the lists for `j < 256` (`decide +kernel`) instead of
case-splitting on `j` and simplifying every bit. -/

/-- Input `v` with only bits `j < n` possibly set. -/
def symLow (n j : Nat) : List Nat := if j < n then [j] else []

/-- `M &&& y`. -/
def symMask (M : Nat) (s : Nat → List Nat) (j : Nat) : List Nat :=
  if M.testBit j then s j else []

/-- `sstage k M y = M &&& (y * 2 ^ k ||| y)`. -/
def symStage (k M : Nat) (s : Nat → List Nat) (j : Nat) : List Nat :=
  if M.testBit j then (if k ≤ j then s (j - k) else []) ++ s j else []

/-- `M &&& (y % 2 ^ 256 / 2 ^ k ||| y)` (the `cext` stage). -/
def symCStage (k M : Nat) (s : Nat → List Nat) (j : Nat) : List Nat :=
  if M.testBit j then (if j + k < 256 then s (j + k) else []) ++ s j else []

theorem symLow_ok {v n : Nat} (hv : v < 2 ^ n) (j : Nat) :
    v.testBit j = (symLow n j).any v.testBit := by
  unfold symLow
  by_cases hj : j < n
  · simp [hj]
  · simp only [hj, if_false, List.any_nil]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))

theorem symMask_ok {v y : Nat} {s : Nat → List Nat} (M : Nat)
    (h : ∀ j, y.testBit j = (s j).any v.testBit) (j : Nat) :
    (M &&& y).testBit j = (symMask M s j).any v.testBit := by
  unfold symMask
  rw [Nat.testBit_and]
  by_cases hM : M.testBit j <;> simp [hM, h]

theorem symStage_ok {v y : Nat} {s : Nat → List Nat} (k M : Nat)
    (h : ∀ j, y.testBit j = (s j).any v.testBit) (j : Nat) :
    (sstage k M y).testBit j = (symStage k M s j).any v.testBit := by
  unfold sstage symStage
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mul_two_pow]
  by_cases hM : M.testBit j <;> by_cases hk : k ≤ j <;> simp [hM, hk, h, List.any_append]

theorem symCStage_ok {v y : Nat} {s : Nat → List Nat} (k M : Nat)
    (h : ∀ j, y.testBit j = (s j).any v.testBit) (j : Nat) :
    (M &&& (y % 2 ^ 256 / 2 ^ k ||| y)).testBit j = (symCStage k M s j).any v.testBit := by
  unfold symCStage
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases hM : M.testBit j <;> by_cases hk : j + k < 256 <;>
    simp [hM, hk, h, List.any_append]

/-- `sprNet` on symbolic bits. -/
def sprSym : Nat → List Nat :=
  symStage 3 0x1111111111111111111111111111111111111111111111111111111111111111
    (symStage 6 0x0303030303030303030303030303030303030303030303030303030303030303
      (symStage 12 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
        (symStage 24 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
          (symStage 48 0xffff000000000000ffff000000000000ffff000000000000ffff
            (symStage 96 0xffffffff000000000000000000000000ffffffff (symLow 64))))))

theorem sprSym_eq : ∀ j, j < 256 → sprSym j = if j % 4 = 0 then [j / 4] else [] := by
  decide +kernel

theorem sprNet_eq {v : Nat} (hv : v < 2 ^ 64) : sprNet v = spread v := by
  have hs : ∀ j, (sprNet v).testBit j = (sprSym j).any v.testBit :=
    symStage_ok _ _ (symStage_ok _ _ (symStage_ok _ _ (symStage_ok _ _ (symStage_ok _ _
      (symStage_ok _ _ (symLow_ok hv))))))
  apply eq_of_testBit_lt (n := 256) (sprNet_lt v) (spread_lt v)
  intro j hj
  rw [testBit_spread, hs, sprSym_eq j hj]
  by_cases h4 : j % 4 = 0 <;> simp [h4, show j / 4 < 64 by omega]

end MlDsaOpt44.Proofs.WP4
