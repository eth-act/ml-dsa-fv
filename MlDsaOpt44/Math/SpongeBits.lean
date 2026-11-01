import MlDsaOpt44.Layout
set_option warningAsError true
/-!
# Bit-level facts about `spread`, `compress` and `il`

`il v` stores bit `b < 64` of `v k` at bit `4b + k` and nothing else
(`testBit_il`), so it commutes with the bitwise operations (`il_xor`,
`il_and`, `il_or`) and only reads the low 64 bits of each slot.
-/

namespace MlDsaOpt44.Proofs

open MlDsa44

/-- `spread` over the first `n` bits (explicit recursion). -/
def spreadR (v : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => spreadR v n + v / 2 ^ n % 2 * 2 ^ (4 * n)

theorem spread_eq_spreadR (v : Nat) : spread v = spreadR v 64 := by
  suffices h : ∀ n, ((List.range n).map fun b => v / 2 ^ b % 2 * 2 ^ (4 * b)).sum = spreadR v n from
    h 64
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [spreadR]

/-- `compress` over the first `n` bits (explicit recursion). -/
def compressR (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => compressR w n + w / 2 ^ (4 * n) % 2 * 2 ^ n

theorem compress_eq_compressR (w : Nat) : compress w = compressR w 64 := by
  suffices h : ∀ n, ((List.range n).map fun b => w / 2 ^ (4 * b) % 2 * 2 ^ b).sum = compressR w n from
    h 64
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [compressR]

theorem bit_eq (v n : Nat) : v / 2 ^ n % 2 = if v.testBit n then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h]

theorem testBit_bit (v n j : Nat) :
    (v / 2 ^ n % 2).testBit j = (decide (j = 0) && v.testBit n) := by
  rw [bit_eq]
  by_cases hb : v.testBit n
  · simp only [hb, if_true, Bool.and_true]
    rcases j with _ | j
    · decide
    · simp [Nat.testBit_lt_two_pow (show 1 < 2 ^ (j + 1) from Nat.one_lt_two_pow (by omega))]
  · simp [hb]

theorem spreadR_lt (v : Nat) : ∀ n, spreadR v n < 2 ^ (4 * n)
  | 0 => by simp [spreadR]
  | n + 1 => by
    have ih := spreadR_lt v n
    have hb : v / 2 ^ n % 2 ≤ 1 := by omega
    have e : 2 ^ (4 * (n + 1)) = 16 * 2 ^ (4 * n) := by rw [Nat.mul_succ, Nat.pow_add]; ring
    show spreadR v n + v / 2 ^ n % 2 * 2 ^ (4 * n) < _
    rw [e]
    have : v / 2 ^ n % 2 * 2 ^ (4 * n) ≤ 1 * 2 ^ (4 * n) := Nat.mul_le_mul_right _ hb
    omega

theorem testBit_spreadR (v : Nat) :
    ∀ n i, (spreadR v n).testBit i = (decide (i % 4 = 0) && decide (i / 4 < n) && v.testBit (i / 4))
  | 0, i => by simp [spreadR]
  | n + 1, i => by
    show (spreadR v n + v / 2 ^ n % 2 * 2 ^ (4 * n)).testBit i = _
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (spreadR_lt v n), testBit_bit]
    by_cases hi : i < 4 * n
    · rw [if_pos hi, testBit_spreadR v n i]
      have : i / 4 < n := by omega
      simp [this, show i / 4 < n + 1 by omega]
    · rw [if_neg hi]
      by_cases he : i = 4 * n
      · subst he; simp
      · have : ¬ (i - 4 * n = 0) := by omega
        simp only [this, decide_false, Bool.false_and]
        by_cases h4 : i % 4 = 0
        · have : ¬ (i / 4 < n + 1) := by omega
          simp [this]
        · simp [h4]

theorem testBit_spread (v i : Nat) :
    (spread v).testBit i = (decide (i % 4 = 0) && decide (i < 256) && v.testBit (i / 4)) := by
  rw [spread_eq_spreadR, testBit_spreadR]
  have : (i / 4 < 64) = (i < 256) := by apply propext; omega
  simp only [this]

theorem spread_lt (v : Nat) : spread v < 2 ^ 256 := by
  rw [spread_eq_spreadR]; exact spreadR_lt v 64

theorem compressR_lt (w : Nat) : ∀ n, compressR w n < 2 ^ n
  | 0 => by simp [compressR]
  | n + 1 => by
    have ih := compressR_lt w n
    have hb : w / 2 ^ (4 * n) % 2 ≤ 1 := by omega
    show compressR w n + w / 2 ^ (4 * n) % 2 * 2 ^ n < _
    rw [Nat.pow_succ]
    have : w / 2 ^ (4 * n) % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hb
    omega

theorem testBit_compressR (w : Nat) :
    ∀ n i, (compressR w n).testBit i = (decide (i < n) && w.testBit (4 * i))
  | 0, i => by simp [compressR]
  | n + 1, i => by
    show (compressR w n + w / 2 ^ (4 * n) % 2 * 2 ^ n).testBit i = _
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (compressR_lt w n), testBit_bit]
    by_cases hi : i < n
    · rw [if_pos hi, testBit_compressR w n i]
      simp [hi, show i < n + 1 by omega]
    · rw [if_neg hi]
      by_cases he : i = n
      · subst he; simp
      · have : ¬ (i - n = 0) := by omega
        simp [this, show ¬ (i < n + 1) by omega]

theorem testBit_compress (w i : Nat) :
    (compress w).testBit i = (decide (i < 64) && w.testBit (4 * i)) := by
  rw [compress_eq_compressR, testBit_compressR]

/-! ## `il` -/

/-- Nibble `n` of `il v`. -/
def nib (v : Nat → Nat) (n : Nat) : Nat :=
  v 0 / 2 ^ n % 2 + 2 * (v 1 / 2 ^ n % 2) + 4 * (v 2 / 2 ^ n % 2) + 8 * (v 3 / 2 ^ n % 2)

/-- `il` over the first `n` nibbles. -/
def ilR (v : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ilR v n + nib v n * 2 ^ (4 * n)

theorem il_eq_ilR (v : Nat → Nat) : il v = ilR v 64 := by
  suffices h : ∀ n, spreadR (v 0) n + 2 * spreadR (v 1) n + 4 * spreadR (v 2) n +
      8 * spreadR (v 3) n = ilR v n by
    unfold il; rw [spread_eq_spreadR, spread_eq_spreadR, spread_eq_spreadR, spread_eq_spreadR]
    exact h 64
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [spreadR, ilR, nib, ← ih]
    ring

theorem nib_lt (v : Nat → Nat) (n : Nat) : nib v n < 16 := by
  unfold nib; omega

theorem testBit_nib (v : Nat → Nat) (n j : Nat) :
    (nib v n).testBit j = (decide (j < 4) && (v (j % 4)).testBit n) := by
  by_cases hj : j < 4
  · unfold nib
    simp only [bit_eq]
    interval_cases j <;>
      cases v 0 |>.testBit n <;> cases v 1 |>.testBit n <;> cases v 2 |>.testBit n <;>
        cases v 3 |>.testBit n <;> decide
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (nib_lt v n)
      (by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 4 ≤ j by omega); simpa using this))]
    simp [hj]

theorem ilR_lt (v : Nat → Nat) : ∀ n, ilR v n < 2 ^ (4 * n)
  | 0 => by simp [ilR]
  | n + 1 => by
    have ih := ilR_lt v n
    have hb : nib v n ≤ 15 := by have := nib_lt v n; omega
    have e : 2 ^ (4 * (n + 1)) = 16 * 2 ^ (4 * n) := by rw [Nat.mul_succ, Nat.pow_add]; ring
    show ilR v n + nib v n * 2 ^ (4 * n) < _
    rw [e]
    have : nib v n * 2 ^ (4 * n) ≤ 15 * 2 ^ (4 * n) := Nat.mul_le_mul_right _ hb
    omega

theorem testBit_ilR (v : Nat → Nat) :
    ∀ n i, (ilR v n).testBit i = (decide (i / 4 < n) && (v (i % 4)).testBit (i / 4))
  | 0, i => by simp [ilR]
  | n + 1, i => by
    show (ilR v n + nib v n * 2 ^ (4 * n)).testBit i = _
    rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (ilR_lt v n), testBit_nib]
    by_cases hi : i < 4 * n
    · rw [if_pos hi, testBit_ilR v n i]
      simp [show i / 4 < n by omega, show i / 4 < n + 1 by omega]
    · rw [if_neg hi]
      by_cases h4 : i - 4 * n < 4
      · have e1 : (i - 4 * n) % 4 = i % 4 := by omega
        have e2 : i / 4 = n := by omega
        simp [h4, e1, e2]
      · simp [h4, show ¬ (i / 4 < n + 1) by omega]

/-- Bit `i` of `il v` is bit `i / 4` of slot `i % 4` (for `i < 256`). -/
theorem testBit_il (v : Nat → Nat) (i : Nat) :
    (il v).testBit i = (decide (i < 256) && (v (i % 4)).testBit (i / 4)) := by
  rw [il_eq_ilR, testBit_ilR]
  have : (i / 4 < 64) = (i < 256) := by apply propext; omega
  simp only [this]

theorem il_lt (v : Nat → Nat) : il v < 2 ^ 256 := by
  rw [il_eq_ilR]; exact ilR_lt v 64

theorem il_ext {a b : Nat → Nat} (h : ∀ k, k < 4 → ∀ j, j < 64 → (a k).testBit j = (b k).testBit j) :
    il a = il b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_il, testBit_il]
  by_cases hi : i < 256
  · rw [h (i % 4) (by omega) (i / 4) (by omega)]
  · simp [hi]

theorem il_congr {a b : Nat → Nat} (h : ∀ k, k < 4 → a k = b k) : il a = il b :=
  il_ext fun k hk j _ => by rw [h k hk]

theorem il_mod (a : Nat → Nat) : il a = il fun k => a k % 2 ^ 64 :=
  il_ext fun k _ j hj => by rw [Nat.testBit_mod_two_pow]; simp [hj]

theorem il_xor (a b : Nat → Nat) : il a ^^^ il b = il fun k => a k ^^^ b k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_il, testBit_il, testBit_il, Nat.testBit_xor]
  cases decide (i < 256) <;> simp

theorem il_and (a b : Nat → Nat) : il a &&& il b = il fun k => a k &&& b k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, testBit_il, testBit_il, testBit_il, Nat.testBit_and]
  cases decide (i < 256) <;> simp

theorem il_or (a b : Nat → Nat) : il a ||| il b = il fun k => a k ||| b k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, testBit_il, testBit_il, testBit_il, Nat.testBit_or]
  cases decide (i < 256) <;> simp

theorem spread_zero : spread 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [testBit_spread]; simp

theorem il_zero : il (fun _ => 0) = 0 := by
  unfold il; rw [spread_zero]

/-- Multiplying a spread lane by a slot mask `c < 16` copies it into the slots of `c`. -/
theorem spread_mul (v : Nat) {c : Nat} (hc : c < 16) :
    spread v * c = il fun k => if c.testBit k then v else 0 := by
  unfold il
  interval_cases c <;> simp [spread_zero, Nat.testBit] <;> ring

theorem spread_mul_two_pow (v : Nat) {sh : Nat} (hsh : sh < 4) :
    spread v * 2 ^ sh = il fun k => if k = sh then v else 0 := by
  unfold il
  interval_cases sh <;> simp [spread_zero] <;> ring

/-- `cext`'s extraction: slot `sh` of an interleaved word, de-interleaved. -/
theorem compress_il (v : Nat → Nat) {sh : Nat} (hsh : sh < 4) :
    compress (il v / 2 ^ sh &&& spread M64) = v sh % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_compress, Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_div_two_pow,
    testBit_il, testBit_spread]
  by_cases hi : i < 64
  · have e1 : (4 * i + sh) % 4 = sh := by omega
    have e2 : (4 * i + sh) / 4 = i := by omega
    have e3 : (4 * i) / 4 = i := by omega
    have hM : M64.testBit i = true := by
      unfold M64; rw [Nat.testBit_two_pow_sub_one]; simp [hi]
    simp [hi, e1, e2, e3, hM, show 4 * i + sh < 256 by omega, show 4 * i < 256 by omega]
  · simp [hi]

/-- Complementing a lane is xor with `M64`. -/
theorem sub_eq_xor_M64 {v : Nat} (hv : v < 2 ^ 64) : 2 ^ 64 - 1 - v = v ^^^ M64 := by
  apply Nat.eq_of_testBit_eq; intro i
  have key : ∀ x : BitVec 64, ~~~x = x ^^^ BitVec.allOnes 64 := fun x => BitVec.xor_allOnes.symm
  have h1 : (~~~(BitVec.ofNat 64 v)).toNat = 2 ^ 64 - 1 - v := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have h2 : ((BitVec.ofNat 64 v) ^^^ BitVec.allOnes 64).toNat = v ^^^ M64 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, BitVec.toNat_allOnes]; rfl
  rw [← h1, ← h2, key]

theorem cpl_eq {x v : Nat} (hv : v < 2 ^ 64) :
    cpl x v = if x ∈ complemented then v ^^^ M64 else v := by
  unfold cpl; split
  · exact sub_eq_xor_M64 hv
  · rfl

theorem xor_lt64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a ^^^ b < 2 ^ 64 :=
  Nat.xor_lt_two_pow ha hb

theorem M64_lt : M64 < 2 ^ 64 := by unfold M64; norm_num

theorem cpl_lt {x v : Nat} (hv : v < 2 ^ 64) : cpl x v < 2 ^ 64 := by
  unfold cpl; split <;> omega

end MlDsaOpt44.Proofs
