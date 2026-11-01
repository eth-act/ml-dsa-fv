import MlDsaOpt44.Fn.Hint.PackSpec
import MlDsaOpt44.Fn.Hint.Lanes
/-!
# `csum` (WP10): 16-bit cells of words

`cell x f = (x >>> 16 f) % 2^16`. Words are the sums of their cells, cells
add without carry when the cell sums stay below `2^16`, and cell `f` of the
word loaded at `A` is the big-endian 16-bit value at `A + 30 − 2 f`.
-/

namespace MlDsaOpt44.Proofs.CS

open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.PK

/-- 16-bit cell `f` of a word. -/
def cell (x f : Nat) : Nat := (x >>> (16 * f)) % 2 ^ 16

/-- Sum of 16 cells. -/
def ofCells (D : Nat → Nat) : Nat := ((List.range 16).map fun f => D f * 2 ^ (16 * f)).sum

theorem cell_lt (x f : Nat) : cell x f < 2 ^ 16 := Nat.mod_lt _ (by positivity)

theorem ofCells_testBit {D : Nat → Nat} (hD : ∀ f, f < 16 → D f < 2 ^ 16) (b : Nat) :
    (ofCells D).testBit b = (decide (b < 256) && (D (b / 16)).testBit (b % 16)) :=
  (digits_testBit 16 (by omega) D 16 hD).2 b

theorem ofCells_lt {D : Nat → Nat} (hD : ∀ f, f < 16 → D f < 2 ^ 16) : ofCells D < 2 ^ 256 :=
  (digits_testBit 16 (by omega) D 16 hD).1

/-- Cells of a cell sum. -/
theorem cell_ofCells {D : Nat → Nat} (hD : ∀ f, f < 16 → D f < 2 ^ 16) {g : Nat} (hg : g < 16) :
    cell (ofCells D) g = D g := by
  apply eq_of_testBit_lt (n := 16) (cell_lt _ _) (hD g hg)
  intro e he
  unfold cell
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, ofCells_testBit hD, decide_eq_true he,
    decide_eq_true (by omega), Bool.true_and, Bool.true_and,
    show (16 * g + e) / 16 = g by omega, show (16 * g + e) % 16 = e by omega]

/-- A word is the sum of its cells. -/
theorem ofCells_cell {x : Nat} (hx : x < 2 ^ 256) : ofCells (cell x) = x := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [ofCells_testBit (fun f _ => cell_lt x f)]
  unfold cell
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < 256
  · rw [decide_eq_true hb, decide_eq_true (Nat.mod_lt _ (by omega)), Bool.true_and, Bool.true_and,
      show 16 * (b / 16) + b % 16 = b by omega]
  · rw [decide_eq_false hb, Bool.false_and,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem ofCells_add (D E : Nat → Nat) : ofCells D + ofCells E = ofCells fun f => D f + E f := by
  unfold ofCells
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  ring

/-- Cells add without carry. -/
theorem cell_add {x y : Nat} (hx : x < 2 ^ 256) (hy : y < 2 ^ 256)
    (h : ∀ f, f < 16 → cell x f + cell y f < 2 ^ 16) :
    x + y < 2 ^ 256 ∧ ∀ f, f < 16 → cell (x + y) f = cell x f + cell y f := by
  have e : x + y = ofCells fun f => cell x f + cell y f := by
    rw [← ofCells_add, ofCells_cell hx, ofCells_cell hy]
  rw [e]
  exact ⟨ofCells_lt h, fun f hf => cell_ofCells h hf⟩

/-! ## Cells of a loaded word -/

theorem beNat_two (m : ByteArray) (a n : Nat) :
    beNat m a (2 * n + 2) = beNat m a (2 * n) * 2 ^ 16 + be16 m (a + 2 * n) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  simp only [beNat, be16]
  have : a + (2 * n + 1) = a + 2 * n + 1 := by omega
  rw [this]; ring

theorem be16_lt (m : ByteArray) (a : Nat) : be16 m a < 2 ^ 16 := by
  unfold be16; have := byteAt_lt m a; have := byteAt_lt m (a + 1); omega

theorem beNat_cell (m : ByteArray) (a : Nat) :
    ∀ n f, f < n → cell (beNat m a (2 * n)) f = be16 m (a + 2 * n - 2 - 2 * f)
  | 0, f, h => by omega
  | n + 1, f, h => by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, beNat_two]
    unfold cell
    rcases f with _ | f
    · simp only [Nat.mul_zero, Nat.shiftRight_zero]
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (be16_lt _ _)]
      congr 1
    · have ih := beNat_cell m a n f (by omega)
      unfold cell at ih
      rw [show 16 * (f + 1) = 16 + 16 * f by ring, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow (beNat m a (2 * n) * 2 ^ 16 + be16 m (a + 2 * n)),
        Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (be16_lt _ _), Nat.add_zero,
        ← Nat.shiftRight_eq_div_pow, ih]
      congr 1
      all_goals omega

/-- Cell `f` of the word at `A` is the 16-bit big-endian value at `A + 30 − 2f`. -/
theorem cell_word (m : ByteArray) (A : Nat) {f : Nat} (hf : f < 16) :
    cell (word m A) f = be16 m (A + 30 - 2 * f) := by
  rw [word_eq_beNat, show (32 : Nat) = 2 * 16 by rfl, beNat_cell m A 16 f hf,
    show A + 2 * 16 - 2 - 2 * f = A + 30 - 2 * f by omega]

end MlDsaOpt44.Proofs.CS
