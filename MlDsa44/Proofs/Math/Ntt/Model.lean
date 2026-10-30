import MlDsa44.Spec.Fips204
/-!
# Closed-index models of Algorithms 41 and 42

`Fips204.ntt`/`nttInv` are `for` loops whose mutable state is a tuple
`(w, m, len)` (outer) and `(w, m, start)` (middle). Here they are restated as
recursions indexed by the layer `L` and the block `b`, with `m`, `len` and
`start` given in closed form, which is the shape the bytecode loop invariants
use:

* `nttL f L`: after `L` layers of Algorithm 41 (`len = 128 / 2^L`, `m = 2^L - 1`);
* `nttIL f L`: after `L` layers of Algorithm 42 (`len = 2^L`, `m = 2^(8-L)`);
* `scaleI w k`: the first `k` steps of the final scaling loop.
-/

namespace MlDsa44.Proofs.NttModel

open MlDsa44.Fips204

/-- One butterfly of Algorithm 41 at indices `a`, `a + len`. -/
def bfN (len : Nat) (z : Int) (w : Poly) (a : Nat) : Poly :=
  (w.set! (a + len) ((w[a]! - z * w[a + len]! % q) % q)).set! a
    (((w.set! (a + len) ((w[a]! - z * w[a + len]! % q) % q))[a]! + z * w[a + len]! % q) % q)

/-- `k` butterflies of one block starting at `st`. -/
def blockN (len : Nat) (z : Int) (w : Poly) (st k : Nat) : Poly :=
  (List.range' st k).foldl (bfN len z) w

/-- The first `b` blocks of a layer with block length `len`, `m = m0` before. -/
def layerN (len m0 : Nat) (w : Poly) : Nat → Poly
  | 0 => w
  | b + 1 => blockN len (zetas (m0 + b + 1)) (layerN len m0 w b) (2 * len * b) len

/-- The first `L` layers of Algorithm 41. -/
def nttL (w : Poly) : Nat → Poly
  | 0 => w
  | L + 1 => layerN (128 / 2 ^ L) (2 ^ L - 1) (nttL w L) (2 ^ L)

/-- One butterfly of Algorithm 42 at indices `a`, `a + len`. -/
def bfI (len : Nat) (z : Int) (w : Poly) (a : Nat) : Poly :=
  ((w.set! a ((w[a]! + w[a + len]!) % q)).set! (a + len)
        ((w[a]! - (w.set! a ((w[a]! + w[a + len]!) % q))[a + len]!) % q)).set! (a + len)
    (z * ((w.set! a ((w[a]! + w[a + len]!) % q)).set! (a + len)
        ((w[a]! - (w.set! a ((w[a]! + w[a + len]!) % q))[a + len]!) % q))[a + len]! % q)

def blockI (len : Nat) (z : Int) (w : Poly) (st k : Nat) : Poly :=
  (List.range' st k).foldl (bfI len z) w

def layerI (len m0 : Nat) (w : Poly) : Nat → Poly
  | 0 => w
  | b + 1 => blockI len (-zetas (m0 - b - 1)) (layerI len m0 w b) (2 * len * b) len

/-- The first `L` layers of Algorithm 42. -/
def nttIL (w : Poly) : Nat → Poly
  | 0 => w
  | L + 1 => layerI (2 ^ L) (2 ^ (8 - L)) (nttIL w L) (128 / 2 ^ L)

/-- One step of the final scaling loop. -/
def scStep (w : Poly) (j : Nat) : Poly := w.set! j (8347681 * w[j]! % q)

def scaleI (w : Poly) (k : Nat) : Poly := (List.range' 0 k).foldl scStep w

/-! ## Folding the spec's tuple state into the closed-index models -/

theorem foldl_midN (len m : Nat) (w : Poly) (F : Poly × Nat × Nat → Nat → Poly × Nat × Nat)
    (hF : ∀ x i, F x i = (blockN len (zetas (x.2.1 + 1)) x.1 x.2.2 len, x.2.1 + 1, x.2.2 + 2 * len)) :
    ∀ n, (List.range' 0 n).foldl F (w, m, 0) = (layerN len m w n, m + n, 2 * len * n)
  | 0 => rfl
  | n + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_midN len m w F hF n]
    simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil, hF, layerN, Prod.mk.injEq]
    and_intros <;> first | trivial | omega | rw [Nat.mul_succ]

theorem foldl_outN (w : Poly) (F : Poly × Nat × Nat → Nat → Poly × Nat × Nat)
    (hF : ∀ x i, F x i = (layerN x.2.2 x.2.1 x.1 (128 / x.2.2), x.2.1 + 128 / x.2.2, x.2.2 / 2)) :
    ∀ n, n ≤ 8 → (List.range' 0 n).foldl F (w, 0, 128) = (nttL w n, 2 ^ n - 1, 128 / 2 ^ n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [List.range'_concat, List.foldl_append, foldl_outN w F hF n (by omega)]
    simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil, hF, nttL, Prod.mk.injEq]
    have h128 : 128 / (128 / 2 ^ n) = 2 ^ n := by
      have key : ∀ n < 8, 128 / (128 / 2 ^ n) = 2 ^ n := by decide
      exact key n (by omega)
    refine ⟨by rw [h128], ?_, ?_⟩
    · rw [h128, Nat.pow_succ]; have := Nat.one_le_two_pow (n := n); omega
    · rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

set_option maxRecDepth 100000 in
theorem ntt_eq (f : Poly) : ntt f = nttL f 8 := by
  unfold ntt
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, Std.Legacy.Range.size, map_pure, Nat.reduceSub, Nat.reduceAdd,
    Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
  rw [foldl_outN f _ (fun x i => ?_) 8 (Nat.le_refl 8)]
  · simp only [pure]
  · rw [foldl_midN x.2.2 x.2.1 x.1 _ (fun y k => ?_)]
    simp only [Nat.add_sub_cancel_left, blockN]
    rfl

theorem foldl_midI (len m : Nat) (w : Poly) (F : Poly × Nat × Nat → Nat → Poly × Nat × Nat)
    (hF : ∀ x i, F x i =
      (blockI len (-zetas (x.2.1 - 1)) x.1 x.2.2 len, x.2.1 - 1, x.2.2 + 2 * len)) :
    ∀ n, (List.range' 0 n).foldl F (w, m, 0) = (layerI len m w n, m - n, 2 * len * n)
  | 0 => rfl
  | n + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_midI len m w F hF n]
    simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil, hF, layerI, Prod.mk.injEq]
    and_intros <;> first | trivial | omega | rw [Nat.mul_succ]

theorem foldl_outI (w : Poly) (F : Poly × Nat × Nat → Nat → Poly × Nat × Nat)
    (hF : ∀ x i, F x i = (layerI x.2.2 x.2.1 x.1 (128 / x.2.2), x.2.1 - 128 / x.2.2, 2 * x.2.2)) :
    ∀ n, n ≤ 8 → (List.range' 0 n).foldl F (w, 256, 1) = (nttIL w n, 2 ^ (8 - n), 2 ^ n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [List.range'_concat, List.foldl_append, foldl_outI w F hF n (by omega)]
    simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil, hF, nttIL, Prod.mk.injEq]
    have key : ∀ n < 8, 2 ^ (8 - n) - 128 / 2 ^ n = 2 ^ (8 - (n + 1)) := by decide
    exact ⟨trivial, key n (by omega), by rw [Nat.pow_succ, Nat.mul_comm]⟩

set_option maxRecDepth 100000 in
theorem nttInv_eq (f : Poly) : nttInv f = scaleI (nttIL f 8) 256 := by
  unfold nttInv
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, Std.Legacy.Range.size, map_pure, Nat.reduceSub, Nat.reduceAdd,
    Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, pure_bind]
  rw [foldl_outI f _ (fun x i => ?_) 8 (Nat.le_refl 8)]
  · simp only [pure, scaleI]
    rfl
  · rw [foldl_midI x.2.2 x.2.1 x.1 _ (fun y k => ?_)]
    simp only [Nat.add_sub_cancel_left, blockI]
    rfl

end MlDsa44.Proofs.NttModel
