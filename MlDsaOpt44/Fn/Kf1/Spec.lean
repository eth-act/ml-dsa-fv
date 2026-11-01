import MlDsaOpt44.Fn.Kf1.Lanes
/-!
# `kf1`: closed form of `Crypto.Keccak.round` and `permute` as 24 rounds
-/

namespace MlDsaOpt44.Proofs.Kf1

open EvmSemantics
open EvmSemantics.Crypto.Keccak

set_option linter.unusedSimpArgs false

/-- The first `n` Keccak rounds. -/
def rounds (A : Array UInt64) (n : Nat) : Array UInt64 :=
  (List.range n).foldl (fun A i => round A RC[i]!) A

theorem permute_eq (A : Array UInt64) : permute A = rounds A 24 := by
  simp only [permute, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, pure_bind, rounds, List.range_eq_range']

theorem rounds_two (A : Array UInt64) (k : Nat) :
    rounds A (2 * k + 2) = round (round (rounds A (2 * k)) RC[2 * k]!) RC[2 * k + 1]! := by
  simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem round_lit (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt64) (rc : UInt64) :
    round #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24] rc = #[Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 0, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 1, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 2, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 3, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 4, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 5, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 6, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 7, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 8, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 9, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 10, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 11, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 12, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 13, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 14, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 15, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 16, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 17, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 18, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 19, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 20, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 21, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 22, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 23, Os (fun i => #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24][i]!) rc 24] := by
  simp only [round, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, pure_bind, bind_pure_comp, Id.run_bind, List.range',
    List.foldl, Id.run_map, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceSub, Nat.reduceDiv,
    Array.replicate, List.replicate, Nat.add_zero, Nat.zero_add, map_pure, Array.set!_eq_setIfInBounds,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, List.getElem!_toArray,
    List.getElem!_cons_succ, List.getElem!_cons_zero, rotOff, List.forIn_cons, List.forIn_nil,
    Os, Bs, Ds, Cs, srcLane, ↓reduceIte, Nat.reduceEqDiff]

/-- Lane `j` of a round, in closed form. -/
theorem round_get (A : Array UInt64) (hA : A.size = 25) (rc : UInt64) {j : Nat} (hj : j < 25) :
    (round A rc)[j]! = Os (fun i => A[i]!) rc j := by
  rcases A with ⟨l⟩
  simp only [List.size_toArray] at hA
  match l, hA with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24], _ =>
    rw [round_lit]
    interval_cases j <;> rfl

theorem round_size (A : Array UInt64) (rc : UInt64) (hA : A.size = 25) : (round A rc).size = 25 := by
  rcases A with ⟨l⟩
  simp only [List.size_toArray] at hA
  match l, hA with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24], _ => rw [round_lit]; rfl

end MlDsaOpt44.Proofs.Kf1
