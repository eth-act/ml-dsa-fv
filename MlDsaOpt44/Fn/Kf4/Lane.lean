import MlDsaOpt44.Fn.Kf4.Il
/-!
# One slot: lane complementing and the spec round

Per-slot (`UInt64`) facts used by the generated `Kf4/Slot.lean`:

* `msk b` is the all-ones lane if `b`, else `0`; `cplU x v = v ^^^ msk (cplb x)`
  is the stored form of lane `x` (`Layout.cpl`);
* masks float out of the theta/rho/pi pieces (`colC_msk`, `dL_msk`, …);
* without masks the pieces are the spec's (`colC_eq`, `dL_eq`, …), written with
  `colS`, `dS`, `bS`, `chiS` in the operand order of `Keccak.round`.
-/

namespace MlDsaOpt44.Proofs.Kf4

open EvmSemantics
open EvmSemantics.Crypto.Keccak

/-- The all-ones lane if `b`. -/
def msk : Bool → UInt64
  | true => ~~~0
  | false => 0

/-- Lane `x` is stored complemented (`Layout.complemented`). -/
def cplb (x : Nat) : Bool := x == 1 || x == 2 || x == 8 || x == 12 || x == 17 || x == 20

/-- The stored form of lane `x`. -/
def cplU (x : Nat) (v : UInt64) : UInt64 := v ^^^ msk (cplb x)

theorem ones_eq : (0xffffffffffffffff : UInt64) = ~~~0 := by decide

theorem xor_ones (v : UInt64) : v ^^^ ~~~0 = ~~~v := by
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_not, UInt64.toBitVec_zero]
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_not, BitVec.getElem_zero]
  cases v.toBitVec[i] <;> rfl

theorem toNat_cplU (x : Nat) (v : UInt64) : (cplU x v).toNat = cpl x v.toNat := by
  unfold cplU cpl
  have hb : cplb x = decide (x ∈ complemented) := by
    simp only [cplb, complemented, List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> by_cases h8 : x = 8 <;>
      by_cases h12 : x = 12 <;> by_cases h17 : x = 17 <;> by_cases h20 : x = 20 <;>
      simp [h1, h2, h8, h12, h17, h20]
  rw [hb]
  by_cases h : x ∈ complemented
  · simp only [h, decide_true, msk, if_true, xor_ones, UInt64.toNat_not, UInt64.size]; rfl
  · simp only [h, decide_false, msk, if_false]
    rw [show (0 : UInt64) = 0 from rfl]
    simp

theorem xor_msk (a b : UInt64) (p q : Bool) :
    (a ^^^ msk p) ^^^ (b ^^^ msk q) = (a ^^^ b) ^^^ msk (p ^^ q) := by
  apply UInt64.toBitVec_inj.mp
  cases p <;> cases q <;>
  · simp only [msk, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      UInt64.toBitVec_xor, UInt64.toBitVec_not, UInt64.toBitVec_zero]
    ext i hi
    simp only [BitVec.getElem_xor, BitVec.getElem_not, BitVec.getElem_zero]
    cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> rfl

theorem rotl_not (a : UInt64) {n : Nat} (h0 : 0 < n) (h64 : n < 64) :
    rotl64 (~~~a) n = ~~~(rotl64 a n) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_rotl64 _ h0 h64, UInt64.toNat_not, UInt64.toNat_not, toNat_rotl64 _ h0 h64]
  have ha := a.toNat_lt
  simp only [UInt64.size] at ha ⊢
  have hX : a.toNat <<< n % 2 ^ 64 ||| a.toNat >>> (64 - n) < 2 ^ 64 :=
    Nat.or_lt_two_pow (Nat.mod_lt _ (by decide))
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by simpa using ha))
  rw [show 18446744073709551616 - 1 - a.toNat = 2 ^ 64 - (a.toNat + 1) by omega,
    show 18446744073709551616 - 1 - (a.toNat <<< n % 2 ^ 64 ||| a.toNat >>> (64 - n)) =
      2 ^ 64 - ((a.toNat <<< n % 2 ^ 64 ||| a.toNat >>> (64 - n)) + 1) by simp only [Nat.reducePow] at hX ⊢; omega]
  have ha' : a.toNat < 2 ^ 64 := by simpa using ha
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_two_pow_sub_succ hX, Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight]
  simp only [Nat.testBit_two_pow_sub_succ ha']
  have hhi : n ≤ j → a.toNat.testBit (64 - n + j) = false := fun h =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by omega) (by omega)))
  by_cases hj : j < 64
  · by_cases hn : j ≥ n
    · simp [hj, hn, hhi hn, show j - n < 64 by omega, show ¬ (64 - n + j < 64) by omega]
    · simp [hj, hn, show 64 - n + j < 64 by omega]
  · simp [hj, hhi (by omega), show ¬ (64 - n + j < 64) by omega]

theorem rotl_msk (a : UInt64) (p : Bool) {n : Nat} (h0 : 0 < n) (h64 : n < 64) :
    rotl64 (a ^^^ msk p) n = rotl64 a n ^^^ msk p := by
  cases p
  · simp only [msk]
    rw [show (0 : UInt64) = 0 from rfl]
    simp
  · simp only [msk, xor_ones, rotl_not _ h0 h64]

/-! ## Masks float out of the pieces -/

theorem colC_msk (a0 a1 a2 a3 a4 : UInt64) (p0 p1 p2 p3 p4 : Bool) :
    colC Ops64 (a0 ^^^ msk p0) (a1 ^^^ msk p1) (a2 ^^^ msk p2) (a3 ^^^ msk p3) (a4 ^^^ msk p4) =
      colC Ops64 a0 a1 a2 a3 a4 ^^^ msk (p4 ^^ (p3 ^^ (p2 ^^ (p1 ^^ p0)))) := by
  simp only [colC, Ops64_xor, xor_msk]

theorem dL_msk (p q : UInt64) (m n : Bool) :
    dL Ops64 (p ^^^ msk m) (q ^^^ msk n) = dL Ops64 p q ^^^ msk (n ^^ m) := by
  simp only [dL, Ops64_xor, Ops64_rot, rotl_msk _ _ (show 0 < 1 by omega) (show 1 < 64 by omega),
    xor_msk]

theorem dR_msk (p q : UInt64) (m n : Bool) :
    dR Ops64 (p ^^^ msk m) (q ^^^ msk n) = dR Ops64 p q ^^^ msk (m ^^ n) := by
  simp only [dR, Ops64_xor, Ops64_rot, rotl_msk _ _ (show 0 < 1 by omega) (show 1 < 64 by omega),
    xor_msk]

theorem bv_msk (d a : UInt64) (q p : Bool) {r : Nat} (h0 : 0 < r) (h64 : r < 64) :
    bv Ops64 (d ^^^ msk q) (a ^^^ msk p) r = bv Ops64 d a r ^^^ msk (q ^^ p) := by
  simp only [bv, Ops64_xor, Ops64_rot, xor_msk, rotl_msk _ _ h0 h64]

theorem bv0_msk (d a : UInt64) (q p : Bool) :
    bv0 Ops64 (d ^^^ msk q) (a ^^^ msk p) = bv0 Ops64 d a ^^^ msk (q ^^ p) := by
  simp only [bv0, Ops64_xor, xor_msk]

/-! ## The pieces in the spec's operand order -/

/-- `Keccak.round`'s chi. -/
def chiS (b0 b1 b2 : UInt64) : UInt64 := b0 ^^^ ((b1 ^^^ 0xffffffffffffffff) &&& b2)

def colS (a0 a1 a2 a3 a4 : UInt64) : UInt64 := a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4

def dS (p q : UInt64) : UInt64 := p ^^^ rotl64 q 1

def bS (a d : UInt64) (r : Nat) : UInt64 := rotl64 (a ^^^ d) r

theorem colC_eq (a0 a1 a2 a3 a4 : UInt64) : colC Ops64 a0 a1 a2 a3 a4 = colS a0 a1 a2 a3 a4 := by
  simp only [colC, colS, Ops64_xor]; ac_rfl

theorem dL_eq (p q : UInt64) : dL Ops64 p q = dS p q := by
  simp only [dL, dS, Ops64_xor, Ops64_rot]; exact UInt64.xor_comm _ _

theorem dR_eq (p q : UInt64) : dR Ops64 p q = dS p q := by
  simp only [dR, dS, Ops64_xor, Ops64_rot]

theorem bv_eq (d a : UInt64) (r : Nat) : bv Ops64 d a r = bS a d r := by
  simp only [bv, bS, Ops64_xor, Ops64_rot]; rw [UInt64.xor_comm]

theorem bv0_eq (d a : UInt64) : bv0 Ops64 d a = bS a d 0 := by
  simp only [bv0, bS, Ops64_xor, rotl64, if_true]; exact UInt64.xor_comm _ _

/-! ## `Keccak.round` lane by lane -/

theorem arr25 {A : Array UInt64} (h : A.size = 25) :
    A = #[A[0]!, A[1]!, A[2]!, A[3]!, A[4]!, A[5]!, A[6]!, A[7]!, A[8]!, A[9]!, A[10]!, A[11]!,
      A[12]!, A[13]!, A[14]!, A[15]!, A[16]!, A[17]!, A[18]!, A[19]!, A[20]!, A[21]!, A[22]!,
      A[23]!, A[24]!] := by
  rcases A with ⟨l⟩
  simp only [List.size_toArray] at h
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
      x20, x21, x22, x23, x24], _ => rfl

theorem round_size (A : Array UInt64) (rc : UInt64) : (round A rc).size = 25 := by
  simp only [round, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, bind_pure_comp, List.range', List.foldl,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceSub, Nat.reduceDiv,
    Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate, map_pure]

end MlDsaOpt44.Proofs.Kf4
