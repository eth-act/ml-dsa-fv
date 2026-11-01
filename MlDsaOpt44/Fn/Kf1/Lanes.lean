import MlDsaOpt44.Fn.Kf1.Win
/-!
# `kf1`: the lane mirror computes the lane-complemented Keccak round

`roundL` (the code's round on 64-bit lanes, `Model.lean`) applied to the
stored lanes `cplU i (v i)` gives the stored form `cplU j` of output lane `j`
of `Os v rc`, a closed form of `Crypto.Keccak.round` (`Spec.lean` proves
`(round A rc)[j]! = Os …`).

Complementing is xor with a mask `mk b` (`b = j ∈ complemented`); masks pass
through theta and rho unchanged (`rotl64 (mk b) n = mk b`), so the `B` lanes of
the code are the spec's `Bs` up to a mask (`BL_cpl`), and chi with complemented
inputs is a three-variable bit identity per output lane (`chi_masks`).
-/

namespace MlDsaOpt44.Proofs.Kf1

open EvmSemantics
open EvmSemantics.Crypto.Keccak

set_option linter.unusedSimpArgs false

/-- Lane `j` as stored (`complemented` lanes inverted). -/
def cplU (j : Nat) (w : UInt64) : UInt64 := if j ∈ complemented then ~~~w else w

/-! ## Closed form of a Keccak round -/

def Cs (v : Nat → UInt64) (x : Nat) : UInt64 := v x ^^^ v (x + 5) ^^^ v (x + 10) ^^^ v (x + 15) ^^^ v (x + 20)

def Ds (v : Nat → UInt64) (x : Nat) : UInt64 := Cs v ((x + 4) % 5) ^^^ rotl64 (Cs v ((x + 1) % 5)) 1

/-- `B'[π(j)]`: theta then rho of lane `j`. -/
def Bs (v : Nat → UInt64) (j : Nat) : UInt64 := rotl64 (v j ^^^ Ds v (j % 5)) rotOff[j]!

/-- Chi (and iota on lane 0) of output lane `j`. -/
def Os (v : Nat → UInt64) (rc : UInt64) (j : Nat) : UInt64 :=
  if j = 0 then
    Bs v (srcLane 0 0) ^^^ ((Bs v (srcLane 0 1) ^^^ 0xffffffffffffffff) &&& Bs v (srcLane 0 2)) ^^^ rc
  else
    Bs v (srcLane (j / 5) (j % 5)) ^^^
      ((Bs v (srcLane (j / 5) ((j % 5 + 1) % 5)) ^^^ 0xffffffffffffffff) &&&
        Bs v (srcLane (j / 5) ((j % 5 + 2) % 5)))

/-! ## Masks -/

/-- All-ones or zero. -/
def mk (b : Bool) : UInt64 := if b then 0xffffffffffffffff else 0

/-- Lane `j` is stored complemented. -/
def cb (j : Nat) : Bool := decide (j ∈ complemented)

theorem mk_xor (a b : Bool) : mk (a ^^ b) = mk a ^^^ mk b := by
  cases a <;> cases b <;> rfl

theorem testBit_hi (a : UInt64) {i : Nat} (hi : ¬ i < 64) : a.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega)))

theorem testBit_not (a : UInt64) (i : Nat) :
    (~~~a).toNat.testBit i = (decide (i < 64) && !a.toNat.testBit i) := by
  rw [UInt64.toNat_not, show UInt64.size - 1 - a.toNat = 2 ^ 64 - (a.toNat + 1) by
    have := a.toNat_lt; simp only [UInt64.size]; omega, Nat.testBit_two_pow_sub_succ a.toNat_lt]

theorem testBit_ones (i : Nat) :
    (0xffffffffffffffff : UInt64).toNat.testBit i = decide (i < 64) := by
  rw [show (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem testBit_mk (b : Bool) (i : Nat) : (mk b).toNat.testBit i = (b && decide (i < 64)) := by
  cases b
  · simp [mk]
  · simp only [mk, if_true, testBit_ones, Bool.true_and]

theorem ext64 {a b : UInt64} (h : ∀ i, i < 64 → a.toNat.testBit i = b.toNat.testBit i) : a = b := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · exact h i hi
  · rw [testBit_hi a hi, testBit_hi b hi]

theorem not_eq_xor (w : UInt64) : ~~~w = w ^^^ mk true :=
  ext64 fun i hi => by
    simp only [testBit_not, UInt64.toNat_xor, Nat.testBit_xor, testBit_mk, hi, decide_true,
      Bool.true_and, Bool.xor_true]

theorem cplU_eq (j : Nat) (w : UInt64) : cplU j w = w ^^^ mk (cb j) := by
  unfold cplU cb
  split
  · rename_i h; simp only [h, decide_true]; exact not_eq_xor w
  · rename_i h; simp only [h, decide_false]
    exact (UInt64.xor_zero (a := w)).symm

theorem cplU_toNat (j : Nat) (w : UInt64) : (cplU j w).toNat = cpl j w.toNat := by
  unfold cplU cpl
  split
  · rw [UInt64.toNat_not]; rfl
  · rfl

theorem rotl64_xor (a b : UInt64) {n : Nat} (hn : n < 64) :
    rotl64 (a ^^^ b) n = rotl64 a n ^^^ rotl64 b n :=
  ext64 fun i hi => by
    rw [UInt64.toNat_xor, Nat.testBit_xor, rotl64_testBit _ hn hi, rotl64_testBit _ hn hi,
      rotl64_testBit _ hn hi, UInt64.toNat_xor, Nat.testBit_xor]

theorem rotl64_mk (b : Bool) {n : Nat} (hn : n < 64) : rotl64 (mk b) n = mk b :=
  ext64 fun i hi => by
    rw [rotl64_testBit _ hn hi, testBit_mk, testBit_mk]
    simp [hi, Nat.mod_lt _ (show 64 > 0 by decide)]

theorem xor_left_comm (a b c : UInt64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt64.xor_assoc, UInt64.xor_comm a b, UInt64.xor_assoc]

/-! ## Theta and rho with masks -/

/-- Mask of `C_x`. -/
def cm (x : Nat) : Bool := cb x ^^ cb (x + 5) ^^ cb (x + 10) ^^ cb (x + 15) ^^ cb (x + 20)

/-- Mask of `D_x`. -/
def dm (x : Nat) : Bool := cm ((x + 4) % 5) ^^ cm ((x + 1) % 5)

theorem CL_cpl (v : Nat → UInt64) (x : Nat) :
    CL (fun i => cplU i (v i)) x = Cs v x ^^^ mk (cm x) := by
  simp only [CL, Cs, cm, cplU_eq, mk_xor]
  simp only [UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm]

theorem DL_cpl (v : Nat → UInt64) {x : Nat} (hx : x < 5) :
    DL (CL fun i => cplU i (v i)) x = Ds v x ^^^ mk (dm x) := by
  interval_cases x <;>
  · simp only [DL, Ds, dm, CL_cpl, rotl64_xor _ _ (show 1 < 64 by decide), rotl64_mk _ (show 1 < 64 by decide), mk_xor,
      Nat.reduceAdd, Nat.reduceMod]
    simp only [UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm]

theorem rotOff_lt (j : Nat) : rotOff[j]! < 64 := by
  by_cases hj : j < 25
  · interval_cases j <;> decide
  · rw [getElem!_neg rotOff j (by rw [show rotOff.size = 25 from rfl]; omega)]; decide

theorem BL_cpl (v : Nat → UInt64) (j : Nat) :
    BL (fun i => cplU i (v i)) (DL (CL fun i => cplU i (v i))) j =
      Bs v j ^^^ mk (dm (j % 5) ^^ cb j) := by
  unfold BL
  rw [DL_cpl v (Nat.mod_lt j (show 5 > 0 by decide))]
  simp only [Bs, cplU_eq, rotl64_xor _ _ (rotOff_lt j), rotl64_mk _ (rotOff_lt j), mk_xor]
  simp only [UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm]

/-! ## Chi with masks -/

set_option maxHeartbeats 1000000 in
/-- Chi of the masked `B` lanes of row `j / 5` is the spec's chi, masked by `cb j`. -/
theorem chi_masks (a : Nat → UInt64) {j : Nat} (hj : j < 25) :
    chiL j (fun k => a k ^^^ mk (dm (srcLane (j / 5) k % 5) ^^ cb (srcLane (j / 5) k))) =
      (a (j % 5) ^^^ ((a ((j % 5 + 1) % 5) ^^^ 0xffffffffffffffff) &&& a ((j % 5 + 2) % 5))) ^^^
        mk (cb j) := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · interval_cases j <;>
    · simp (config := { decide := true }) only [chiL, srcLane, dm, cm, cb, complemented,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv, UInt64.toNat_xor,
        UInt64.toNat_and, UInt64.toNat_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or,
        testBit_not, testBit_mk, testBit_ones, hi, decide_true, Bool.true_and, Bool.and_true,
        Bool.xor_false, Bool.false_xor, Bool.true_xor, Bool.xor_true]
      cases (a 0).toNat.testBit i <;> cases (a 1).toNat.testBit i <;> cases (a 2).toNat.testBit i <;>
        cases (a 3).toNat.testBit i <;> cases (a 4).toNat.testBit i <;> rfl
  · interval_cases j <;>
    · simp only [chiL, UInt64.toNat_xor, UInt64.toNat_and, UInt64.toNat_or, Nat.testBit_xor,
        Nat.testBit_and, Nat.testBit_or, testBit_not, testBit_mk, testBit_ones, testBit_hi _ hi, hi,
        decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor, Bool.or_false]

/-! ## One round -/

theorem roundL_cpl (v : Nat → UInt64) (rc : UInt64) {j : Nat} (hj : j < 25) :
    roundL (fun i => cplU i (v i)) rc j = cplU j (Os v rc j) := by
  have hB : ∀ y, (fun k => BL (fun i => cplU i (v i)) (DL (CL fun i => cplU i (v i))) (srcLane y k)) =
      fun k => Bs v (srcLane y k) ^^^ mk (dm (srcLane y k % 5) ^^ cb (srcLane y k)) := fun y =>
    funext fun k => BL_cpl v (srcLane y k)
  unfold roundL outL Os
  rw [cplU_eq]
  by_cases h0 : j = 0
  · subst j
    rw [if_pos rfl, if_pos rfl, hB 0]
    have h := chi_masks (fun k => Bs v (srcLane 0 k)) (j := 0) (by decide)
    simp only [Nat.zero_div, Nat.zero_mod, Nat.zero_add, Nat.reduceAdd, Nat.reduceMod] at h
    rw [h]
    simp only [UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm]
  · rw [if_neg h0, if_neg h0, hB (j / 5), chi_masks _ hj]

end MlDsaOpt44.Proofs.Kf1
