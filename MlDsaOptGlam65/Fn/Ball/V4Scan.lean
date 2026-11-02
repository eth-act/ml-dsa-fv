import MlDsaOptGlam65.Fn.Ball.V4Proof
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Ball/V4Scan.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (v4, ML-DSA-65): one stream position

A position `p` (`8 ≤ p < 272`, byte `p` of the stream) is the loop head when
`p ≡ 0 (mod 8)` and the test of byte `p mod 8` of the lane otherwise
(`posSt`). `byte_rej`, `byte_acc` and `acc_back` move from position `p` to
`p + 1` for a rejected byte, and into and out of the shared accept step. -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Ball4

open MlDsaOpt65.Proofs

/-- Cost of a rejected byte at lane offset `r`. -/
def rc (r : Nat) : Nat := if r = 0 then 66 else if r = 7 then 62 else 40

/-- Cost of the rejected bytes `p … 271`. -/
def rs (p : Nat) : Nat := ((List.range (272 - p)).map fun d => rc ((p + d) % 8)).sum

theorem rs_succ {p : Nat} (hp : p < 272) : rs p = rc (p % 8) + rs (p + 1) := by
  unfold rs
  rw [show 272 - p = (272 - (p + 1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, List.map_map, Nat.add_zero]
  congr 2
  apply List.map_congr_left
  intro d _
  simp only [Function.comp]
  congr 2; omega

theorem rs_8 : rs 8 = 12144 := by decide +kernel

/-- The sign word after `i − 207` accepted bytes. -/
abbrev sgw (bs : ByteArray) (i : Nat) : Nat := le64 bs 0 / 2 ^ (i - 207)

/-- The state at stream position `p`. -/
def posSt (s : State) (ret : Nat) (tail : List UInt256) (bs : ByteArray) (p i z : Nat) (M : ByteArray) :
    State :=
  if p % 8 = 0 then headSt s ret tail (4 * p) i (sgw bs i) M
  else skipSt s ret tail (p % 8) z (le64 bs (p - p % 8)) (4 * (p - p % 8)) i (sgw bs i) M

theorem le64_lt8 (b : ByteArray) (a : Nat) : le64 b a < 2 ^ 256 :=
  Nat.lt_trans (le64_lt b a) (by norm_num)

/-- Byte `r` of the lane word is the stream byte. -/
theorem lane_byte (bs : ByteArray) {p r : Nat} (hr : r = p % 8) :
    255 &&& le64 bs (p - r) / 2 ^ (8 * r) = bs[p]!.toNat := by
  rw [Nat.and_comm, show ∀ x : Nat, x &&& 255 = x % 256 from fun x => Nat.and_two_pow_sub_one_eq_mod x 8,
    le64_byte _ _ _ (by omega), show p - r + r = p by omega, byteAt_eq_get]

theorem sgw_succ (bs : ByteArray) {i : Nat} (hi : 207 ≤ i) : sgw bs i / 2 = sgw bs (i + 1) := by
  unfold sgw
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, show (i - 207).succ = i + 1 - 207 by omega]

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem byte_rej (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat)
    (bs M : ByteArray) {p i z : Nat} (hp : p < 272)
    (hw : p % 8 = 0 → word M (88064 + 4 * p) = le64 bs p)
    (hji : i < bs[p]!.toNat) (hi : i < 256) :
    Reach (posSt s ret tail bs p i z M) (posSt s ret tail bs (p + 1) i bs[p]!.toNat M) (rc (p % 8)) := by
  have hj' : bs[p]!.toNat < 256 := UInt8.toNat_lt _
  have hb := lane_byte bs (p := p) rfl
  unfold posSt
  have h8 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨
    p % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hb ⊢ <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.sub_zero, Nat.div_one] at hb
  · rw [if_pos rfl, if_neg (by omega), show (p + 1) % 8 = 1 by omega, show p + 1 - 1 = p by omega]
    exact b_head_rej hs htail hsized M (4 * p) i _ _ _ (by omega) (by omega) (hw h) hb
      hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 2 by omega,
      show p + 1 - 2 = p - 1 by omega]
    exact b_skip_rej1 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 3 by omega,
      show p + 1 - 3 = p - 2 by omega]
    exact b_skip_rej2 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 4 by omega,
      show p + 1 - 4 = p - 3 by omega]
    exact b_skip_rej3 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 5 by omega,
      show p + 1 - 5 = p - 4 by omega]
    exact b_skip_rej4 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 6 by omega,
      show p + 1 - 6 = p - 5 by omega]
    exact b_skip_rej5 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 7 by omega,
      show p + 1 - 7 = p - 6 by omega]
    exact b_skip_rej6 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega), if_pos (by omega)]
    have h' := b_skip_rej7 (ret := ret) hs htail hsized M z _ (4 * (p - 7)) i (sgw bs i) _ (le64_lt8 _ _) hb hji hj' hi
    rw [show 32 + 4 * (p - 7) = 4 * (p + 1) by omega] at h'
    exact h'

/-- The return label of the accept step for lane offset `r`. -/
abbrev rlOf (r : Nat) : Nat := 7379 + 24 * r

/-- Cost of an accepted byte's test. -/
def acost (r : Nat) : Nat := if r = 0 then 83 else 57

theorem byte_acc (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat)
    (bs M : ByteArray) {p i z : Nat} (hp : p < 272)
    (hw : p % 8 = 0 → word M (88064 + 4 * p) = le64 bs p)
    (hji : bs[p]!.toNat ≤ i) (hi : i < 256) :
    Reach (posSt s ret tail bs p i z M)
      (accSt s ret tail bs[p]!.toNat (rlOf (p % 8)) (le64 bs (p - p % 8)) (4 * (p - p % 8)) i (sgw bs i) M)
      (acost (p % 8)) := by
  have hj' : bs[p]!.toNat < 256 := UInt8.toNat_lt _
  have hb := lane_byte bs (p := p) rfl
  unfold posSt
  have h8 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨
    p % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hb ⊢ <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.sub_zero, Nat.div_one] at hb
  · rw [if_pos rfl]
    exact b_head_acc hs htail hsized M (4 * p) i _ _ _ (by omega) (by omega) (hw h) hb
      hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc1 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc2 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc3 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc4 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc5 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc6 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc7 hs htail hsized M z _ _ i _ _ (le64_lt8 _ _) hb hji hj' hi

/-- Back from the accept step to position `p + 1`. -/
theorem acc_back (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat)
    (bs M : ByteArray) {p i : Nat} (hp : p < 272) :
    Reach (callState s (rlOf (p % 8)) (wd (rlOf (p % 8)) :: wd (le64 bs (p - p % 8)) ::
        wd (4 * (p - p % 8)) :: wd (i + 1) :: wd (sgw bs (i + 1)) :: wd ret :: tail) M)
      (posSt s ret tail bs (p + 1) (i + 1) (rlOf (p % 8)) M) (if p % 8 = 7 then 22 else 0) := by
  unfold posSt
  by_cases h7 : p % 8 = 7
  · rw [if_pos h7, if_pos (by omega), h7]
    have h := b_tail8 (ret := ret) hs htail hsized M (rlOf 7) (le64 bs (p - 7)) (4 * (p - 7)) (i + 1) (sgw bs (i + 1))
    rw [show 32 + 4 * (p - 7) = 4 * (p + 1) by omega] at h
    exact h
  · rw [if_neg h7, if_neg (by omega), show (p + 1) % 8 = p % 8 + 1 by omega,
      show p + 1 - (p % 8 + 1) = p - p % 8 by omega]
    refine (Reach.refl _).of_eq rfl ?_
    simp only [skipSt, skipPc, rlOf, Nat.add_sub_cancel]

end

end Ball4

end MlDsaOptGlam65.Proofs
