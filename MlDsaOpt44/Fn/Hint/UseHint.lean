import MlDsaOpt44.Fn.Hint.Lanes
import MlDsaOpt44.Budget
/-!
# `usehint` (WP10): loop body as a word function, lane semantics, `UseHint`

`uhW w s h` is the word the loop body stores, written with the `UInt256`
operations in exactly the shape `opt44_block` produces (so the block lemma's
residual closes by unfolding). `uhW_pack` evaluates it lane-wise on in-range
words, `uhLane_spec` identifies a lane with FIPS 204 `UseHint`.
-/

namespace MlDsaOpt44.Proofs.UH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.L10

/-! ## The stored word -/

def uhX (w s : Nat) : UInt256 :=
  UInt256.ofNat (6733405452027397254358290306971416642451224083449399316382630281344 + w) -
    UInt256.ofNat s

def uhQ (x : UInt256) : UInt256 :=
  (UInt256.ofNat 3207598986782593870493972684755717093467514342740420773020159).land
    ((UInt256.ofNat 1074791297 * x).shiftRight (UInt256.ofNat 53))

def uhR (x : UInt256) : UInt256 := x - UInt256.ofNat 8380417 * uhQ x

def uhR1 (r : UInt256) : UInt256 :=
  (UInt256.ofNat 395457409329360888143092522778102107413803138146079273386047).land
    ((UInt256.ofNat 2886403 *
      (UInt256.ofNat 597774675362608995853251492645737171287680740456972623552803839 + r)).shiftRight
      (UInt256.ofNat 39))

def uhPos (r : UInt256) : UInt256 :=
  (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969).land
    ((UInt256.ofNat 104714504438991106934412238609704954414940284379357872306006166527 +
      (UInt256.ofNat 597780952464344382534015668717527299892560324633768593065079808 + r -
        UInt256.ofNat 190464 * uhR1 r)).shiftRight (UInt256.ofNat 24))

def uhV (r : UInt256) (h : Nat) : UInt256 :=
  UInt256.ofNat 276192476357013953623747158765658614701703779022658540142636 - UInt256.ofNat h +
      ((UInt256.ofNat h).land (uhPos r)).shiftLeft (UInt256.ofNat 1) + uhR1 r

def uhF (v : UInt256) : UInt256 :=
  v - UInt256.ofNat 44 *
    (UInt256.ofNat 18831305206160042292528215370385814638752530387908536827907).land
      ((UInt256.ofNat 94 * v).shiftRight (UInt256.ofNat 12))

/-- The word stored for `W` (at `ACC`), `S` (at `SP`) and `H` (at `HP`). -/
def uhW (w s h : Nat) : UInt256 := uhF (uhV (uhR (uhX w s)) h)

/-! ## Lane functions -/

def lx (a b : Nat) : Nat := a + 1072693376 - b
def lr (x : Nat) : Nat := x - 8380417 * (1074791297 * x / 2 ^ 53 % 2 ^ 9)
def lr1 (r : Nat) : Nat := 2886403 * (95231 + r) / 2 ^ 39 % 2 ^ 6
def lpos (r : Nat) : Nat := (16681983 + (95232 + r - 190464 * lr1 r)) / 2 ^ 24 % 2 ^ 1
def lv (r c : Nat) : Nat := 44 - c + 2 ^ 1 * (c &&& lpos r) + lr1 r
def lf (v : Nat) : Nat := v - 44 * (94 * v / 2 ^ 12 % 2 ^ 2)

/-- One lane of `uhW`. -/
def uhLane (a b c : Nat) : Nat := lf (lv (lr (lx a b)) c)

theorem div_q {x : Nat} (hx : x < 2 ^ 31) : 1074791297 * x / 2 ^ 53 % 2 ^ 9 = x / 8380417 := by
  have h : 1074791297 * x / 2 ^ 53 = x / 8380417 := by omega
  rw [h]; omega

theorem div_g {y : Nat} (hy : y < 8380417 + 95231) : 2886403 * y / 2 ^ 39 % 2 ^ 6 = y / 190464 := by
  have h : 2886403 * y / 2 ^ 39 = y / 190464 := by omega
  rw [h]; omega

theorem lf_eq {v : Nat} (hv : v ≤ 89) : lf v = v % 44 := by
  unfold lf; interval_cases v <;> rfl

theorem lr_eq {x : Nat} (hx : x < 2 ^ 31) : lr x = x % 8380417 := by
  unfold lr; rw [div_q hx]; omega

theorem lr1_eq {r : Nat} (hr : r < 8380417) : lr1 r = (95231 + r) / 190464 := by
  unfold lr1; rw [div_g (by omega)]

theorem lpos_eq {r : Nat} (hr : r < 8380417) :
    lpos r = if 190464 * ((95231 + r) / 190464) < r then 1 else 0 := by
  unfold lpos; rw [lr1_eq hr]; split_ifs <;> omega

theorem lv_le {r c : Nat} (hr : r < 8380417) (hc : c ≤ 1) : lv r c ≤ 89 := by
  have h1 : c &&& lpos r ≤ c := Nat.and_le_left
  unfold lv; rw [lr1_eq hr]; omega

theorem useHint_lane (r c : Nat) (hr : r < 8380417) (hc : c ≤ 1) :
    (((44 - c + 2 * (c &&& (if 190464 * ((95231 + r) / 190464) < r then 1 else 0)) +
      (95231 + r) / 190464) % 44 : Nat) : Int) = Fips204.useHint c r := by
  have hq : ((r : Int) % (8380417 : Nat)) = r := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Fips204.useHint, Fips204.decompose, Fips204.modPm, Fips204.q, Fips204.gamma2, hq]
  norm_num
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 190464 ∧ r = 190464 * a + b :=
    ⟨r / 190464, r % 190464, Nat.mod_lt _ (by omega), (Nat.div_add_mod r 190464).symm⟩
  have ha : a ≤ 44 := by omega
  have e1 : (95231 + (190464 * a + b)) / 190464 = if b ≤ 95232 then a else a + 1 := by
    split_ifs <;> omega
  rw [e1]
  have e2 : ((190464 * a + b : Nat) : Int) % 190464 = b := by omega
  push_cast at e2 ⊢
  rw [e2]
  interval_cases c <;> by_cases hb2 : b ≤ 95232 <;> simp [hb2] <;> split_ifs <;> omega

/-- A lane of `uhW` is `UseHint`. -/
theorem uhLane_spec {a b c : Nat} (ha : a < 2 ^ 27) (hb : b < 2 ^ 29) (hc : c ≤ 1) :
    uhLane a b c = (Fips204.useHint c ((a : Int) - b)).toNat := by
  have hx : lx a b < 2 ^ 31 := by unfold lx; omega
  have hr : lr (lx a b) < 8380417 := by rw [lr_eq hx]; exact Nat.mod_lt _ (by omega)
  have hmod : ((a : Int) - b) % (Fips204.q : Int) = (lr (lx a b) : Int) := by
    rw [lr_eq hx]; unfold lx Fips204.q; push_cast; omega
  have e : Fips204.useHint c ((a : Int) - b) = Fips204.useHint c (lr (lx a b) : Int) := by
    rw [← hmod]
    unfold Fips204.useHint Fips204.decompose
    rw [Int.emod_emod]
  rw [e, ← useHint_lane _ _ hr hc, Int.toNat_natCast, uhLane, lf_eq (lv_le hr hc)]
  unfold lv; rw [lpos_eq hr, lr1_eq hr]; norm_num

theorem uhLane_lt {a b c : Nat} (ha : a < 2 ^ 27) (hb : b < 2 ^ 29) (hc : c ≤ 1) :
    uhLane a b c < 44 := by
  have hx : lx a b < 2 ^ 31 := by unfold lx; omega
  have hr : lr (lx a b) < 8380417 := by rw [lr_eq hx]; exact Nat.mod_lt _ (by omega)
  rw [uhLane, lf_eq (lv_le hr hc)]; exact Nat.mod_lt _ (by omega)

/-! ## Word level -/

theorem uhW_pack {a b c : Nat → Nat} (ha : ∀ r, r < 4 → a r < 2 ^ 27) (hb : ∀ r, r < 4 → b r < 2 ^ 29)
    (hc : ∀ r, r < 4 → c r ≤ 1) :
    uhW (pack4 a) (pack4 b) (pack4 c) = UInt256.ofNat (pack4 fun r => uhLane (a r) (b r) (c r)) := by
  -- x
  have hX : uhX (pack4 a) (pack4 b) = UInt256.ofNat (pack4 fun r => lx (a r) (b r)) := by
    unfold uhX
    rw [show 6733405452027397254358290306971416642451224083449399316382630281344 + pack4 a =
      pack4 fun r => 1072693376 + a r by unfold pack4; norm_num; ring]
    rw [u_sub (fun r hr => by have := ha r hr; show _ < _; omega)
      (fun r hr => by have := ha r hr; have := hb r hr; show _ ≤ _; omega)]
    congr 2; funext r; unfold lx; omega
  have hx31 : ∀ r, r < 4 → lx (a r) (b r) < 2 ^ 31 := fun r hr => by
    have := ha r hr; unfold lx; omega
  -- r
  have hR : uhR (UInt256.ofNat (pack4 fun r => lx (a r) (b r))) =
      UInt256.ofNat (pack4 fun r => lr (lx (a r) (b r))) := by
    unfold uhR uhQ
    rw [u_mul, u_shr_and (j := 9) (fun r hr => by have := hx31 r hr; show _ < _; omega) (by norm_num)
      (by norm_num) (by unfold pack4; norm_num), u_mul,
      u_sub (fun r hr => by have := hx31 r hr; show _ < _; omega)
        (fun r hr => by have := hx31 r hr; show _ ≤ _; rw [div_q this]; exact Nat.mul_div_le _ _)]
    rfl
  have hr : ∀ r, r < 4 → lr (lx (a r) (b r)) < 8380417 := fun r hr => by
    rw [lr_eq (hx31 r hr)]; exact Nat.mod_lt _ (by omega)
  -- r1
  have hR1 : uhR1 (UInt256.ofNat (pack4 fun r => lr (lx (a r) (b r)))) =
      UInt256.ofNat (pack4 fun r => lr1 (lr (lx (a r) (b r)))) := by
    unfold uhR1
    rw [show (597774675362608995853251492645737171287680740456972623552803839 : Nat) =
      pack4 fun _ => 95231 by unfold pack4; norm_num, u_add, u_mul,
      u_shr_and (j := 6) (fun r hr' => by have := hr r hr'; show _ < _; omega) (by norm_num)
        (by norm_num) (by unfold pack4; norm_num)]
    rfl
  have hr1 : ∀ r, r < 4 → lr1 (lr (lx (a r) (b r))) ≤ 44 := fun r hr' => by
    have := hr r hr'; rw [lr1_eq this]; omega
  -- pos
  have hP : uhPos (UInt256.ofNat (pack4 fun r => lr (lx (a r) (b r)))) =
      UInt256.ofNat (pack4 fun r => lpos (lr (lx (a r) (b r)))) := by
    unfold uhPos
    rw [hR1, show (597780952464344382534015668717527299892560324633768593065079808 : Nat) =
      pack4 fun _ => 95232 by unfold pack4; norm_num, u_add, u_mul,
      u_sub (fun r hr' => by have := hr r hr'; show _ < _; omega)
        (fun r hr' => by
          have := hr r hr'; show _ ≤ _; rw [lr1_eq this]; omega),
      show (104714504438991106934412238609704954414940284379357872306006166527 : Nat) =
        pack4 fun _ => 16681983 by unfold pack4; norm_num, u_add,
      u_shr_and (j := 1) (fun r hr' => by have := hr r hr'; show _ < _; omega) (by norm_num)
        (by norm_num) (by unfold pack4; norm_num)]
    rfl
  -- v
  have hV : uhV (UInt256.ofNat (pack4 fun r => lr (lx (a r) (b r)))) (pack4 c) =
      UInt256.ofNat (pack4 fun r => lv (lr (lx (a r) (b r))) (c r)) := by
    unfold uhV
    have hpl : Lanes fun r => lpos (lr (lx (a r) (b r))) := fun r _ =>
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
    rw [hP, hR1, show (276192476357013953623747158765658614701703779022658540142636 : Nat) =
      pack4 fun _ => 44 by unfold pack4; norm_num,
      u_sub (fun r _ => by show _ < _; omega) (fun r hr' => by have := hc r hr'; show _ ≤ _; omega),
      u_and (fun r hr' => by have := hc r hr'; show _ < _; omega) hpl, u_shl _ (by norm_num),
      u_add, u_add]
    rfl
  have hv : ∀ r, r < 4 → lv (lr (lx (a r) (b r))) (c r) ≤ 89 := fun r hr' => lv_le (hr r hr') (hc r hr')
  unfold uhW
  rw [hX, hR, hV]
  unfold uhF
  rw [u_mul, u_shr_and (j := 2) (fun r hr' => by have := hv r hr'; show _ < _; omega) (by norm_num)
      (by norm_num) (by unfold pack4; norm_num), u_mul,
    u_sub (fun r hr' => by have := hv r hr'; show _ < _; omega)
      (fun r hr' => by have := hv r hr'; show _ ≤ _; interval_cases (lv (lr (lx (a r) (b r))) (c r)) <;> norm_num)]
  rfl

end MlDsaOpt44.Proofs.UH
