import MlDsaOpt44.Fn.Hint.Lanes
import MlDsaOpt44.Budget
/-!
# `usehint` (WP10): loop body as a word function, lane semantics, `UseHint`

`uhW w s h` is the word the loop body stores, written with the `UInt256`
operations in exactly the shape `opt44_block` produces (so the block lemma's
residual closes by unfolding). The 2γ2 quotient and the sign of `r0` come from one
exact multiply-shift `D = ((r + γ2 − 1) · 2886403) >> 38 = 2 r1 + [r0 > 0]` (`lD_eq`); the
stored lane is `((D >> 1) + 44 − h + 2 (h & D)) mod 44`, equal to the v2 form
`(44 − h + 2 (h & [r0 > 0]) + r1) mod 44` (`lv_eq`), with the corner `r = q − 1` (`r1 = 44`)
folded into the `mod 44`. `uhW_pack` evaluates the word lane-wise on in-range words,
`uhLane_spec` identifies a lane with FIPS 204 `UseHint`.
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

/-- `D = ((r + γ2 − 1) · 2886403) >> 38` (7 bits per lane): `2 r1 + [r0 > 0]`. -/
def uhD (r : UInt256) : UInt256 :=
  (UInt256.ofNat 797191920394108457050361117346332819707190453088128059048063).land
    ((UInt256.ofNat 2886403 *
      (UInt256.ofNat 597774675362608995853251492645737171287680740456972623552803839 + r)).shiftRight
      (UInt256.ofNat 38))

/-- `(D >> 1) + 44 − h + 2 (h & D)`. -/
def uhV (d : UInt256) (h : Nat) : UInt256 :=
  (UInt256.ofNat 395457409329360888143092522778102107413803138146079273386047).land
      (d.shiftRight (UInt256.ofNat 1)) +
    (UInt256.ofNat 276192476357013953623747158765658614701703779022658540142636 - UInt256.ofNat h +
      ((UInt256.ofNat h).land d + (UInt256.ofNat h).land d))

def uhF (v : UInt256) : UInt256 :=
  v - UInt256.ofNat 44 *
    (UInt256.ofNat 18831305206160042292528215370385814638752530387908536827907).land
      ((UInt256.ofNat 94 * v).shiftRight (UInt256.ofNat 12))

/-- The word stored for `W` (at `ACC`), `S` (at `SP`) and `H` (at `HP`). -/
def uhW (w s h : Nat) : UInt256 := uhF (uhV (uhD (uhR (uhX w s))) h)

/-! ## Lane functions -/

def lx (a b : Nat) : Nat := a + 1072693376 - b
def lr (x : Nat) : Nat := x - 8380417 * (1074791297 * x / 2 ^ 53 % 2 ^ 9)
def lD (r : Nat) : Nat := 2886403 * (95231 + r) / 2 ^ 38 % 2 ^ 7
def lv (d c : Nat) : Nat := d / 2 ^ 1 % 2 ^ 6 + (44 - c + ((c &&& d) + (c &&& d)))
def lf (v : Nat) : Nat := v - 44 * (94 * v / 2 ^ 12 % 2 ^ 2)

/-- One lane of `uhW`. -/
def uhLane (a b c : Nat) : Nat := lf (lv (lD (lr (lx a b))) c)

theorem div_q {x : Nat} (hx : x < 2 ^ 31) : 1074791297 * x / 2 ^ 53 % 2 ^ 9 = x / 8380417 := by
  have h : 1074791297 * x / 2 ^ 53 = x / 8380417 := by omega
  rw [h]; omega

theorem lf_eq {v : Nat} (hv : v ≤ 89) : lf v = v % 44 := by
  unfold lf; interval_cases v <;> rfl

theorem lr_eq {x : Nat} (hx : x < 2 ^ 31) : lr x = x % 8380417 := by
  unfold lr; rw [div_q hx]; omega

/-- The exact quotient: `D = ⌊(r + γ2 − 1) / γ2⌋ = 2 r1 + [r0 > 0]`. -/
theorem lD_eq {r : Nat} (hr : r < 8380417) : lD r = (95231 + r) / 95232 := by
  have h : 2886403 * (95231 + r) / 2 ^ 38 = (95231 + r) / 95232 := by omega
  unfold lD; rw [h]; omega

theorem land_bit {c d : Nat} (hc : c ≤ 1) : c &&& d = if c = 0 then 0 else d % 2 := by
  interval_cases c
  · simp
  · rw [Nat.and_comm, Nat.and_one_is_mod]; rfl

/-- `lv` is the v2 form `44 − h + 2 (h & [r0 > 0]) + r1`. -/
theorem lv_eq {r c : Nat} (hr : r < 8380417) (hc : c ≤ 1) :
    lv (lD r) c = 44 - c + 2 * (c &&& (if 190464 * ((95231 + r) / 190464) < r then 1 else 0)) +
      (95231 + r) / 190464 := by
  unfold lv; rw [lD_eq hr, land_bit hc, land_bit hc]
  split_ifs <;> omega

theorem lv_le {r c : Nat} (hr : r < 8380417) (hc : c ≤ 1) : lv (lD r) c ≤ 89 := by
  rw [lv_eq hr hc, land_bit hc]; split_ifs <;> omega

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
  rw [e, ← useHint_lane _ _ hr hc, Int.toNat_natCast, uhLane, lf_eq (lv_le hr hc), lv_eq hr hc]

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
  -- D
  have hD : uhD (UInt256.ofNat (pack4 fun r => lr (lx (a r) (b r)))) =
      UInt256.ofNat (pack4 fun r => lD (lr (lx (a r) (b r)))) := by
    unfold uhD
    rw [show (597774675362608995853251492645737171287680740456972623552803839 : Nat) =
      pack4 fun _ => 95231 by unfold pack4; norm_num, u_add, u_mul,
      u_shr_and (j := 7) (fun r hr' => by have := hr r hr'; show _ < _; omega) (by norm_num)
        (by norm_num) (by unfold pack4; norm_num)]
    rfl
  have hd : Lanes fun r => lD (lr (lx (a r) (b r))) := fun r _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  -- v
  have hV : uhV (UInt256.ofNat (pack4 fun r => lD (lr (lx (a r) (b r))))) (pack4 c) =
      UInt256.ofNat (pack4 fun r => lv (lD (lr (lx (a r) (b r)))) (c r)) := by
    unfold uhV
    rw [u_shr_and (j := 6) hd (by norm_num) (by norm_num) (by unfold pack4; norm_num),
      show (276192476357013953623747158765658614701703779022658540142636 : Nat) =
        pack4 fun _ => 44 by unfold pack4; norm_num,
      u_sub (fun r _ => by show _ < _; omega) (fun r hr' => by have := hc r hr'; show _ ≤ _; omega),
      u_and (fun r hr' => by have := hc r hr'; show _ < _; omega) hd, u_add, u_add, u_add]
    rfl
  have hv : ∀ r, r < 4 → lv (lD (lr (lx (a r) (b r)))) (c r) ≤ 89 := fun r hr' =>
    lv_le (hr r hr') (hc r hr')
  unfold uhW
  rw [hX, hR, hD, hV]
  unfold uhF
  rw [u_mul, u_shr_and (j := 2) (fun r hr' => by have := hv r hr'; show _ < _; omega) (by norm_num)
      (by norm_num) (by unfold pack4; norm_num), u_mul,
    u_sub (fun r hr' => by have := hv r hr'; show _ < _; omega)
      (fun r hr' => by have := hv r hr'; show _ ≤ _; interval_cases (lv (lD (lr (lx (a r) (b r)))) (c r)) <;> norm_num)]
  rfl

end MlDsaOpt44.Proofs.UH
