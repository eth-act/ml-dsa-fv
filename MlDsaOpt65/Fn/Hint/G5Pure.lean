import MlDsaOpt44.Fn.Hint.UseHint
import MlDsaOpt44.Fn.Hint.PackMain
import MlDsa.Spec.Fips204
/-!
# `usehint`, `pack` for `γ2 = (q − 1)/32` (ML-DSA-65 and ML-DSA-87): pure part

Shared by `MlDsaOpt65` and `MlDsaOpt87` (the two artifacts emit identical `usehint` and
`pack` code). `uhW w s h` is the word the `usehint` loop body stores, in the shape the
block tactic produces; `uhW_pack` evaluates it lane-wise on in-range words and
`uhLane_spec` identifies a lane with FIPS 204 `UseHint` (any parameter set with
`γ2 = 261888`): `D = ((r + γ2 − 1) · 16793617) >> 42 = 2 r1 + [r0 > 0]` (`lD_eq`) and the
lane `(D >> 1) + 16 − h + 2 (h & D)` equals the v2 form `16 − h + 2 (h & [r0 > 0]) + r1`
(`lv_eq`), the corner `r = q − 1` folded into `mod 16`. `uhW_lt16` bounds every lane by `16`
unconditionally (final `AND 15`).
For `pack`: `pkX M wp k` is the `OR` of the first `k` coefficient words shifted by `4i`,
`pkX_eq` its lane-wise value, and `le64_sbp15_testBit` the bits of a `SimpleBitPack(w, 15)`
stream lane.
-/

namespace MlDsaOpt65.Proofs.G5H

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.L10

/-! ## `usehint`: the stored word -/

def uhX (w s : Nat) : UInt256 :=
  UInt256.ofNat (6733405452027397254358290306971416642451224083449399316382630281344 + w) -
    UInt256.ofNat s

def uhQ (x : UInt256) : UInt256 :=
  (UInt256.ofNat 3207598986782593870493972684755717093467514342740420773020159).land
    ((UInt256.ofNat 1074791297 * x).shiftRight (UInt256.ofNat 53))

def uhR (x : UInt256) : UInt256 := x - UInt256.ofNat 8380417 * uhQ x

/-- `D = ((r + γ2 − 1) · 16793617) >> 42` (7 bits per lane): `2 r1 + [r0 > 0]`. -/
def uhD (r : UInt256) : UInt256 :=
  (UInt256.ofNat 797191920394108457050361117346332819707190453088128059048063).land
    ((UInt256.ofNat 16793617 *
      (UInt256.ofNat 1643891342175211665287778912901409946099661308566067661416693503 + r)).shiftRight
      (UInt256.ofNat 42))

/-- `(D >> 1) + 16 − h + 2 (h & D)`. -/
def uhV (d : UInt256) (h : Nat) : UInt256 :=
  (UInt256.ofNat 395457409329360888143092522778102107413803138146079273386047).land
      (d.shiftRight (UInt256.ofNat 1)) +
    (UInt256.ofNat 100433627766186892226817148642057678073346828735512196415504 - UInt256.ofNat h +
      ((UInt256.ofNat h).land d + (UInt256.ofNat h).land d))

def uhF (v : UInt256) : UInt256 :=
  (UInt256.ofNat 94156526030800211462641076851929073193762651939542684139535).land v

/-- The word stored for `W` (at `p`), `S` (at `p − 0x4900`) and `H` (at `p + 0x4000`). -/
def uhW (w s h : Nat) : UInt256 := uhF (uhV (uhD (uhR (uhX w s))) h)

/-! ## `usehint`: lane functions -/

open MlDsaOpt44.Proofs.UH (lx lr lr_eq land_bit)

def lD (r : Nat) : Nat := 16793617 * (261887 + r) / 2 ^ 42 % 2 ^ 7
def lv (d c : Nat) : Nat := d / 2 ^ 1 % 2 ^ 6 + (16 - c + ((c &&& d) + (c &&& d)))

/-- One lane of `uhW`. -/
def uhLane (a b c : Nat) : Nat := 15 &&& lv (lD (lr (lx a b))) c

/-- The exact quotient: `D = ⌊(r + γ2 − 1) / γ2⌋ = 2 r1 + [r0 > 0]`. -/
theorem lD_eq {r : Nat} (hr : r < 8380417) : lD r = (261887 + r) / 261888 := by
  have h : 16793617 * (261887 + r) / 2 ^ 42 = (261887 + r) / 261888 := by omega
  unfold lD; rw [h]; omega

/-- `lv` is the v2 form `16 − h + 2 (h & [r0 > 0]) + r1`. -/
theorem lv_eq {r c : Nat} (hr : r < 8380417) (hc : c ≤ 1) :
    lv (lD r) c = 16 - c + 2 * (c &&& (if 523776 * ((261887 + r) / 523776) < r then 1 else 0)) +
      (261887 + r) / 523776 := by
  unfold lv; rw [lD_eq hr, land_bit hc, land_bit hc]
  split_ifs <;> omega

theorem lv_le {r c : Nat} (hr : r < 8380417) (hc : c ≤ 1) : lv (lD r) c ≤ 34 := by
  rw [lv_eq hr hc, land_bit hc]; split_ifs <;> omega

theorem and15 (v : Nat) : 15 &&& v = v % 16 := by
  rw [Nat.and_comm, show (15 : Nat) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem useHint_lane (Q : Params) (hQ : Q.gamma2 = 261888) (r c : Nat) (hr : r < 8380417)
    (hc : c ≤ 1) :
    (((16 - c + 2 * (c &&& (if 523776 * ((261887 + r) / 523776) < r then 1 else 0)) +
      (261887 + r) / 523776) % 16 : Nat) : Int) = Fips204.useHint Q c r := by
  have hq : ((r : Int) % (8380417 : Nat)) = r := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Fips204.useHint, Fips204.decompose, Fips204.modPm, Fips204.q, hQ, hq]
  norm_num
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 523776 ∧ r = 523776 * a + b :=
    ⟨r / 523776, r % 523776, Nat.mod_lt _ (by omega), (Nat.div_add_mod r 523776).symm⟩
  have ha : a ≤ 16 := by omega
  have e1 : (261887 + (523776 * a + b)) / 523776 = if b ≤ 261888 then a else a + 1 := by
    split_ifs <;> omega
  rw [e1]
  have e2 : ((523776 * a + b : Nat) : Int) % 523776 = b := by omega
  push_cast at e2 ⊢
  rw [e2]
  interval_cases c <;> by_cases hb2 : b ≤ 261888 <;> simp [hb2] <;> split_ifs <;> omega

/-- A lane of `uhW` is `UseHint` (`γ2 = 261888`). -/
theorem uhLane_spec (Q : Params) (hQ : Q.gamma2 = 261888) {a b c : Nat} (ha : a < 2 ^ 27)
    (hb : b < 2 ^ 29) (hc : c ≤ 1) :
    uhLane a b c = (Fips204.useHint Q c ((a : Int) - b)).toNat := by
  have hx : lx a b < 2 ^ 31 := by unfold lx; omega
  have hr : lr (lx a b) < 8380417 := by rw [lr_eq hx]; exact Nat.mod_lt _ (by omega)
  have hmod : ((a : Int) - b) % (Fips204.q : Int) = (lr (lx a b) : Int) := by
    rw [lr_eq hx]; unfold lx Fips204.q; push_cast; omega
  have e : Fips204.useHint Q c ((a : Int) - b) = Fips204.useHint Q c (lr (lx a b) : Int) := by
    rw [← hmod]
    unfold Fips204.useHint Fips204.decompose
    rw [Int.emod_emod]
  rw [e, ← useHint_lane Q hQ _ _ hr hc, Int.toNat_natCast, uhLane, and15, lv_eq hr hc]

/-! ## `usehint`: word level -/

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
        (fun r hr => by
          have := hx31 r hr; show _ ≤ _; rw [MlDsaOpt44.Proofs.UH.div_q this]
          exact Nat.mul_div_le _ _)]
    rfl
  have hr : ∀ r, r < 4 → lr (lx (a r) (b r)) < 8380417 := fun r hr => by
    rw [lr_eq (hx31 r hr)]; exact Nat.mod_lt _ (by omega)
  -- D
  have hD : uhD (UInt256.ofNat (pack4 fun r => lr (lx (a r) (b r)))) =
      UInt256.ofNat (pack4 fun r => lD (lr (lx (a r) (b r)))) := by
    unfold uhD
    rw [show (1643891342175211665287778912901409946099661308566067661416693503 : Nat) =
      pack4 fun _ => 261887 by unfold pack4; norm_num, u_add, u_mul,
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
      show (100433627766186892226817148642057678073346828735512196415504 : Nat) =
        pack4 fun _ => 16 by unfold pack4; norm_num,
      u_sub (fun r _ => by show _ < _; omega) (fun r hr' => by have := hc r hr'; show _ ≤ _; omega),
      u_and (fun r hr' => by have := hc r hr'; show _ < _; omega) hd, u_add, u_add, u_add]
    rfl
  have hv : ∀ r, r < 4 → lv (lD (lr (lx (a r) (b r)))) (c r) ≤ 34 := fun r hr' =>
    lv_le (hr r hr') (hc r hr')
  unfold uhW
  rw [hX, hR, hD, hV]
  unfold uhF
  rw [show (94156526030800211462641076851929073193762651939542684139535 : Nat) =
      pack4 fun _ => 15 by unfold pack4; norm_num,
    u_and (fun r _ => by show _ < _; omega) (fun r hr' => by have := hv r hr'; show _ < _; omega)]
  rfl

/-- Lane `r` of the stored word is `UseHint` on in-range lanes. -/
theorem uhW_spec (Q : Params) (hQ : Q.gamma2 = 261888) {w s h : Nat} (hw : w < 2 ^ 256)
    (hs : s < 2 ^ 256) (hh : h < 2 ^ 256)
    (hb : ∀ r, r < 4 → lane w r < 2 ^ 27 ∧ lane s r < 2 ^ 29 ∧ lane h r ≤ 1) {r : Nat} (hr : r < 4) :
    lane (uhW w s h).toNat r = (Fips204.useHint Q (lane h r) ((lane w r : Int) - lane s r)).toNat := by
  have key := uhW_pack (a := fun r => lane w r) (b := fun r => lane s r) (c := fun r => lane h r)
    (fun r hr => (hb r hr).1) (fun r hr => (hb r hr).2.1) (fun r hr => (hb r hr).2.2)
  rw [pk_lanes hw, pk_lanes hs, pk_lanes hh] at key
  have hl : Lanes fun r => uhLane (lane w r) (lane s r) (lane h r) := fun r _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)
  rw [key, toNat_ofNat_of_lt (pk_lt hl), pk_lane hl hr]
  exact uhLane_spec Q hQ (hb r hr).1 (hb r hr).2.1 (hb r hr).2.2

/-- Every lane of the stored word is below `16` (final `AND 15`). -/
theorem uhW_lt16 (w s h : Nat) {r : Nat} (hr : r < 4) : lane (uhW w s h).toNat r < 16 := by
  unfold uhW uhF
  generalize uhV (uhD (uhR (uhX w s))) h = v
  rw [← ofNat_toNat v, ← pk_lanes (MlDsaOpt44.Proofs.PK.u_toNat_lt v), show
      (94156526030800211462641076851929073193762651939542684139535 : Nat) =
      pack4 fun _ => 15 by unfold pack4; norm_num,
    u_and (fun r _ => by show (15 : Nat) < _; omega) (lanes_lane _)]
  have hl : Lanes fun r => 15 &&& lane v.toNat r := fun r _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)
  rw [toNat_ofNat_of_lt (pk_lt hl), pk_lane hl hr]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

/-! ## `pack`: bits of `SimpleBitPack(w, 15)` -/

open MlDsaOpt44.Proofs.PK (digits_testBit bits_testBit bits_lt le64_eq le64_lt Xl u_toNat_lt)

theorem bitlen_15 : Fips204.bitlen 15 = 4 := by
  decide

/-- Byte `n < 128` of `SimpleBitPack w 15`. -/
theorem byteAt_sbp15 (w : Fips204.Poly) {n : Nat} (hn : n < 128) :
    byteAt (Fips204.simpleBitPack w 15) n =
      ((List.range 8).map fun t => w[(8 * n + t) / 4]!.toNat / 2 ^ ((8 * n + t) % 4) % 2 * 2 ^ t).sum := by
  have hs : (Fips204.simpleBitPack w 15).size = 128 := by
    simp [Fips204.simpleBitPack, bitlen_15, ByteArray.size]
  unfold byteAt
  rw [dif_pos (by omega)]
  have hlt : ((List.range 8).map fun t => w[(8 * n + t) / 4]!.toNat / 2 ^ ((8 * n + t) % 4) % 2 * 2 ^ t).sum
      < 256 := by
    exact bits_lt (fun t => w[(8 * n + t) / 4]!.toNat / 2 ^ ((8 * n + t) % 4)) 8
  simp only [Fips204.simpleBitPack, bitlen_15]
  simp [ByteArray.getElem_eq_data_getElem, Array.getElem_map, Array.getElem_range,
    Nat.mod_eq_of_lt hlt]

/-- Bit `b` of stream lane `x < 16` of `SimpleBitPack w 15`. -/
theorem le64_sbp15_testBit (w : Fips204.Poly) {x : Nat} (hx : x < 16) (b : Nat) :
    (le64 (Fips204.simpleBitPack w 15) (8 * x)).testBit b =
      (decide (b < 64) && (w[(64 * x + b) / 4]!.toNat).testBit ((64 * x + b) % 4)) := by
  rw [le64_eq, (digits_testBit 8 (by omega) _ 8 (fun i _ => byteAt_lt _ _)).2 b]
  by_cases hb : b < 64
  · simp only [show b < 8 * 8 by omega, decide_true, Bool.true_and]
    rw [byteAt_sbp15 w (by omega)]
    rw [bits_testBit (fun t => w[(8 * (8 * x + b / 8) + t) / 4]!.toNat / 2 ^ ((8 * (8 * x + b / 8) + t) % 4))]
    have e : 8 * (8 * x + b / 8) + b % 8 = 64 * x + b := by omega
    rw [decide_eq_true (Nat.mod_lt _ (by omega)), Bool.true_and, Nat.testBit_eq_decide_div_mod_eq, e]
  · simp only [show ¬ b < 8 * 8 by omega, decide_false, Bool.false_and]

/-! ## `pack`: the `OR` of sixteen shifted coefficient words -/

/-- The value the `pack` loop body builds from the 16 coefficient words at `wp`
(the shape of the block tactic). -/
def pkA (M : ByteArray) (wp : Nat) : UInt256 :=
  ((UInt256.ofNat (word M (480 + wp))).shiftLeft (UInt256.ofNat 60)).lor
    (((UInt256.ofNat (word M (448 + wp))).shiftLeft (UInt256.ofNat 56)).lor
    (((UInt256.ofNat (word M (416 + wp))).shiftLeft (UInt256.ofNat 52)).lor
    (((UInt256.ofNat (word M (384 + wp))).shiftLeft (UInt256.ofNat 48)).lor
    (((UInt256.ofNat (word M (352 + wp))).shiftLeft (UInt256.ofNat 44)).lor
    (((UInt256.ofNat (word M (320 + wp))).shiftLeft (UInt256.ofNat 40)).lor
    (((UInt256.ofNat (word M (288 + wp))).shiftLeft (UInt256.ofNat 36)).lor
    (((UInt256.ofNat (word M (256 + wp))).shiftLeft (UInt256.ofNat 32)).lor
    (((UInt256.ofNat (word M (224 + wp))).shiftLeft (UInt256.ofNat 28)).lor
    (((UInt256.ofNat (word M (192 + wp))).shiftLeft (UInt256.ofNat 24)).lor
    (((UInt256.ofNat (word M (160 + wp))).shiftLeft (UInt256.ofNat 20)).lor
    (((UInt256.ofNat (word M (128 + wp))).shiftLeft (UInt256.ofNat 16)).lor
    (((UInt256.ofNat (word M (96 + wp))).shiftLeft (UInt256.ofNat 12)).lor
    (((UInt256.ofNat (word M (64 + wp))).shiftLeft (UInt256.ofNat 8)).lor
    (((UInt256.ofNat (word M (32 + wp))).shiftLeft (UInt256.ofNat 4)).lor
    ((UInt256.ofNat (word M wp)).lor (UInt256.ofNat 0))))))))))))))))

/-- `pkA` as a recursion: the first `k` words. -/
def pkX (M : ByteArray) (wp : Nat) : Nat → UInt256
  | 0 => UInt256.ofNat 0
  | 1 => (UInt256.ofNat (word M wp)).lor (UInt256.ofNat 0)
  | k + 2 => ((UInt256.ofNat (word M (32 * (k + 1) + wp))).shiftLeft (UInt256.ofNat (4 * (k + 1)))).lor
      (pkX M wp (k + 1))

theorem pkA_eq (M : ByteArray) (wp : Nat) : pkA M wp = pkX M wp 16 := rfl

/-- Lane `r` of coefficient word `i` at `wp`. -/
def cw (M : ByteArray) (wp i r : Nat) : Nat := lane (word M (32 * i + wp)) r

/-- The 4-bit digit sum of lane `r` over the first `k` words. -/
def pkS (M : ByteArray) (wp k r : Nat) : Nat := ((List.range k).map fun i => cw M wp i r * 2 ^ (4 * i)).sum

/-- The replication constant `REP`. -/
def REPc : Nat := 6277101735386680764176071790128604879584176795969512275969

/-- The four stored words (lane `j` of `x`, replicated). -/
def pw0 (x : UInt256) : UInt256 := UInt256.ofNat REPc * (UInt256.ofNat 18446744073709551615).land x
def pw1 (x : UInt256) : UInt256 :=
  UInt256.ofNat REPc * (UInt256.ofNat 18446744073709551615).land (x.shiftRight (UInt256.ofNat 64))
def pw2 (x : UInt256) : UInt256 :=
  UInt256.ofNat REPc * (UInt256.ofNat 18446744073709551615).land (x.shiftRight (UInt256.ofNat 128))
def pw3 (x : UInt256) : UInt256 := UInt256.ofNat REPc * x.shiftRight (UInt256.ofNat 192)

theorem pk_or {a b : Nat → Nat} (ha : Lanes a) (hb : Lanes b) :
    pack4 a ||| pack4 b = pack4 fun r => a r ||| b r := by
  have hab : Lanes fun r => a r ||| b r := fun r hr => Nat.or_lt_two_pow (ha r hr) (hb r hr)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, testBit_pk ha, testBit_pk hb, testBit_pk hab, Nat.testBit_or]
  cases decide (i < 256) <;> simp

theorem or_add {n x y : Nat} (hx : x < 2 ^ n) : 2 ^ n * y ||| x = x + 2 ^ n * y := by
  apply Nat.eq_of_testBit_eq; intro i
  have h0 := Nat.testBit_two_pow_mul_add y (Nat.two_pow_pos n) i
  rw [Nat.add_zero] at h0
  rw [Nat.testBit_or, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hx, h0]
  split_ifs with h
  · simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp

theorem pk_congr {f g : Nat → Nat} (h : ∀ r, r < 4 → f r = g r) : pack4 f = pack4 g := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem pkS_succ (M : ByteArray) (wp k r : Nat) :
    pkS M wp (k + 1) r = pkS M wp k r + 2 ^ (4 * k) * cw M wp k r := by
  unfold pkS
  rw [List.range_succ, List.map_append, List.sum_append]
  simp [Nat.mul_comm]

theorem pkS_lt (M : ByteArray) (wp : Nat) (hA : ∀ i r, i < 16 → r < 4 → cw M wp i r < 16)
    {k r : Nat} (hk : k ≤ 16) (hr : r < 4) : pkS M wp k r < 2 ^ (4 * k) :=
  (digits_testBit 4 (by omega) (fun i => cw M wp i r) k (fun i hi => hA i r (by omega) hr)).1

theorem pkS_lanes (M : ByteArray) (wp : Nat) (hA : ∀ i r, i < 16 → r < 4 → cw M wp i r < 16)
    {k : Nat} (hk : k ≤ 16) : Lanes fun r => pkS M wp k r := fun r hr =>
  Nat.lt_of_lt_of_le (pkS_lt M wp hA hk hr) (Nat.pow_le_pow_right (by omega) (by omega))

theorem pkX_eq (M : ByteArray) (wp : Nat) (hA : ∀ i r, i < 16 → r < 4 → cw M wp i r < 16) :
    ∀ k, k ≤ 16 → pkX M wp k = UInt256.ofNat (pack4 fun r => pkS M wp k r)
  | 0, _ => by simp [pkX, pkS, pack4]
  | 1, _ => by
    show (UInt256.ofNat (word M wp)).lor (UInt256.ofNat 0) = _
    rw [ofNat_lor, Nat.or_zero]
    congr 1
    rw [← pk_lanes (word_lt M wp)]
    congr 1; funext r
    simp [pkS, cw]
  | k + 2, hk => by
    show ((UInt256.ofNat (word M (32 * (k + 1) + wp))).shiftLeft (UInt256.ofNat (4 * (k + 1)))).lor
      (pkX M wp (k + 1)) = _
    rw [pkX_eq M wp hA (k + 1) (by omega), ← pk_lanes (word_lt M (32 * (k + 1) + wp)),
      u_shl _ (by omega), ofNat_lor,
      pk_or (a := fun r => 2 ^ (4 * (k + 1)) * lane (word M (32 * (k + 1) + wp)) r) (fun r hr => Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (hA (k + 1) r (by omega) hr)
        (Nat.two_pow_pos _)) (by rw [show (16 : Nat) = 2 ^ 4 by norm_num, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)))
        (pkS_lanes M wp hA (by omega))]
    congr 1; apply pk_congr; intro r hr
    rw [show pkS M wp (k + 2) r = _ from pkS_succ M wp (k + 1) r,
      or_add (pkS_lt M wp hA (k := k + 1) (by omega) hr)]
    rfl

/-- Lane `j` of the built value is the digit sum. -/
theorem Xl_pkA (M : ByteArray) (wp : Nat) (hA : ∀ i r, i < 16 → r < 4 → cw M wp i r < 16)
    {j : Nat} (hj : j < 4) : Xl (pkA M wp) j = pkS M wp 16 j := by
  have hl := pkS_lanes M wp hA (le_refl 16)
  rw [pkA_eq, pkX_eq M wp hA 16 le_rfl, Xl, toNat_ofNat_of_lt (pk_lt hl), Nat.shiftRight_eq_div_pow]
  exact pk_lane hl hj

theorem pkS_testBit (M : ByteArray) (wp : Nat) (hA : ∀ i r, i < 16 → r < 4 → cw M wp i r < 16)
    {r : Nat} (hr : r < 4) (b : Nat) :
    (pkS M wp 16 r).testBit b = (decide (b < 64) && (cw M wp (b / 4) r).testBit (b % 4)) :=
  (digits_testBit 4 (by omega) (fun i => cw M wp i r) 16 (fun i hi => hA i r hi hr)).2 b

/-! ## `pack`: the stored words -/

theorem pw0_eq (x : UInt256) : (pw0 x).toNat = rep (Xl x 0) := MlDsaOpt44.Proofs.PK.st_lane0 x
theorem pw1_eq (x : UInt256) : (pw1 x).toNat = rep (Xl x 1) :=
  MlDsaOpt44.Proofs.PK.st_lane x (by norm_num) (by norm_num)
theorem pw2_eq (x : UInt256) : (pw2 x).toNat = rep (Xl x 2) :=
  MlDsaOpt44.Proofs.PK.st_lane x (by norm_num) (by norm_num)
theorem pw3_eq (x : UInt256) : (pw3 x).toNat = rep (Xl x 3) := MlDsaOpt44.Proofs.PK.st_lane3 x

/-- A stored stream lane is the `SimpleBitPack(·, 15)` stream lane of row `r` (16 words of
coefficients `16 j … 16 j + 15` at `wp = base + 512 j`). -/
theorem Xl_pkA_le64 (M : ByteArray) (base j : Nat) (hj : j < 16)
    (hA : ∀ t r, t < 256 → r < 4 → lane (word M (base + 32 * t)) r < 16) {r : Nat} (hr : r < 4) :
    Xl (pkA M (base + 512 * j)) r = le64 (Fips204.simpleBitPack (lanesPoly M base r) 15) (8 * j) := by
  have hA' : ∀ i r, i < 16 → r < 4 → cw M (base + 512 * j) i r < 16 := fun i r hi hr => by
    unfold cw
    rw [show 32 * i + (base + 512 * j) = base + 32 * (16 * j + i) by ring]
    exact hA _ r (by omega) hr
  rw [Xl_pkA M _ hA' hr]
  apply eq_of_testBit_lt (pkS_lt M _ hA' le_rfl hr) (le64_lt _ _)
  intro b hb
  rw [pkS_testBit M _ hA' hr, le64_sbp15_testBit _ hj, decide_eq_true hb, Bool.true_and, Bool.true_and]
  have ht : (64 * j + b) / 4 < 256 := by omega
  rw [MlDsaOpt44.Proofs.PK.lanesPoly_get' M base r ht, Int.toNat_natCast]
  unfold cw
  rw [show 32 * (b / 4) + (base + 512 * j) = base + 32 * ((64 * j + b) / 4) by omega,
    show b % 4 = (64 * j + b) % 4 by omega]

end MlDsaOpt65.Proofs.G5H
