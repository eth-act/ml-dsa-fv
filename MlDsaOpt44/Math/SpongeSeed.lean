import MlDsaOpt44.Fn.Sponge.Defs
import MlDsaOpt44.Math.SpongeBytes
set_option warningAsError true
/-!
# Single-block seed states and the `ginit` word

* `seedState rate msg`: the state after xoring the single padded block of
  `msg` into the empty state (before the first permutation); its lanes
  (`laneOf_seedState`, `laneOf_aSeed`, `laneOf_ctSeed`) and
  `absorb_single`.
* `ginitWord_eq`: the word `ginit` stores is the interleaved, complemented
  form of per-slot fresh lanes (ρ / c̃ lanes, lane 4, padding bits), with the
  `keep` slots carried over; `ginit_group` instantiates it for `group`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44

/-! ## Single-block seed states -/

/-- The absorbed state of a message shorter than one block, before the first
permutation. -/
def seedState (rate : Nat) (msg : ByteArray) : Fips202.SpongeState :=
  Fips202.xorBlock rate (Fips202.pad rate 0x1F msg) 0 Fips202.emptyState

/-- The ExpandA seed `ρ ‖ col ‖ r`. -/
def aSeed (cd : ByteArray) (r col : Nat) : ByteArray :=
  rhoOf cd ++ ByteArray.mk #[UInt8.ofNat col, UInt8.ofNat r]

theorem seedState_size (rate : Nat) (msg : ByteArray) : (seedState rate msg).size = 25 := by
  unfold seedState; rw [xorBlock_size, emptyState_size]

theorem laneOf_seedState {rate : Nat} (hr : rate / 8 ≤ 25) (msg : ByteArray) (x : Nat) :
    laneOf (seedState rate msg) x =
      if x < rate / 8 then le64 (Fips202.pad rate 0x1F msg) (8 * x) else 0 := by
  unfold seedState
  rw [laneOf_xorBlock _ _ emptyState_size hr, laneOf_emptyState, Nat.zero_add, Nat.zero_xor]

theorem absorb_single {rate : Nat} (hr : 0 < rate) {msg : ByteArray} (hm : msg.size < rate) :
    Fips202.absorb rate (Fips202.pad rate 0x1F msg) = Keccak.permute (seedState rate msg) := by
  rw [absorb_eq rate _ 1 hr (by rw [pad_size rate msg hr, Nat.div_eq_of_lt hm]), absorbPre_succ,
    absorbPre_zero, Nat.zero_mul]
  rfl

theorem sized4_seedState (rate : Nat) (msg : Nat → ByteArray) :
    Sized4 fun k => seedState rate (msg k) := fun k _ => seedState_size rate (msg k)

/-! ### Bytes of the padded seeds -/

theorem rhoOf_size {cd : ByteArray} (hcd : 32 ≤ cd.size) : (rhoOf cd).size = 32 := by
  unfold rhoOf; simp [ByteArray.size_extract]; omega

theorem byteAt_pair (a b : UInt8) (j : Nat) :
    byteAt (ByteArray.mk #[a, b]) j = if j = 0 then a.toNat else if j = 1 then b.toNat else 0 := by
  unfold byteAt
  by_cases h : j < 2
  · rw [dif_pos (show j < (ByteArray.mk #[a, b]).size from h)]
    interval_cases j <;> rfl
  · rw [dif_neg (show ¬ j < (ByteArray.mk #[a, b]).size from h), if_neg (by omega), if_neg (by omega)]

theorem byteAt_aSeed {cd : ByteArray} (hcd : 32 ≤ cd.size) {r col : Nat} (hr : r < 256)
    (hcol : col < 256) (i : Nat) :
    byteAt (aSeed cd r col) i =
      if i < 32 then byteAt cd i else if i = 32 then col else if i = 33 then r else 0 := by
  unfold aSeed
  rw [byteAt_append, rhoOf_size hcd, byteAt_pair]
  simp only [UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_eq_of_lt hcol, Nat.mod_eq_of_lt hr]
  by_cases h : i < 32
  · rw [if_pos h, if_pos h]; unfold rhoOf
    rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

theorem aSeed_size {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) : (aSeed cd r col).size = 34 := by
  unfold aSeed; rw [ByteArray.size_append, rhoOf_size hcd]; rfl

theorem byteAt_padASeed {cd : ByteArray} (hcd : 32 ≤ cd.size) {r col : Nat} (hr : r < 256)
    (hcol : col < 256) {i : Nat} (hi : i < 168) :
    byteAt (Fips202.pad 168 0x1F (aSeed cd r col)) i =
      if i < 32 then byteAt cd i else if i = 32 then col else if i = 33 then r
      else if i = 34 then 31 else if i = 167 then 128 else 0 := by
  rw [byteAt_pad1 168 _ (by rw [aSeed_size hcd]; omega) i hi, aSeed_size hcd,
    byteAt_aSeed hcd hr hcol]
  split_ifs <;> first | rfl | omega

/-- Lanes of the ExpandA seed state of `ρ ‖ col ‖ r`. -/
theorem laneOf_aSeed {cd : ByteArray} (hcd : 32 ≤ cd.size) {r col : Nat} (hr : r < 256)
    (hcol : col < 256) {x : Nat} (hx : x < 25) :
    laneOf (seedState 168 (aSeed cd r col)) x =
      if x < 4 then le64 cd (8 * x) else if x = 4 then col + 256 * r + 0x1F0000
      else if x = 20 then 2 ^ 63 else 0 := by
  rw [laneOf_seedState (by norm_num)]
  have hb := fun i (hi : i < 168) => byteAt_padASeed hcd hr hcol (i := i) hi
  by_cases h4 : x < 4
  · rw [if_pos (by norm_num; omega), if_pos h4]
    apply le64_congr
    intro k hk
    rw [hb _ (by omega), if_pos (by omega)]
  rw [if_neg h4]
  by_cases h21 : x < 21
  · rw [if_pos (by norm_num; omega), le64_eq]
    by_cases hx4 : x = 4
    · subst hx4
      simp only [hb _ (by norm_num : 32 < 168), hb _ (by norm_num : 32 + 1 < 168),
        hb _ (by norm_num : 32 + 2 < 168), hb _ (by norm_num : 32 + 3 < 168),
        hb _ (by norm_num : 32 + 4 < 168), hb _ (by norm_num : 32 + 5 < 168),
        hb _ (by norm_num : 32 + 6 < 168), hb _ (by norm_num : 32 + 7 < 168)]
      norm_num
      omega
    · by_cases hx20 : x = 20
      · subst hx20
        simp only [hb _ (by norm_num : 160 < 168), hb _ (by norm_num : 160 + 1 < 168),
          hb _ (by norm_num : 160 + 2 < 168), hb _ (by norm_num : 160 + 3 < 168),
          hb _ (by norm_num : 160 + 4 < 168), hb _ (by norm_num : 160 + 5 < 168),
          hb _ (by norm_num : 160 + 6 < 168), hb _ (by norm_num : 160 + 7 < 168)]
        norm_num
      · have hz : ∀ k, k < 8 → byteAt (Fips202.pad 168 0x1F (aSeed cd r col)) (8 * x + k) = 0 :=
          fun k hk => by
            rw [hb _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
        rw [show 8 * x = 8 * x + 0 from rfl, hz 0 (by omega), hz 1 (by omega), hz 2 (by omega),
          hz 3 (by omega), hz 4 (by omega), hz 5 (by omega), hz 6 (by omega), hz 7 (by omega),
          if_neg hx4, if_neg hx20]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega)]

theorem ctOf_size {cd : ByteArray} (hcd : 1344 ≤ cd.size) : (ctOf cd).size = 32 := by
  unfold ctOf; simp [ByteArray.size_extract]; omega

theorem byteAt_padCt {cd : ByteArray} (hcd : 1344 ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (Fips202.pad 136 0x1F (ctOf cd)) i =
      if i < 32 then byteAt cd (1312 + i) else if i = 32 then 31 else if i = 135 then 128 else 0 := by
  rw [byteAt_pad1 136 _ (by rw [ctOf_size hcd]; omega) i hi, ctOf_size hcd]
  by_cases h : i < 32
  · rw [if_pos h, if_pos h]; unfold ctOf
    rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega)]
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- Lanes of the SampleInBall seed state of `c̃`. -/
theorem laneOf_ctSeed {cd : ByteArray} (hcd : 1344 ≤ cd.size) {x : Nat} (hx : x < 25) :
    laneOf (seedState 136 (ctOf cd)) x =
      if x < 4 then le64 cd (CTOFF + 8 * x) else if x = 4 then 31
      else if x = 16 then 2 ^ 63 else 0 := by
  rw [laneOf_seedState (by norm_num)]
  have hb := fun i (hi : i < 136) => byteAt_padCt hcd (i := i) hi
  by_cases h4 : x < 4
  · rw [if_pos (by norm_num; omega), if_pos h4]
    apply le64_congr
    intro k hk
    rw [hb _ (by omega), if_pos (by omega), CTOFF, Nat.add_assoc]
  rw [if_neg h4]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), le64_eq]
    by_cases hx4 : x = 4
    · subst hx4
      simp only [hb _ (by norm_num : 32 < 136), hb _ (by norm_num : 32 + 1 < 136),
        hb _ (by norm_num : 32 + 2 < 136), hb _ (by norm_num : 32 + 3 < 136),
        hb _ (by norm_num : 32 + 4 < 136), hb _ (by norm_num : 32 + 5 < 136),
        hb _ (by norm_num : 32 + 6 < 136), hb _ (by norm_num : 32 + 7 < 136)]
      norm_num
    · by_cases hx16 : x = 16
      · subst hx16
        simp only [hb _ (by norm_num : 128 < 136), hb _ (by norm_num : 128 + 1 < 136),
          hb _ (by norm_num : 128 + 2 < 136), hb _ (by norm_num : 128 + 3 < 136),
          hb _ (by norm_num : 128 + 4 < 136), hb _ (by norm_num : 128 + 5 < 136),
          hb _ (by norm_num : 128 + 6 < 136), hb _ (by norm_num : 128 + 7 < 136)]
        norm_num
      · have hz : ∀ k, k < 8 → byteAt (Fips202.pad 136 0x1F (ctOf cd)) (8 * x + k) = 0 :=
          fun k hk => by
            rw [hb _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [show 8 * x = 8 * x + 0 from rfl, hz 0 (by omega), hz 1 (by omega), hz 2 (by omega),
          hz 3 (by omega), hz 4 (by omega), hz 5 (by omega), hz 6 (by omega), hz 7 (by omega),
          if_neg hx4, if_neg hx16]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega)]

/-! ## `ginit` -/

theorem ones_sub_il {a : Nat → Nat} (h : ∀ k, k < 4 → a k < 2 ^ 64) :
    2 ^ 256 - 1 - il a = il fun k => 2 ^ 64 - 1 - a k := by
  have key : ∀ x : BitVec 256, ~~~x = x ^^^ BitVec.allOnes 256 := fun x => BitVec.xor_allOnes.symm
  have hX := il_lt a
  have h1 : (~~~(BitVec.ofNat 256 (il a))).toNat = 2 ^ 256 - 1 - il a := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hX]
  have h2 : ((BitVec.ofNat 256 (il a)) ^^^ BitVec.allOnes 256).toNat = il a ^^^ (2 ^ 256 - 1) := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hX, BitVec.toNat_allOnes]
  have h3 : (2 ^ 256 - 1 : Nat) = il fun _ => M64 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_two_pow_sub_one, testBit_il]
    by_cases hi : i < 256
    · have : M64.testBit (i / 4) = true := by
        unfold M64; rw [Nat.testBit_two_pow_sub_one]; simp; omega
      simp [hi, this]
    · simp [hi]
  rw [← h1, key, h2, h3, il_xor]
  exact il_congr fun k hk => (sub_eq_xor_M64 (h k hk)).symm

theorem il_eq_zero {a : Nat → Nat} (h : ∀ k, k < 4 → a k = 0) : il a = 0 :=
  (il_congr h).trans il_zero

/-- A slot's fresh lane `x` before complementing: ρ lanes (slots of `amult`),
c̃ lanes (slots of `cmult`), lane 4 from `l4`, the final padding bit. -/
def freshLane (amult cmult : Nat) (ρ c L : Nat → Nat) (k x : Nat) : Nat :=
  (if x < 4 then (if amult.testBit k then ρ x else 0) ^^^ (if cmult.testBit k then c x else 0) else 0) ^^^
    (if x = 4 then L k else 0) ^^^ (if x = 16 ∧ cmult.testBit k = true then 2 ^ 63 else 0) ^^^
    (if x = 20 ∧ amult.testBit k = true then 2 ^ 63 else 0)

theorem freshLane_lt {amult cmult : Nat} {ρ c L : Nat → Nat} {k x : Nat} (hρ : ρ x < 2 ^ 64)
    (hc : c x < 2 ^ 64) (hL : L k < 2 ^ 64) : freshLane amult cmult ρ c L k x < 2 ^ 64 := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  have z : (0 : Nat) < 2 ^ 64 := by norm_num
  have e : ∀ (p : Prop) [Decidable p] (a : Nat), a < 2 ^ 64 → (if p then a else 0) < 2 ^ 64 :=
    fun p _ a ha => by split <;> omega
  unfold freshLane
  refine xor_lt64 (xor_lt64 (xor_lt64 ?_ (e _ _ hL)) (e _ _ h63)) (e _ _ h63)
  split
  · exact xor_lt64 (e _ _ hρ) (e _ _ hc)
  · exact z

/-- The word `ginit` stores at lane `x`: kept slots (`kmask`) carry `cur`,
fresh slots their complemented `freshLane`. -/
theorem ginitWord_eq {m : ByteArray} {keep amult cmult kmask l4 : Nat} {ρ c L : Nat → Nat}
    {cur : Nat → Nat} {x : Nat}
    (ha : amult < 16) (hc : cmult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hρw : x < 4 → word m (RHO1 + 32 * x) = spread (ρ x))
    (hcw : x < 4 → word m (RHO1 + 32 * (4 + x)) = spread (c x))
    (hks : word m (KS + 32 * x) &&& keep = il fun k => if kmask.testBit k then cur k else 0)
    (hρ : ρ x < 2 ^ 64) (hcl : c x < 2 ^ 64) (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true →
      amult.testBit k = false ∧ cmult.testBit k = false ∧ L k = 0) :
    ginitWord m keep amult cmult l4 x =
      il fun k => if kmask.testBit k then cur k else cpl x (freshLane amult cmult ρ c L k x) := by
  have hd0 : (if x < 4 then
      (word m (RHO1 + 32 * x) * amult % 2 ^ 256) ^^^ (word m (RHO1 + 32 * (4 + x)) * cmult % 2 ^ 256)
      else 0) = il fun k => if x < 4 then
        (if amult.testBit k then ρ x else 0) ^^^ (if cmult.testBit k then c x else 0) else 0 := by
    by_cases hx : x < 4
    · rw [if_pos hx, hρw hx, hcw hx, spread_mul _ ha, spread_mul _ hc,
        Nat.mod_eq_of_lt (il_lt _), Nat.mod_eq_of_lt (il_lt _), il_xor]
      exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd1 : (if x = 4 then l4 else 0) = il fun k => if x = 4 then L k else 0 := by
    by_cases hx : x = 4
    · rw [if_pos hx, hl4]; exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd2 : (if x = 16 then padTop * cmult % 2 ^ 256 else 0) =
      il fun k => if x = 16 ∧ cmult.testBit k = true then 2 ^ 63 else 0 := by
    by_cases hx : x = 16
    · rw [if_pos hx, padTop, spread_mul _ hc, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by simp [hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  have hd3 : (if x = 20 then padTop * amult % 2 ^ 256 else 0) =
      il fun k => if x = 20 ∧ amult.testBit k = true then 2 ^ 63 else 0 := by
    by_cases hx : x = 20
    · rw [if_pos hx, padTop, spread_mul _ ha, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by simp [hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  have hd4 : (if x ∈ complemented then 2 ^ 256 - 1 - keep else 0) =
      il fun k => if x ∈ complemented ∧ kmask.testBit k = false then M64 else 0 := by
    by_cases hx : x ∈ complemented
    · rw [if_pos hx, hkeep, ones_sub_il (fun k _ => by split <;> simp [M64])]
      exact il_congr fun k _ => by
        cases hkk : kmask.testBit k <;> simp [hx, M64]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  unfold ginitWord
  simp only
  rw [hd0, hd1, hd2, hd3, hd4, hks, il_xor, il_xor, il_xor, il_xor, il_or]
  apply il_congr
  intro k hk
  cases hkk : kmask.testBit k
  · have hf := freshLane_lt (amult := amult) (cmult := cmult) (k := k) hρ hcl (hL k hk)
    rw [cpl_eq hf]
    simp only [Bool.false_eq_true, if_false, Nat.or_zero]
    unfold freshLane
    by_cases hx : x ∈ complemented
    · simp only [hx, true_and, if_true]
    · simp only [hx, false_and, if_false, Nat.xor_zero]
  · obtain ⟨h1, h2, h3⟩ := hdisj k hk hkk
    simp only [h1, h2, h3, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false, and_false,
      Nat.xor_zero, ite_self, Nat.zero_or]

/-- `KS[x] &&& 0`. -/
theorem and_keep0 (w : Nat) : w &&& 0 = il fun k => if (0 : Nat).testBit k then w else 0 := by
  rw [Nat.and_zero, il_eq_zero fun k _ => by simp]

/-- `KS4` keeps slot `3` under the `keep` mask `0x8888…`. -/
theorem and_keep3 {v : Nat → Nat} (hv : ∀ k, k < 4 → v k < 2 ^ 64) :
    il v &&& (il fun k => if (8 : Nat).testBit k then M64 else 0) =
      il fun k => if (8 : Nat).testBit k then v k else 0 := by
  rw [il_and]
  apply il_congr; intro k hk
  split
  · rw [show M64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hv k hk)]
  · exact Nat.and_zero _

/-- `ginit` of a pure ExpandA group (`group`): slot `k` is the seed of `A[k][col]`. -/
theorem ginit_group {m cd : ByteArray}
    (hrho : ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 cd (8 * x)) ∧
      word m (RHO1 + 32 * (4 + x)) = spread (le64 cd (CTOFF + 8 * x)))
    (hcd : 32 ≤ cd.size) {col : Nat} (hcol : col < 4) {x : Nat} (hx : x < 25) :
    ginitWord m 0 15 0 (il fun k => col + 256 * k + 0x1F * 65536) x =
      il fun k => cpl x (laneOf (seedState 168 (aSeed cd k col)) x) := by
  rw [ginitWord_eq (kmask := 0) (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x))
    (cur := fun _ => 0) (by norm_num) (by norm_num)
    (il_eq_zero fun k _ => by simp).symm rfl
    (fun h => (hrho x h).1) (fun h => (hrho x h).2) (and_keep0 _) (le64_lt _ _) (le64_lt _ _)
    (fun k hk => by omega) (fun k _ h => by simp at h)]
  apply il_congr; intro k hk
  rw [laneOf_aSeed hcd (by omega) (by omega) hx]
  have h15 : (15 : Nat).testBit k = true := by interval_cases k <;> decide
  simp only [Nat.zero_testBit, Bool.false_eq_true, if_false, freshLane, h15, if_true, Nat.xor_zero,
    and_false, and_true]
  congr 1
  by_cases h4 : x < 4
  · simp [h4, show x ≠ 4 by omega, show x ≠ 20 by omega]
  · by_cases h5 : x = 4
    · subst h5; simp
    · by_cases h6 : x = 20
      · subst h6; simp
      · simp [h4, h5, h6]

end MlDsaOpt44.Proofs
