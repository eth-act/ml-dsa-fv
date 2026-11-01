import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Mu0
import MlDsaOpt44.Math.Sponge
import MlDsaOpt44.Math.SpongeG234
set_option warningAsError true
/-!
# Sponge facts for the mixed SIMD groups 5–8 (ML-DSA-65, WP S4)

The ML-DSA-65 counterparts of `MlDsaOpt44/Math/SpongeG234.lean` /
`SpongeSeed.lean`: the `ginit` word of ML-DSA-65 (six c̃ lanes, c̃'s domain
byte in lane 6) as fresh / kept slots (`S4.ks4_ginit`), the c̃ seed state
(48 bytes), the padded public key (1952 bytes, 15 blocks, the last one with
48 data bytes), `tr`, the c̃ stream `H(c̃)` and the short-message μ as lanes of
permuted states.
-/

namespace MlDsaOpt65.Proofs.S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44

/-! ## `ginit` (ML-DSA-65) -/

/-- A slot's fresh lane `x` before complementing (ML-DSA-65 `ginit`). -/
def freshLane (amult cmult : Nat) (ρ c L : Nat → Nat) (k x : Nat) : Nat :=
  (if x < 4 then (if amult.testBit k then ρ x else 0) else 0) ^^^
    (if x < 6 then (if cmult.testBit k then c x else 0) else 0) ^^^
    (if x = 4 then L k else 0) ^^^ (if x = 6 ∧ cmult.testBit k = true then 0x1F else 0) ^^^
    (if x = 16 ∧ cmult.testBit k = true then 2 ^ 63 else 0) ^^^
    (if x = 20 ∧ amult.testBit k = true then 2 ^ 63 else 0)

theorem freshLane_lt {amult cmult : Nat} {ρ c L : Nat → Nat} {k x : Nat} (hρ : ρ x < 2 ^ 64)
    (hc : c x < 2 ^ 64) (hL : L k < 2 ^ 64) : freshLane amult cmult ρ c L k x < 2 ^ 64 := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  have h31 : (0x1F : Nat) < 2 ^ 64 := by norm_num
  have e : ∀ (p : Prop) [Decidable p] (a : Nat), a < 2 ^ 64 → (if p then a else 0) < 2 ^ 64 :=
    fun p _ a ha => by split <;> omega
  unfold freshLane
  exact xor_lt64 (xor_lt64 (xor_lt64 (xor_lt64 (xor_lt64 (e _ _ (e _ _ hρ)) (e _ _ (e _ _ hc)))
    (e _ _ hL)) (e _ _ h31)) (e _ _ h63)) (e _ _ h63)

theorem ginitWord_eq {m : ByteArray} {keep amult cmult kmask l4 : Nat} {ρ c L : Nat → Nat}
    {cur : Nat → Nat} {x : Nat}
    (ha : amult < 16) (hc : cmult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hρw : x < 4 → word m (RHO1 + 32 * x) = spread (ρ x))
    (hcw : x < 6 → word m (RHO1 + 32 * (4 + x)) = spread (c x))
    (hks : word m (KS + 32 * x) &&& keep = il fun k => if kmask.testBit k then cur k else 0)
    (hρ : ρ x < 2 ^ 64) (hcl : c x < 2 ^ 64) (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true →
      amult.testBit k = false ∧ cmult.testBit k = false ∧ L k = 0) :
    ginitWord m keep amult cmult l4 x =
      il fun k => if kmask.testBit k then cur k else cpl x (freshLane amult cmult ρ c L k x) := by
  have hda : (if x < 4 then word m (RHO1 + 32 * x) * amult % 2 ^ 256 else 0) =
      il fun k => if x < 4 then (if amult.testBit k then ρ x else 0) else 0 := by
    by_cases hx : x < 4
    · rw [if_pos hx, hρw hx, spread_mul _ ha, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hdc : (if x < 6 then word m (RHO1 + 32 * (4 + x)) * cmult % 2 ^ 256 else 0) =
      il fun k => if x < 6 then (if cmult.testBit k then c x else 0) else 0 := by
    by_cases hx : x < 6
    · rw [if_pos hx, hcw hx, spread_mul _ hc, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd1 : (if x = 4 then l4 else 0) = il fun k => if x = 4 then L k else 0 := by
    by_cases hx : x = 4
    · rw [if_pos hx, hl4]; exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd5 : (if x = 6 then spread 0x1F * cmult % 2 ^ 256 else 0) =
      il fun k => if x = 6 ∧ cmult.testBit k = true then 0x1F else 0 := by
    by_cases hx : x = 6
    · rw [if_pos hx, spread_mul _ hc, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by simp [hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  have hd2 : (if x = 16 then spread (2 ^ 63) * cmult % 2 ^ 256 else 0) =
      il fun k => if x = 16 ∧ cmult.testBit k = true then 2 ^ 63 else 0 := by
    by_cases hx : x = 16
    · rw [if_pos hx, spread_mul _ hc, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by simp [hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  have hd3 : (if x = 20 then spread (2 ^ 63) * amult % 2 ^ 256 else 0) =
      il fun k => if x = 20 ∧ amult.testBit k = true then 2 ^ 63 else 0 := by
    by_cases hx : x = 20
    · rw [if_pos hx, spread_mul _ ha, Nat.mod_eq_of_lt (il_lt _)]
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
  rw [hda, hdc, hd1, hd5, hd2, hd3, hd4, hks, il_xor, il_xor, il_xor, il_xor, il_xor, il_xor, il_or]
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

/-- The state `ginit` builds (ML-DSA-65): kept slots (`kmask`) carry `S`, fresh
slots the states whose lanes are their `freshLane`s. -/
theorem ks4_ginit {m m' : ByteArray} {keep amult cmult kmask l4 : Nat} {ρ c L : Nat → Nat}
    {S I : Nat → Fips202.SpongeState}
    (ha : amult < 16) (hc : cmult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hρw : ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (ρ x))
    (hcw : ∀ x, x < 6 → word m (RHO1 + 32 * (4 + x)) = spread (c x))
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hρ : ∀ x, ρ x < 2 ^ 64) (hcl : ∀ x, c x < 2 ^ 64) (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true →
      amult.testBit k = false ∧ cmult.testBit k = false ∧ L k = 0)
    (hkept : ∀ k, k < 4 → kmask.testBit k = true → I k = S k)
    (hfresh : ∀ k, k < 4 → kmask.testBit k = false → ∀ x, x < 25 →
      freshLane amult cmult ρ c L k x = laneOf (I k) x)
    (hm' : ∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) :
    KS4 m' I := by
  intro x hx
  rw [hm' x hx, ginitWord_eq ha hc hkeep hl4 (hρw x) (hcw x) (hand x hx) (hρ x) (hcl x) hL hdisj]
  apply il_congr; intro k hk
  cases hkk : kmask.testBit k
  · simp only [Bool.false_eq_true, if_false]; rw [hfresh k hk hkk x hx]
  · simp only [if_true]; rw [hkept k hk hkk]

theorem freshLane_aSeed {cd : ByteArray} (hcd : 32 ≤ cd.size) {amult cmult : Nat} {ρ c L : Nat → Nat}
    (hρ : ∀ x, x < 4 → ρ x = le64 cd (8 * x)) {k r col : Nat} (hr : r < 256) (hcol : col < 256)
    (ha : amult.testBit k = true) (hc : cmult.testBit k = false) (hL : L k = col + 256 * r + 0x1F0000)
    {x : Nat} (hx : x < 25) :
    freshLane amult cmult ρ c L k x = laneOf (seedState 168 (aSeed cd r col)) x := by
  rw [laneOf_aSeed hcd hr hcol hx]
  unfold freshLane
  simp only [ha, hc, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, ite_self, and_false,
    and_true]
  by_cases h4 : x < 4
  · simp [h4, show x ≠ 4 by omega, show x ≠ 20 by omega, hρ x h4]
  · by_cases h5 : x = 4
    · subst h5; simp [hL]
    · by_cases h6 : x = 20
      · subst h6; simp
      · simp [h4, h5, h6]

theorem freshLane_zero {amult cmult : Nat} {ρ c L : Nat → Nat} {k : Nat}
    (ha : amult.testBit k = false) (hc : cmult.testBit k = false) (hL : L k = 0) (x : Nat) :
    freshLane amult cmult ρ c L k x = laneOf Fips202.emptyState x := by
  rw [laneOf_emptyState]
  unfold freshLane
  simp [ha, hc, hL]

/-! ## The c̃ seed (48 bytes) -/

theorem ctOf_size {cd : ByteArray} (hcd : Z0 ≤ cd.size) : (ctOf cd).size = 48 := by
  unfold ctOf Z0 CTOFF at *; simp [ByteArray.size_extract]; omega

theorem byteAt_padCt {cd : ByteArray} (hcd : Z0 ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (Fips202.pad 136 0x1F (ctOf cd)) i =
      if i < 48 then byteAt cd (1952 + i) else if i = 48 then 31 else if i = 135 then 128 else 0 := by
  rw [byteAt_pad1 136 _ (by rw [ctOf_size hcd]; omega) i hi, ctOf_size hcd]
  by_cases h : i < 48
  · rw [if_pos h, if_pos h]; unfold ctOf
    rw [byteAt_extract _ _ _ _ (by unfold Z0 at hcd; exact hcd), if_pos (by unfold Z0 CTOFF; omega)]
    rfl
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- Lanes of the SampleInBall seed state of `c̃` (ML-DSA-65: six lanes). -/
theorem laneOf_ctSeed {cd : ByteArray} (hcd : Z0 ≤ cd.size) {x : Nat} (hx : x < 25) :
    laneOf (seedState 136 (ctOf cd)) x =
      if x < 6 then le64 cd (CTOFF + 8 * x) else if x = 6 then 31
      else if x = 16 then 2 ^ 63 else 0 := by
  rw [laneOf_seedState (by norm_num)]
  have hb := fun i (hi : i < 136) => byteAt_padCt hcd (i := i) hi
  by_cases h6 : x < 6
  · rw [if_pos (by norm_num; omega), if_pos h6]
    apply le64_congr
    intro k hk
    rw [hb _ (by omega), if_pos (by omega), CTOFF, Nat.add_assoc]
  rw [if_neg h6]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), le64_eq]
    by_cases hx6 : x = 6
    · subst hx6
      simp only [hb _ (by norm_num : 48 < 136), hb _ (by norm_num : 48 + 1 < 136),
        hb _ (by norm_num : 48 + 2 < 136), hb _ (by norm_num : 48 + 3 < 136),
        hb _ (by norm_num : 48 + 4 < 136), hb _ (by norm_num : 48 + 5 < 136),
        hb _ (by norm_num : 48 + 6 < 136), hb _ (by norm_num : 48 + 7 < 136)]
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
          if_neg hx6, if_neg hx16]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega)]

theorem freshLane_ctSeed {cd : ByteArray} (hcd : Z0 ≤ cd.size) {amult cmult : Nat}
    {ρ c L : Nat → Nat} (hcw : ∀ x, x < 6 → c x = le64 cd (CTOFF + 8 * x)) {k : Nat}
    (ha : amult.testBit k = false) (hc : cmult.testBit k = true) (hL : L k = 0)
    {x : Nat} (hx : x < 25) :
    freshLane amult cmult ρ c L k x = laneOf (seedState 136 (ctOf cd)) x := by
  rw [laneOf_ctSeed hcd hx]
  unfold freshLane
  simp only [ha, hc, hL, if_true, Bool.false_eq_true, if_false, Nat.zero_xor, Nat.xor_zero,
    and_false, and_true, ite_self]
  by_cases h6 : x < 6
  · simp [h6, show x ≠ 6 by omega, show x ≠ 16 by omega, hcw x h6]
  · by_cases h5 : x = 6
    · subst h5; simp
    · by_cases h16 : x = 16
      · subst h16; simp
      · simp [h6, h5, h16]

/-! ## The padded public key (1952 bytes, 15 blocks) -/

theorem lm_top2 : (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 : Nat) =
    pack4 fun k => if 4 - 2 ≤ k then M64 else 0 := by
  unfold pack4 M64; norm_num

theorem pkOf_size {cd : ByteArray} (hcd : CTOFF ≤ cd.size) : (pkOf cd).size = 1952 := by
  unfold pkOf CTOFF at *; simp [ByteArray.size_extract]; omega

theorem le64_padPk_full {cd : ByteArray} (hcd : CTOFF ≤ cd.size) {a : Nat} (ha : a + 8 ≤ 1952) :
    le64 (Fips202.pad 136 0x1F (pkOf cd)) a = le64 cd a := by
  apply le64_congr
  intro k hk
  rw [byteAt_pad_lt _ _ _ (by rw [pkOf_size hcd]; omega)]
  unfold pkOf
  rw [byteAt_extract _ _ _ _ hcd, if_pos (by unfold CTOFF; omega), Nat.zero_add]

theorem byteAt_padPk_last {cd : ByteArray} (hcd : CTOFF ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (Fips202.pad 136 0x1F (pkOf cd)) (1904 + i) =
      if i < 48 then byteAt cd (1904 + i) else if i = 48 then 31 else if i = 135 then 128 else 0 := by
  have := byteAt_pad_last 136 (pkOf cd) (by norm_num) i hi
  rw [pkOf_size hcd] at this
  norm_num at this
  rw [this]
  by_cases h : i < 48
  · rw [if_pos h, if_pos h]; unfold pkOf
    rw [byteAt_extract _ _ _ _ hcd, if_pos (by unfold CTOFF; omega), Nat.zero_add]
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- The last block of the padded public key (block 14). -/
theorem le64_padPk_last {cd : ByteArray} (hcd : CTOFF ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (Fips202.pad 136 0x1F (pkOf cd)) (1904 + 8 * x) =
      if x < 6 then le64 cd (1904 + 8 * x) else if x = 6 then 31 else if x = 16 then 2 ^ 63 else 0 := by
  have hb := fun i (hi : i < 136) => byteAt_padPk_last hcd (i := i) hi
  by_cases h6 : x < 6
  · rw [if_pos h6]
    apply le64_congr
    intro k hk
    rw [Nat.add_assoc, hb _ (by omega), if_pos (by omega)]
  rw [if_neg h6, le64_eq]
  have hk : ∀ k, k < 8 → byteAt (Fips202.pad 136 0x1F (pkOf cd)) (1904 + 8 * x + k) =
      if 8 * x + k < 48 then byteAt cd (1904 + (8 * x + k)) else if 8 * x + k = 48 then 31
      else if 8 * x + k = 135 then 128 else 0 := fun k hk => by
    rw [Nat.add_assoc]; exact hb _ (by omega)
  rw [show 1904 + 8 * x = 1904 + 8 * x + 0 from rfl, hk 0 (by omega), hk 1 (by omega),
    hk 2 (by omega), hk 3 (by omega), hk 4 (by omega), hk 5 (by omega), hk 6 (by omega),
    hk 7 (by omega)]
  by_cases hx6 : x = 6
  · subst hx6; norm_num
  · by_cases hx16 : x = 16
    · subst hx16; norm_num
    · rw [if_neg hx6, if_neg hx16]
      have z : ∀ k, k < 8 → (if 8 * x + k < 48 then byteAt cd (1904 + (8 * x + k))
          else if 8 * x + k = 48 then 31 else if 8 * x + k = 135 then 128 else 0) = 0 := fun k hk => by
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [z 0 (by omega), z 1 (by omega), z 2 (by omega), z 3 (by omega), z 4 (by omega),
        z 5 (by omega), z 6 (by omega), z 7 (by omega)]

theorem padPk_size {cd : ByteArray} (hcd : CTOFF ≤ cd.size) :
    (Fips202.pad 136 0x1F (pkOf cd)).size = 15 * 136 := by
  rw [pad_size _ _ (by norm_num), pkOf_size hcd]

/-! ## Output lanes -/

theorem trOf_size (cd : ByteArray) : (trOf cd).size = 64 := H_size _ _

/-- `tr = H(pk, 64)`: lane `x` of the state after the fifteen absorbed blocks. -/
theorem le64_trOf {cd : ByteArray} (hcd : CTOFF ≤ cd.size) {x : Nat} (hx : x < 8) :
    le64 (trOf cd) (8 * x) = laneOf (absorbPre 136 (Fips202.pad 136 0x1F (pkOf cd)) 15) x := by
  unfold trOf MlDsa.Fips204.H Fips202.shake256
  have := le64_shake256 (pkOf cd) (n := 64) (j := 0) (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this, Function.iterate_zero_apply, absorb_eq 136 _ 15 (by norm_num) (padPk_size hcd)]

/-- The SampleInBall stream: lanes of the first two squeezed blocks of `c̃`'s seed state. -/
theorem le64_cStream {cd : ByteArray} (hcd : Z0 ≤ cd.size) {j x : Nat} (hj : j < 2) (hx : x < 17) :
    le64 (cStream cd) (8 * (17 * j + x)) = laneOf (permN (j + 1) (seedState 136 (ctOf cd))) x := by
  unfold cStream MlDsa.Fips204.H Fips202.shake256
  rw [le64_shake256 _ hx (by unfold MlDsa.Fips204.sampleInBallLimit; omega),
    absorb_single (by norm_num) (by rw [ctOf_size hcd]; omega)]
  unfold permN
  rw [Function.iterate_succ_apply]

/-- μ's input `tr ‖ 0 ‖ 0 ‖ M`. -/
def muMsg (cd : ByteArray) : ByteArray := trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)

/-- The message representative of a short message. -/
theorem le64_muOf {cd : ByteArray} (hm : mlenOf cd ≤ 69) {x : Nat} (hx : x < 8) :
    le64 (muOf cd) (8 * x) = laneOf (permN 1 (seedState 136 (muMsg cd))) x := by
  have hs : (muMsg cd).size < 136 := by
    unfold muMsg
    rw [ByteArray.size_append, ByteArray.size_append, trOf_size,
      show (ByteArray.mk #[(0 : UInt8), 0]).size = 2 from rfl]
    unfold msgOf mlenOf at *
    simp [ByteArray.size_extract]
    omega
  unfold muOf MlDsa.Fips204.H Fips202.shake256
  have := le64_shake256 (muMsg cd) (n := 64) (j := 0) (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [show trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd) = muMsg cd from rfl, this,
    Function.iterate_zero_apply, absorb_single (by norm_num) hs]
  rfl

/-- Lanes of μ's seed state are the lanes of `muBlock`. -/
theorem laneOf_muSeed (cd : ByteArray) {x : Nat} :
    laneOf (seedState 136 (muMsg cd)) x =
      if x < 17 then le64 (MlDsaOpt65.Proofs.muBlock (trOf cd) cd) (8 * x) else 0 := by
  rw [laneOf_seedState (by norm_num)]
  rfl

end MlDsaOpt65.Proofs.S4
