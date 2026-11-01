import MlDsaOpt44.Math.SpongeSeed
set_option warningAsError true
/-!
# Sponge facts for the three mixed SIMD groups (`seg_g234`)

* `ks4_xor_slot`: xoring spread lanes into one slot of a `KS4` state;
  `ks4_ginit`: the state `ginit` builds from fresh / kept slots, with
  `freshLane_aSeed`, `freshLane_ctSeed`, `freshLane_zero` for the slot kinds.
* `cext_lane`: `cext` reads a slot's lanes back.
* `trLane_*`: the calldata lanes `trabs` absorbs; `le64_padPk_*`: the lanes of
  the padded public key; `le64_trOf`: `tr` is lane-wise the state after ten
  absorbed blocks.
* `le64_cStream`, `le64_muOf`: `H(c̃)` and the short-message μ are lanes of
  permuted single-block seed states.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44

theorem cpl_cpl {x v : Nat} (hv : v < 2 ^ 64) : cpl x (cpl x v) = v := by
  unfold cpl; split <;> omega

theorem cpl_xor {x v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) : cpl x v ^^^ w = cpl x (v ^^^ w) := by
  rw [cpl_eq hv, cpl_eq (xor_lt64 hv hw)]
  split
  · rw [Nat.xor_assoc, Nat.xor_comm M64 w, ← Nat.xor_assoc]
  · rfl

/-! ## `KS4` transformations -/

/-- Xoring `spread (t x) · 2^sh` into every lane changes slot `sh` to `T'`. -/
theorem ks4_xor_slot {m m' : ByteArray} {S : Nat → Fips202.SpongeState} {sh : Nat} (hsh : sh < 4)
    (hks : KS4 m S) (t : Nat → Nat) (ht : ∀ x, x < 25 → t x < 2 ^ 64)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) = word m (KS + 32 * x) ^^^ spread (t x) * 2 ^ sh)
    (T' : Fips202.SpongeState) (hT : ∀ x, x < 25 → laneOf T' x = laneOf (S sh) x ^^^ t x) :
    KS4 m' fun k => if k = sh then T' else S k := by
  intro x hx
  rw [hw x hx, hks x hx, spread_mul_two_pow _ hsh, il_xor]
  apply il_congr
  intro k _
  by_cases hk : k = sh
  · subst hk
    simp only [if_true]
    rw [cpl_xor (laneOf_lt _ _) (ht x hx), hT x hx]
  · simp only [hk, if_false, Nat.xor_zero]

/-- The state `ginit` builds: kept slots (`kmask`) carry `S`, fresh slots the
states whose lanes are their `freshLane`s. -/
theorem ks4_ginit {m m' : ByteArray} {keep amult cmult kmask l4 : Nat} {ρ c L : Nat → Nat}
    {S I : Nat → Fips202.SpongeState}
    (ha : amult < 16) (hc : cmult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hρw : ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (ρ x))
    (hcw : ∀ x, x < 4 → word m (RHO1 + 32 * (4 + x)) = spread (c x))
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

/-- `KS[x] &&& keep` when `keep` masks the slots `kmask` of a `KS4` state. -/
theorem ks4_and_keep {m : ByteArray} {S : Nat → Fips202.SpongeState} (hks : KS4 m S) (kmask : Nat)
    {x : Nat} (hx : x < 25) :
    word m (KS + 32 * x) &&& (il fun k => if kmask.testBit k then M64 else 0) =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0 := by
  rw [hks x hx, il_and]
  apply il_congr; intro k _
  split
  · rw [show M64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (cpl_lt (laneOf_lt _ _))]
  · exact Nat.and_zero _

theorem freshLane_aSeed {cd : ByteArray} (hcd : 32 ≤ cd.size) {amult cmult : Nat} {ρ c L : Nat → Nat}
    (hρ : ∀ x, x < 4 → ρ x = le64 cd (8 * x)) {k r col : Nat} (hr : r < 256) (hcol : col < 256)
    (ha : amult.testBit k = true) (hc : cmult.testBit k = false) (hL : L k = col + 256 * r + 0x1F0000)
    {x : Nat} (hx : x < 25) :
    freshLane amult cmult ρ c L k x = laneOf (seedState 168 (aSeed cd r col)) x := by
  rw [laneOf_aSeed hcd hr hcol hx]
  unfold freshLane
  simp only [ha, hc, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, and_false, and_true]
  by_cases h4 : x < 4
  · simp [h4, show x ≠ 4 by omega, show x ≠ 20 by omega, hρ x h4]
  · by_cases h5 : x = 4
    · subst h5; simp [hL]
    · by_cases h6 : x = 20
      · subst h6; simp
      · simp [h4, h5, h6]

theorem freshLane_ctSeed {cd : ByteArray} (hcd : 1344 ≤ cd.size) {amult cmult : Nat}
    {ρ c L : Nat → Nat} (hcw : ∀ x, x < 4 → c x = le64 cd (CTOFF + 8 * x)) {k : Nat}
    (ha : amult.testBit k = false) (hc : cmult.testBit k = true) (hL : L k = 31)
    {x : Nat} (hx : x < 25) :
    freshLane amult cmult ρ c L k x = laneOf (seedState 136 (ctOf cd)) x := by
  rw [laneOf_ctSeed hcd hx]
  unfold freshLane
  simp only [ha, hc, if_true, Bool.false_eq_true, if_false, Nat.zero_xor, Nat.xor_zero, and_false,
    and_true]
  by_cases h4 : x < 4
  · simp [h4, show x ≠ 4 by omega, show x ≠ 16 by omega, hcw x h4]
  · by_cases h5 : x = 4
    · subst h5; simp [hL]
    · by_cases h6 : x = 16
      · subst h6; simp
      · simp [h4, h5, h6]

theorem freshLane_zero {amult cmult : Nat} {ρ c L : Nat → Nat} {k : Nat}
    (ha : amult.testBit k = false) (hc : cmult.testBit k = false) (hL : L k = 0) (x : Nat) :
    freshLane amult cmult ρ c L k x = laneOf Fips202.emptyState x := by
  rw [laneOf_emptyState]
  unfold freshLane
  simp [ha, hc, hL]

/-! ## `cext` -/

theorem cext_lane {m : ByteArray} {S : Nat → Fips202.SpongeState} (hks : KS4 m S) {sh : Nat}
    (hsh : sh < 4) {x : Nat} (hx : x < 25) :
    cpl x (compress (word m (KS + 32 * x) / 2 ^ sh &&& spread M64)) = laneOf (S sh) x := by
  rw [hks x hx, compress_il _ hsh, Nat.mod_eq_of_lt (cpl_lt (laneOf_lt _ _)), cpl_cpl (laneOf_lt _ _)]

/-! ## `trabs` lanes -/

theorem lane_and (a b k : Nat) : lane (a &&& b) k = lane a k &&& lane b k := by
  apply Nat.eq_of_testBit_eq; intro j
  unfold lane
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  cases decide (j < 64) <;> simp

theorem lane_eq_div (w j : Nat) (hj : j < 4) : w / 2 ^ (192 - 64 * j) % 2 ^ 64 = lane w (3 - j) := by
  unfold lane; congr 3; omega

theorem lane_pack4_lt {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] <;> omega

theorem lane_bsw (cd : ByteArray) (a j : Nat) (hj : j < 4) :
    lane (bsw cd a) (3 - j) = le64 cd (a + 8 * j) := by
  unfold bsw
  rw [lane_pack4_lt (fun k _ => le64_lt _ _) (by omega), show 3 - (3 - j) = j by omega]

/-- `trabs` lanes when the last group keeps its top `r` lanes. -/
theorem trLane_eq (cd : ByteArray) {off n4 r lm u : Nat}
    (hlm : lm = pack4 fun k => if 4 - r ≤ k then M64 else 0) :
    trLane cd off lm n4 u = if u / 4 + 1 = n4 ∧ r ≤ u % 4 then 0 else le64 cd (off + 8 * u) := by
  unfold trLane
  simp only
  have hu : u % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have ha : off + 32 * (u / 4) + 8 * (u % 4) = off + 8 * u := by omega
  split
  · rw [lane_eq_div _ _ hu, lane_and, lane_bsw _ _ _ hu, hlm,
      lane_pack4_lt (fun k _ => by split <;> simp [M64]) (by omega), ha]
    by_cases hr : r ≤ u % 4
    · rw [if_neg (by omega), Nat.and_zero, if_pos ⟨by assumption, hr⟩]
    · rw [if_pos (by omega), show M64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (le64_lt _ _), if_neg (fun h => hr h.2)]
  · rw [lane_eq_div _ _ hu, lane_bsw _ _ _ hu, ha, if_neg (fun h => by simp_all)]

theorem lm_top1 : (0xffffffffffffffff000000000000000000000000000000000000000000000000 : Nat) =
    pack4 fun k => if 4 - 1 ≤ k then M64 else 0 := by
  unfold pack4 M64; norm_num

theorem lm_top3 : (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : Nat) =
    pack4 fun k => if 4 - 3 ≤ k then M64 else 0 := by
  unfold pack4 M64; norm_num

/-! ## The padded public key -/

theorem pkOf_size {cd : ByteArray} (hcd : 1312 ≤ cd.size) : (pkOf cd).size = 1312 := by
  unfold pkOf; simp [ByteArray.size_extract]; omega

/-- Full blocks of the padded public key are calldata lanes. -/
theorem le64_padPk_full {cd : ByteArray} (hcd : 1312 ≤ cd.size) {a : Nat} (ha : a + 8 ≤ 1312) :
    le64 (Fips202.pad 136 0x1F (pkOf cd)) a = le64 cd a := by
  apply le64_congr
  intro k hk
  rw [byteAt_pad_lt _ _ _ (by rw [pkOf_size hcd]; omega)]
  unfold pkOf
  rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]

theorem byteAt_padPk_last {cd : ByteArray} (hcd : 1312 ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (Fips202.pad 136 0x1F (pkOf cd)) (1224 + i) =
      if i < 88 then byteAt cd (1224 + i) else if i = 88 then 31 else if i = 135 then 128 else 0 := by
  have := byteAt_pad_last 136 (pkOf cd) (by norm_num) i hi
  rw [pkOf_size hcd] at this
  norm_num at this
  rw [this]
  by_cases h : i < 88
  · rw [if_pos h, if_pos h]; unfold pkOf
    rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- The last block of the padded public key. -/
theorem le64_padPk_last {cd : ByteArray} (hcd : 1312 ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (Fips202.pad 136 0x1F (pkOf cd)) (1224 + 8 * x) =
      if x < 11 then le64 cd (1224 + 8 * x) else if x = 11 then 31 else if x = 16 then 2 ^ 63 else 0 := by
  have hb := fun i (hi : i < 136) => byteAt_padPk_last hcd (i := i) hi
  by_cases h11 : x < 11
  · rw [if_pos h11]
    apply le64_congr
    intro k hk
    rw [Nat.add_assoc, hb _ (by omega), if_pos (by omega)]
  rw [if_neg h11, le64_eq]
  have h0 : byteAt (Fips202.pad 136 0x1F (pkOf cd)) (1224 + 8 * x) =
      if 8 * x < 88 then byteAt cd (1224 + 8 * x) else if 8 * x = 88 then 31
      else if 8 * x = 135 then 128 else 0 := hb _ (by omega)
  have hk : ∀ k, k < 8 → byteAt (Fips202.pad 136 0x1F (pkOf cd)) (1224 + 8 * x + k) =
      if 8 * x + k < 88 then byteAt cd (1224 + (8 * x + k)) else if 8 * x + k = 88 then 31
      else if 8 * x + k = 135 then 128 else 0 := fun k hk => by
    rw [Nat.add_assoc]; exact hb _ (by omega)
  rw [h0, hk 1 (by omega), hk 2 (by omega), hk 3 (by omega), hk 4 (by omega), hk 5 (by omega),
    hk 6 (by omega), hk 7 (by omega)]
  by_cases hx11 : x = 11
  · subst hx11; norm_num
  · by_cases hx16 : x = 16
    · subst hx16; norm_num
    · rw [if_neg hx11, if_neg hx16]
      simp only [show ¬ 8 * x < 88 by omega, show ¬ 8 * x = 88 by omega, show ¬ 8 * x = 135 by omega,
        show ¬ 8 * x + 1 < 88 by omega, show ¬ 8 * x + 1 = 88 by omega, show ¬ 8 * x + 1 = 135 by omega,
        show ¬ 8 * x + 2 < 88 by omega, show ¬ 8 * x + 2 = 88 by omega, show ¬ 8 * x + 2 = 135 by omega,
        show ¬ 8 * x + 3 < 88 by omega, show ¬ 8 * x + 3 = 88 by omega, show ¬ 8 * x + 3 = 135 by omega,
        show ¬ 8 * x + 4 < 88 by omega, show ¬ 8 * x + 4 = 88 by omega, show ¬ 8 * x + 4 = 135 by omega,
        show ¬ 8 * x + 5 < 88 by omega, show ¬ 8 * x + 5 = 88 by omega, show ¬ 8 * x + 5 = 135 by omega,
        show ¬ 8 * x + 6 < 88 by omega, show ¬ 8 * x + 6 = 88 by omega, show ¬ 8 * x + 6 = 135 by omega,
        show ¬ 8 * x + 7 < 88 by omega, show ¬ 8 * x + 7 = 88 by omega, show ¬ 8 * x + 7 = 135 by omega,
        if_false]

theorem padPk_size {cd : ByteArray} (hcd : 1312 ≤ cd.size) :
    (Fips202.pad 136 0x1F (pkOf cd)).size = 10 * 136 := by
  rw [pad_size _ _ (by norm_num), pkOf_size hcd]

/-! ## Output lanes -/

theorem H_size (msg : ByteArray) (n : Nat) : (Fips204.H msg n).size = n := by
  unfold Fips204.H Fips202.shake256 Fips202.shake
  have := MlDsa44.Proofs.Math.squeeze_size' 136
    (Fips202.absorb 136 (Fips202.pad 136 0x1F msg)) ((n + 136 - 1) / 136)
  simp only [ByteArray.size_extract, this]
  omega

theorem trOf_size (cd : ByteArray) : (trOf cd).size = 64 := H_size _ _

/-- `tr = H(pk, 64)`: lane `x` is lane `x` of the state after the ten absorbed
blocks of the padded public key. -/
theorem le64_trOf {cd : ByteArray} (hcd : 1312 ≤ cd.size) {x : Nat} (hx : x < 8) :
    le64 (trOf cd) (8 * x) = laneOf (absorbPre 136 (Fips202.pad 136 0x1F (pkOf cd)) 10) x := by
  unfold trOf Fips204.H Fips202.shake256
  have := le64_shake256 (pkOf cd) (n := 64) (j := 0) (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this, Function.iterate_zero_apply, absorb_eq 136 _ 10 (by norm_num) (padPk_size hcd)]

/-- The SampleInBall stream: lanes of the first two squeezed blocks of `c̃`'s
seed state. -/
theorem le64_cStream {cd : ByteArray} (hcd : 1344 ≤ cd.size) {j x : Nat} (hj : j < 2) (hx : x < 17) :
    le64 (cStream cd) (8 * (17 * j + x)) = laneOf (permN (j + 1) (seedState 136 (ctOf cd))) x := by
  unfold cStream Fips204.H Fips202.shake256
  rw [le64_shake256 _ hx (by unfold Fips204.sampleInBallLimit; omega),
    absorb_single (by norm_num) (by rw [ctOf_size hcd]; omega)]
  unfold permN
  rw [Function.iterate_succ_apply]

/-- The message representative of a short message: lanes of the permuted seed
state of `tr ‖ 0 ‖ 0 ‖ M`. -/
theorem le64_muOf {cd : ByteArray} (hm : mlenOf cd ≤ 69) {x : Nat}
    (hx : x < 8) :
    le64 (muOf cd) (8 * x) =
      laneOf (permN 1 (seedState 136 (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)))) x := by
  have hs : (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size < 136 := by
    rw [ByteArray.size_append, ByteArray.size_append, trOf_size,
      show (ByteArray.mk #[(0 : UInt8), 0]).size = 2 from rfl]
    unfold msgOf mlenOf at *
    simp [ByteArray.size_extract]
    omega
  unfold muOf Fips204.H Fips202.shake256
  have := le64_shake256 (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) (n := 64) (j := 0)
    (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this, Function.iterate_zero_apply, absorb_single (by norm_num) hs]
  rfl

/-- Lanes of μ's seed state are the lanes of `muBlock`. -/
theorem laneOf_muSeed (tr cd : ByteArray) {x : Nat} :
    laneOf (seedState 136 (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))) x =
      if x < 17 then le64 (muBlock tr cd) (8 * x) else 0 := by
  rw [laneOf_seedState (by norm_num)]
  rfl

end MlDsaOpt44.Proofs
