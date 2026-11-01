import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Fix
import MlDsaOpt87.Fn.Group.Seed
import MlDsaOpt87.Math
import MlDsaOpt44.Math.SpongeG234
import MlDsaOpt44.Math.Sponge
set_option warningAsError true
/-!
# Sponge facts for the mixed groups 10–13 of ML-DSA-87 (WP S5)

* `s5_ginitWord_eq`, `s5_ks4_ginit`: the state ML-DSA-87's `ginit` (no c̃
  lanes) builds from fresh / kept slots.
* `S5Blocks`: the squeezed blocks of a group; `S5Blocks.pending` (the 87 `Pending`).
* `s5_le64_padPk_*`, `s5_le64_trOf`: the 20 blocks of the padded public key and
  `tr` as lanes of the absorbed state.
* `s5_ks4_trabs_full`, `s5_ks4_trabs_last`: what `trabs` (and the padding
  xors of group 13) do to the `tr` slot.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs

/-! ## `ginit` -/

theorem s5_ginitWord_eq {m cd : ByteArray} (hrho : Rho1At m cd)
    {keep amult cmult kmask l4 : Nat} {L cur : Nat → Nat} {x : Nat}
    (ha : amult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hks : word m (KS + 32 * x) &&& keep = il fun k => if kmask.testBit k then cur k else 0)
    (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true → amult.testBit k = false ∧ L k = 0) :
    ginitWord m keep amult cmult l4 x =
      il fun k => if kmask.testBit k then cur k else
        cpl x (freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x) := by
  have hd0 : (if x < 4 then word m (RHO1 + 32 * x) * amult % 2 ^ 256 else 0) =
      il fun k => if x < 4 then (if amult.testBit k then le64 cd (8 * x) else 0) else 0 := by
    by_cases hx : x < 4
    · rw [if_pos hx, hrho x hx, spread_mul _ ha, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd1 : (if x = 4 then l4 else 0) = il fun k => if x = 4 then L k else 0 := by
    by_cases hx : x = 4
    · rw [if_pos hx, hl4]; exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
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
  rw [hd0, hd1, hd3, hd4, hks, il_xor, il_xor, il_xor, il_or]
  apply il_congr
  intro k hk
  cases hkk : kmask.testBit k
  · have hf := freshLane_lt (amult := amult) (cmult := 0) (ρ := fun x => le64 cd (8 * x))
      (c := fun _ => 0) (k := k) (x := x) (le64_lt _ _) (by norm_num) (hL k hk)
    rw [cpl_eq hf]
    simp only [Bool.false_eq_true, if_false, Nat.or_zero]
    unfold freshLane
    simp only [Nat.zero_testBit, Bool.false_eq_true, if_false, and_false, Nat.xor_zero, ite_self]
    by_cases hx : x ∈ complemented
    · simp only [hx, true_and, if_true]
    · simp only [hx, false_and, if_false, Nat.xor_zero]
  · obtain ⟨h1, h3⟩ := hdisj k hk hkk
    simp only [h1, h3, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false, and_false,
      Nat.xor_zero, ite_self, Nat.zero_or]

/-- The state ML-DSA-87's `ginit` builds: kept slots (`kmask`) carry `S`, fresh
slots the states whose lanes are their `freshLane`s (no c̃ lanes). -/
theorem s5_ks4_ginit {m m' cd : ByteArray} {keep amult cmult kmask l4 : Nat} {L : Nat → Nat}
    {S I : Nat → Fips202.SpongeState} (hrho : Rho1At m cd) (ha : amult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true → amult.testBit k = false ∧ L k = 0)
    (hkept : ∀ k, k < 4 → kmask.testBit k = true → I k = S k)
    (hfresh : ∀ k, k < 4 → kmask.testBit k = false → ∀ x, x < 25 →
      freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x = laneOf (I k) x)
    (hm' : ∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) :
    KS4 m' I := by
  intro x hx
  rw [hm' x hx, s5_ginitWord_eq hrho ha hkeep hl4 (hand x hx) hL hdisj]
  apply il_congr; intro k hk
  cases hkk : kmask.testBit k
  · simp only [Bool.false_eq_true, if_false]; rw [hfresh k hk hkk x hx]
  · simp only [if_true]; rw [hkept k hk hkk]

theorem s5_freshLane_aSeed {cd : ByteArray} (hcd : 32 ≤ cd.size) {amult : Nat} {L : Nat → Nat}
    {k r col : Nat} (hr : r < 256) (hcol : col < 256)
    (ha : amult.testBit k = true) (hL : L k = col + 256 * r + 0x1F0000) {x : Nat} (hx : x < 25) :
    freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x =
      laneOf (seedState 168 (aSeed cd r col)) x :=
  freshLane_aSeed hcd (fun _ _ => rfl) hr hcol ha (Nat.zero_testBit k) hL hx

theorem s5_freshLane_zero {amult : Nat} {L : Nat → Nat} {k : Nat}
    (ha : amult.testBit k = false) (hL : L k = 0) (x : Nat) :
    freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x = laneOf Fips202.emptyState x :=
  freshLane_zero ha (Nat.zero_testBit k) hL x

/-! ## Squeezed blocks -/

/-- Blocks `0 … n − 1` of a SIMD group, block `b` made from the slot states `St b`. -/
def S5Blocks (m : ByteArray) (St : Nat → Nat → Fips202.SpongeState) (n : Nat) : Prop :=
  ∀ b, b < n → (∀ i, i < 56 → word m (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (St b k) i) ∧
    (∀ g, g < 7 → word m (FL + 224 * b + 32 * g) = flagWord (St b) g)

theorem S5Blocks.zero (m : ByteArray) (St : Nat → Nat → Fips202.SpongeState) : S5Blocks m St 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem S5Blocks.frame {m m' : ByteArray} {St : Nat → Nat → Fips202.SpongeState} {n : Nat}
    {rs : List (Nat × Nat)} (h : S5Blocks m St n) (hf : FrameExcept m m' rs)
    (ha : Avoids rs ABUF (ABUF + 1792 * n)) (hb : Avoids rs FL (FL + 224 * n)) : S5Blocks m' St n :=
  fun b hbn => ⟨fun i hi => by
      rw [word_frame hf ha (a := ABUF + 1792 * b + 32 * i) (by omega) (by omega)]; exact (h b hbn).1 i hi,
    fun g hg => by
      rw [word_frame hf hb (a := FL + 224 * b + 32 * g) (by omega) (by omega)]; exact (h b hbn).2 g hg⟩

theorem S5Blocks.pending {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState} (h : S5Blocks m St 5)
    {sl : Nat} (hsl : sl < 4) {I : Fips202.SpongeState} (hSt : ∀ b, b < 5 → St b sl = permN (b + 1) I)
    (h6 : word m HAVE6 = 0) {S : Nat → Fips202.SpongeState} (hS : S sl = permN 5 I) :
    MlDsaOpt87.Proofs.Pending m S sl I :=
  pending_of_blocks hsl hSt (fun b hb => (h b hb).1) (fun b hb => (h b hb).2) h6 hS

theorem s5_KS4_congr {m : ByteArray} {S S' : Nat → Fips202.SpongeState} (h : KS4 m S)
    (hS : ∀ k, k < 4 → S k = S' k) : KS4 m S' := fun x hx => by
  rw [h x hx]; exact il_congr fun k hk => by rw [hS k hk]

theorem s5_KS4_frame {m m' : ByteArray} {rs : List (Nat × Nat)} {S : Nat → Fips202.SpongeState}
    (h : KS4 m S) (hf : FrameExcept m m' rs) (ha : Avoids rs KS (KS + 800)) : KS4 m' S := fun x hx => by
  rw [word_frame hf ha (a := KS + 32 * x) (by omega) (by omega)]; exact h x hx

theorem s5_pack4_congr {v w : Nat → Nat} (h : ∀ k, k < 4 → v k = w k) : pack4 v = pack4 w := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem s5_flagWord_congr {F G : Nat → Fips202.SpongeState} (h : ∀ k, k < 4 → F k = G k) (g : Nat) :
    flagWord F g = flagWord G g := by
  unfold flagWord
  have e : ((List.range 8).map fun i => pack4 fun k => cand (F k) (8 * g + i) + 2 ^ 23 - Fips204.q) =
      (List.range 8).map fun i => pack4 fun k => cand (G k) (8 * g + i) + 2 ^ 23 - Fips204.q :=
    List.map_congr_left fun i _ => s5_pack4_congr fun k hk => by rw [h k hk]
  rw [e]

theorem s5_sized4_permute {S : Nat → Fips202.SpongeState} (hS : Sized4 S) :
    Sized4 fun k => Keccak.permute (S k) := fun k hk => permute_size (hS k hk)

/-! ## The padded public key (2592 bytes, 20 blocks) -/

theorem s5_pkOf_size {cd : ByteArray} (hcd : 2592 ≤ cd.size) : (pkOf cd).size = 2592 := by
  unfold pkOf CTOFF; simp [ByteArray.size_extract]; omega

theorem s5_padPk_size {cd : ByteArray} (hcd : 2592 ≤ cd.size) : (padPk cd).size = 20 * 136 := by
  unfold padPk; rw [pad_size _ _ (by norm_num), s5_pkOf_size hcd]

/-- Lanes of the 19 full blocks of the padded public key are calldata lanes. -/
theorem s5_le64_padPk_full {cd : ByteArray} (hcd : 2592 ≤ cd.size) {a : Nat} (ha : a + 8 ≤ 2592) :
    le64 (padPk cd) a = le64 cd a := by
  apply le64_congr
  intro k hk
  unfold padPk
  rw [byteAt_pad_lt _ _ _ (by rw [s5_pkOf_size hcd]; omega)]
  unfold pkOf CTOFF
  rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]

theorem s5_byteAt_padPk_last {cd : ByteArray} (hcd : 2592 ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (padPk cd) (2584 + i) =
      if i < 8 then byteAt cd (2584 + i) else if i = 8 then 31 else if i = 135 then 128 else 0 := by
  have := byteAt_pad_last 136 (pkOf cd) (by norm_num) i hi
  rw [s5_pkOf_size hcd] at this
  norm_num at this
  unfold padPk
  rw [this]
  by_cases h : i < 8
  · rw [if_pos h, if_pos h]; unfold pkOf CTOFF
    rw [byteAt_extract _ _ _ _ hcd, if_pos (by omega), Nat.zero_add]
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- The last block of the padded public key: one calldata lane, then the padding. -/
theorem s5_le64_padPk_last {cd : ByteArray} (hcd : 2592 ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (padPk cd) (2584 + 8 * x) =
      if x = 0 then le64 cd 2584 else if x = 1 then 31 else if x = 16 then 2 ^ 63 else 0 := by
  have hb := fun i (hi : i < 136) => s5_byteAt_padPk_last hcd (i := i) hi
  by_cases h0 : x = 0
  · subst h0; rw [if_pos rfl]
    apply le64_congr
    intro k hk
    rw [Nat.mul_zero, Nat.add_zero, hb _ (by omega), if_pos (by omega)]
  rw [if_neg h0, le64_eq]
  have hk : ∀ k, k < 8 → byteAt (padPk cd) (2584 + 8 * x + k) =
      if 8 * x + k < 8 then byteAt cd (2584 + (8 * x + k)) else if 8 * x + k = 8 then 31
      else if 8 * x + k = 135 then 128 else 0 := fun k hk => by
    rw [Nat.add_assoc]; exact hb _ (by omega)
  have h0' := hk 0 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at h0'
  rw [h0', hk 1 (by omega), hk 2 (by omega), hk 3 (by omega), hk 4 (by omega), hk 5 (by omega),
    hk 6 (by omega), hk 7 (by omega)]
  by_cases hx1 : x = 1
  · subst hx1; norm_num
  · by_cases hx16 : x = 16
    · subst hx16; norm_num
    · rw [if_neg hx1, if_neg hx16]
      simp only [show ¬ 8 * x < 8 by omega, show ¬ 8 * x = 8 by omega, show ¬ 8 * x = 135 by omega,
        show ¬ 8 * x + 1 < 8 by omega, show ¬ 8 * x + 1 = 8 by omega, show ¬ 8 * x + 1 = 135 by omega,
        show ¬ 8 * x + 2 < 8 by omega, show ¬ 8 * x + 2 = 8 by omega, show ¬ 8 * x + 2 = 135 by omega,
        show ¬ 8 * x + 3 < 8 by omega, show ¬ 8 * x + 3 = 8 by omega, show ¬ 8 * x + 3 = 135 by omega,
        show ¬ 8 * x + 4 < 8 by omega, show ¬ 8 * x + 4 = 8 by omega, show ¬ 8 * x + 4 = 135 by omega,
        show ¬ 8 * x + 5 < 8 by omega, show ¬ 8 * x + 5 = 8 by omega, show ¬ 8 * x + 5 = 135 by omega,
        show ¬ 8 * x + 6 < 8 by omega, show ¬ 8 * x + 6 = 8 by omega, show ¬ 8 * x + 6 = 135 by omega,
        show ¬ 8 * x + 7 < 8 by omega, show ¬ 8 * x + 7 = 8 by omega, show ¬ 8 * x + 7 = 135 by omega,
        if_false]

/-- `tr = H(pk, 64)`: lane `x` is lane `x` of the state after the 20 absorbed
blocks of the padded public key. -/
theorem s5_le64_trOf {cd : ByteArray} (hcd : 2592 ≤ cd.size) {x : Nat} (hx : x < 8) :
    le64 (trOf cd) (8 * x) = laneOf (absorbPre 136 (padPk cd) 20) x := by
  unfold trOf MlDsa.Fips204.H Fips202.shake256
  have := le64_shake256 (pkOf cd) (n := 64) (j := 0) (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this, Function.iterate_zero_apply]
  exact congrArg (fun S => laneOf S x) (absorb_eq 136 (padPk cd) 20 (by norm_num) (s5_padPk_size hcd))

/-! ## `trabs` on the `tr` slot -/

/-- `trabs`'s post with `kp = 0`, `sh = 3`, normalised. -/
theorem s5_trabs_norm {m m' : ByteArray} {cd : ByteArray} {off lm n4 : Nat}
    (hpost : ∀ x, x < 25 → word m' (KS + 32 * x) =
      if 0 ≤ KS + 32 * x ∧ KS + 32 * x < 0 + 128 * n4 then
        word m (KS + 32 * x) ^^^ spread (trLane cd off lm n4 ((KS + 32 * x - 0) / 32)) * 2 ^ 3
      else word m (KS + 32 * x)) :
    ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * n4 then trLane cd off lm n4 x else 0) * 2 ^ 3 := by
  intro x hx
  rw [hpost x hx]
  by_cases h : x < 4 * n4
  · rw [if_pos (by unfold KS; omega), if_pos h, show (KS + 32 * x - 0) / 32 = x by unfold KS; omega]
  · rw [if_neg (by unfold KS; omega), if_neg h, spread_zero, Nat.zero_mul, Nat.xor_zero]

theorem s5_trLane_lt (cd : ByteArray) (off lm n4 u : Nat) : trLane cd off lm n4 u < 2 ^ 64 := by
  unfold trLane; exact Nat.mod_lt _ (by norm_num)

/-- A full block `j < 19` of the padded public key, absorbed into slot 3. -/
theorem s5_ks4_trabs_full {m m' : ByteArray} {cd : ByteArray} (hcd : 2592 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S) {j : Nat} (hj : j < 19)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 5 then
        trLane cd (136 * j) 0xffffffffffffffff000000000000000000000000000000000000000000000000 5 x
        else 0) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then Fips202.xorBlock 136 (padPk cd) (j * 136) (S 3) else S k := by
  refine ks4_xor_slot (by norm_num) hks _ (fun x _ => by
    split
    · exact s5_trLane_lt _ _ _ _ _
    · norm_num) hw _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), if_pos (by omega), trLane_eq cd lm_top1,
      if_neg (by omega), s5_le64_padPk_full hcd (by omega), Nat.mul_comm j]
  · rw [if_neg (by norm_num; omega)]
    by_cases h20 : x < 20
    · rw [if_pos (by omega), trLane_eq cd lm_top1, if_pos (by omega), Nat.xor_zero]
    · rw [if_neg (by omega), Nat.xor_zero]

theorem s5_spread_xor_shift (a b : Nat) :
    spread a * 2 ^ 3 ^^^ spread b * 2 ^ 3 = spread (a ^^^ b) * 2 ^ 3 := by
  rw [spread_mul_two_pow _ (by norm_num), spread_mul_two_pow _ (by norm_num),
    spread_mul_two_pow _ (by norm_num), il_xor]
  exact il_congr fun k _ => by split <;> simp

/-- The last block 19 of the padded public key (`trabs` with one group, then
the two padding xors), absorbed into slot 3. -/
theorem s5_ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : 2592 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 1 then
        trLane cd 2584 0xffffffffffffffff000000000000000000000000000000000000000000000000 1 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 1 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then Fips202.xorBlock 136 (padPk cd) (19 * 136) (S 3) else S k := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 1 then
        trLane cd 2584 0xffffffffffffffff000000000000000000000000000000000000000000000000 1 x
        else 0) ^^^ ((if x = 1 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact s5_trLane_lt _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, s5_spread_xor_shift]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 19 * 136 + 8 * x = 2584 + 8 * x by omega,
      s5_le64_padPk_last hcd h17]
    congr 1
    by_cases h0 : x = 0
    · subst h0
      rw [trLane_eq cd lm_top1]
      norm_num
    · rw [if_neg h0]
      by_cases hx1 : x = 1
      · subst hx1; rw [trLane_eq cd lm_top1]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx1, if_neg hx16, Nat.xor_zero]
          split
          · rw [trLane_eq cd lm_top1, if_pos (by omega)]
          · rfl
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

end MlDsaOpt87.Proofs
