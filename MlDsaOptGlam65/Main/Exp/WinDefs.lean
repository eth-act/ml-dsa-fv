import MlDsaOptGlam65.Main.Exp.Bound
import MlDsaOpt44.Main.Win.Math
import MlDsaOpt44.Fn.Fix.Lane
set_option warningAsError true
/-!
# The window of the 42-call schedule (calls 35–41): slot states and word lemmas

Seeds: `A[4][4]`, `A[5][4]`, `A[3][4]`, `A[3][3]`, c̃; `tr`'s sponge `T k` after `k`
blocks of the padded public key. `W cd b k` is slot `k` after call `35 + b`:

| call | slot 0 | slot 1 | slot 2 | slot 3 |
|---|---|---|---|---|
| 35, 36 | `A44` ×1, ×2 | `T 11`, `T 12` | `A34` ×1, ×2 | `A33` ×1, ×2 |
| 37, 38 | `T 13`, `T 14` | `A54` ×1, ×2 | `A34` ×3, ×4 | `A33` ×3, ×4 |
| 39 | `A44` ×3 | `A54` ×3 | `A34` ×5 | `A33` ×5 |
| 40 | `A44` ×4 | `A54` ×4 | `T 15` | c̃ ×1 |
| 41 | `A44` ×5 | `A54` ×5 | μ after block 0 | c̃ ×2 |

`kmove_*`: the four `kmove` calls; `lmerge_lane0`: `lmerge` with `ma = M64`, `sl = 0`;
`ks4_trabs_last2`, `pad_words2`: `pk`'s last block into slot 2.
-/

namespace MlDsaOptGlam65.Proofs.Exp

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs
open MlDsaOptGlam65.Proofs.Ex

/-- The seed state of `A[r][c]`. -/
def sA (cd : ByteArray) (r c : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r c)

/-- `tr`'s sponge after `k` blocks of the padded public key. -/
def T (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  absorbPre 136 (Fips202.pad 136 0x1F (pkOf cd)) k

/-- c̃'s seed state. -/
def sC (cd : ByteArray) : Fips202.SpongeState := seedState 136 (ctOf cd)

/-- Slot `k` after call `35 + b`. -/
def W (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 0 then (if b < 2 then permN (b + 1) (sA cd 4 4) else if b < 4 then T cd (b + 11)
    else permN (b - 1) (sA cd 4 4))
  else if k = 1 then (if b < 2 then T cd (b + 11) else permN (b - 1) (sA cd 5 4))
  else if k = 2 then (if b < 5 then permN (b + 1) (sA cd 3 4) else if b = 5 then T cd 15
    else absorbPre 136 (padMu cd) 1)
  else (if b < 5 then permN (b + 1) (sA cd 3 3) else permN (b - 4) (sC cd))

theorem sA_size (cd : ByteArray) (r c : Nat) : (sA cd r c).size = 25 := seedState_size _ _

theorem T_size (cd : ByteArray) (k : Nat) : (T cd k).size = 25 := absorbPre_size _ _ _

theorem W_sized (cd : ByteArray) (b : Nat) : Sized4 (W cd b) := fun k _ => by
  have h1 := fun n r c => permN_size (sA_size cd r c) n
  have h2 := fun n => permN_size (seedState_size 136 (ctOf cd)) n
  unfold W
  by_cases k0 : k = 0
  · rw [if_pos k0]
    by_cases b2 : b < 2
    · rw [if_pos b2]; exact h1 _ _ _
    · rw [if_neg b2]; by_cases b4 : b < 4
      · rw [if_pos b4]; exact T_size _ _
      · rw [if_neg b4]; exact h1 _ _ _
  · rw [if_neg k0]; by_cases k1 : k = 1
    · rw [if_pos k1]; by_cases b2 : b < 2
      · rw [if_pos b2]; exact T_size _ _
      · rw [if_neg b2]; exact h1 _ _ _
    · rw [if_neg k1]; by_cases k2 : k = 2
      · rw [if_pos k2]; by_cases b5 : b < 5
        · rw [if_pos b5]; exact h1 _ _ _
        · rw [if_neg b5]; by_cases b55 : b = 5
          · rw [if_pos b55]; exact T_size _ _
          · rw [if_neg b55]; exact absorbPre_size _ _ _
      · rw [if_neg k2]; by_cases b5 : b < 5
        · rw [if_pos b5]; exact h1 _ _ _
        · rw [if_neg b5]; exact h2 _

theorem W0 (cd : ByteArray) {b : Nat} (hb : b < 2 ∨ (4 ≤ b ∧ b < 7)) :
    W cd b 0 = permN (if b < 2 then b + 1 else b - 1) (sA cd 4 4) := by
  unfold W; rcases hb with hb | ⟨h1, _⟩
  · simp [hb]
  · simp [show ¬ b < 2 by omega, show ¬ b < 4 by omega]

/-! ## `kmove` -/

private theorem bit256 {c : Nat} (hc : c < 2 ^ 256) (p : Nat → Bool)
    (h : ∀ i, i < 256 → c.testBit i = p (i % 4)) (i : Nat) :
    c.testBit i = (decide (i < 256) && p (i % 4)) := by
  by_cases hi : i < 256
  · simp [hi, h i hi]
  · have : c < 2 ^ i := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hi, Nat.testBit_lt_two_pow this]

private theorem m1_bit (i : Nat) :
    (0x1111111111111111111111111111111111111111111111111111111111111111 : Nat).testBit i =
      (decide (i < 256) && decide (i % 4 = 0)) :=
  bit256 (by norm_num) (fun k => decide (k = 0)) (by decide +kernel) i

private theorem m2_bit (i : Nat) :
    (0x2222222222222222222222222222222222222222222222222222222222222222 : Nat).testBit i =
      (decide (i < 256) && decide (i % 4 = 1)) :=
  bit256 (by norm_num) (fun k => decide (k = 1)) (by decide +kernel) i

private theorem m4_bit (i : Nat) :
    (0x4444444444444444444444444444444444444444444444444444444444444444 : Nat).testBit i =
      (decide (i < 256) && decide (i % 4 = 2)) :=
  bit256 (by norm_num) (fun k => decide (k = 2)) (by decide +kernel) i

private theorem m3_bit (i : Nat) :
    (0x3333333333333333333333333333333333333333333333333333333333333333 : Nat).testBit i =
      (decide (i < 256) && decide (i % 4 < 2)) :=
  bit256 (by norm_num) (fun k => decide (k < 2)) (by decide +kernel) i

private theorem me_bit (i : Nat) :
    (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : Nat).testBit i =
      (decide (i < 256) && !decide (i % 4 = 0)) :=
  bit256 (by norm_num) (fun k => !decide (k = 0)) (by decide +kernel) i

set_option linter.unusedVariables false in
/-- `kmove [0, 0x2222…, 0, 1, KS]`: slot 0 moves to slot 1, the rest is cleared. -/
theorem kmove_01 (v : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) :
    (il v * 2 ^ 1 % 2 ^ 256 / 2 ^ 0 &&&
        0x2222222222222222222222222222222222222222222222222222222222222222) ||| (il v &&& 0) =
    il fun k => if k = 1 then v 0 else 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.and_zero, Nat.or_zero, Nat.testBit_and, Nat.pow_zero, Nat.div_one, Nat.testBit_mod_two_pow,
    Nat.testBit_mul_two_pow, m2_bit, testBit_il, testBit_il]
  by_cases hi : i < 256
  · by_cases h : i % 4 = 1
    · have e : (i - 1) % 4 = 0 ∧ (i - 1) / 4 = i / 4 ∧ 1 ≤ i ∧ i - 1 < 256 := by omega
      simp_all
    · simp [hi, h]
  · simp [hi]

set_option linter.unusedVariables false in
/-- `kmove [0xeee…, 0x1111…, 1, 0, KS]`: slot 1 moves to slot 0, slots 1 … 3 stay. -/
theorem kmove_10 (v : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) :
    (il v * 2 ^ 0 % 2 ^ 256 / 2 ^ 1 &&&
        0x1111111111111111111111111111111111111111111111111111111111111111) |||
      (il v &&& 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee) =
    il fun k => if k = 0 then v 1 else v k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_div_two_pow, Nat.pow_zero,
    Nat.mul_one, Nat.mod_eq_of_lt (il_lt v), m1_bit, me_bit, testBit_il, testBit_il, testBit_il]
  by_cases hi : i < 256
  · by_cases h : i % 4 = 0
    · have e : (i + 1) % 4 = 1 ∧ (i + 1) / 4 = i / 4 ∧ i + 1 < 256 := by omega
      simp_all
    · simp [hi, h]
  · simp [hi, show ¬ i + 1 < 256 by omega]

set_option linter.unusedVariables false in
/-- `kmove [0xeee…, 0x1111…, 0, 0, src]`: slot 0 from `src`, slots 1 … 3 stay. -/
theorem kmove_src0 (v w : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) (hw : ∀ k, k < 4 → w k < 2 ^ 64) :
    (il v * 2 ^ 0 % 2 ^ 256 / 2 ^ 0 &&&
        0x1111111111111111111111111111111111111111111111111111111111111111) |||
      (il w &&& 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee) =
    il fun k => if k = 0 then v 0 else w k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.pow_zero, Nat.mul_one, Nat.div_one,
    Nat.mod_eq_of_lt (il_lt v), m1_bit, me_bit, testBit_il, testBit_il, testBit_il]
  by_cases hi : i < 256
  · by_cases h : i % 4 = 0 <;> simp [hi, h]
  · simp [hi]

set_option linter.unusedVariables false in
/-- `kmove [0x3333…, 0x4444…, 0, 2, src]`: slot 2 from slot 0 of `src`, slots 0, 1 stay,
slot 3 cleared. -/
theorem kmove_02 (v w : Nat → Nat) (hv : ∀ k, k < 4 → v k < 2 ^ 64) (hw : ∀ k, k < 4 → w k < 2 ^ 64) :
    (il v * 2 ^ 2 % 2 ^ 256 / 2 ^ 0 &&&
        0x4444444444444444444444444444444444444444444444444444444444444444) |||
      (il w &&& 0x3333333333333333333333333333333333333333333333333333333333333333) =
    il fun k => if k < 2 then w k else if k = 2 then v 0 else 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.pow_zero, Nat.div_one, Nat.testBit_mod_two_pow,
    Nat.testBit_mul_two_pow, m4_bit, m3_bit, testBit_il, testBit_il, testBit_il]
  by_cases hi : i < 256
  · have h4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have e2 : i % 4 = 2 → (i - 2) % 4 = 0 ∧ (i - 2) / 4 = i / 4 ∧ 2 ≤ i ∧ i - 2 < 256 := by omega
    rcases h4 with h | h | h | h <;> simp_all
  · simp [hi]

/-! ## `lmerge` with `ma = M64`, `sl = 0` -/

theorem lmerge_lane0 {a b : Nat} (hb : b < 2 ^ 256) (r : Nat) :
    lane (let b' := b * 2 ^ 0 % 2 ^ 256; b' ^^^ ((a ^^^ b') &&& M64)) r =
      if r = 0 then lane a 0 else lane b r := by
  simp only [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hb]
  apply Nat.eq_of_testBit_eq; intro j
  have hM : M64 = 2 ^ 64 - 1 := rfl
  by_cases hr : r = 0
  · subst hr
    simp only [if_true, Fix.testBit_lane, Nat.testBit_xor, Nat.testBit_and, hM, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < 64
    · simp only [hj, decide_true, Bool.true_and, Bool.and_true, Nat.mul_zero, Nat.zero_add]
      cases a.testBit j <;> cases b.testBit j <;> rfl
    · simp [hj]
  · simp only [if_neg hr, Fix.testBit_lane, Nat.testBit_xor, Nat.testBit_and, hM, Nat.testBit_two_pow_sub_one]
    have : ¬ 64 * r + j < 64 := by omega
    by_cases hj : j < 64 <;> simp [hj, this]

/-! ## The last block of `pk` into slot 2 -/

/-- The last block of the padded public key (`trabs` with two groups, then the
two padding xors), absorbed into slot 2. -/
theorem ks4_trabs_last2 {m m' : ByteArray} {cd : ByteArray} (hcd : CTOFF ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 2 then
        trLane cd 1904 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 2 x
        else 0) * 2 ^ 2 ^^^ spread ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 2) :
    KS4 m' (upd S 2 (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (14 * 136) (S 2))) := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  have hsx : ∀ a b, spread a * 2 ^ 2 ^^^ spread b * 2 ^ 2 = spread (a ^^^ b) * 2 ^ 2 := fun a b => by
    rw [spread_mul_two_pow _ (by norm_num), spread_mul_two_pow _ (by norm_num),
      spread_mul_two_pow _ (by norm_num), il_xor]
    exact il_congr fun k _ => by split <;> simp
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 2 then
        trLane cd 1904 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 2 x
        else 0) ^^^ ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact trLane_lt' _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, hsx]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 2 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 14 * 136 + 8 * x = 1904 + 8 * x by omega,
      S4.le64_padPk_last hcd h17]
    congr 1
    by_cases h6 : x < 6
    · rw [if_pos h6, if_pos (by omega), trLane_eq cd S4.lm_top2, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero]
    · rw [if_neg h6]
      by_cases hx6 : x = 6
      · subst hx6; rw [trLane_eq cd S4.lm_top2]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx6, if_neg hx16, Nat.xor_zero]
          by_cases h8 : x < 8
          · rw [if_pos h8, trLane_eq cd S4.lm_top2, if_pos (by omega)]
          · rw [if_neg h8]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

/-- The two padding xors of the last `pk` block (lanes 6 and 16, slot 2). -/
theorem pad_words2 {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 192 ^^^ 279620) % 2 ^ 256) 32) 192)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 192 ^^^ 279620) % 2 ^ 256) 32) 192) 512 ^^^
        28948022309329048855892746252171976963317496166410141009864396001978282409984) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 2 := by
  have hm : ∀ (w c : Nat), c < 2 ^ 256 → w < 2 ^ 256 → (w ^^^ c) % 2 ^ 256 = w ^^^ c :=
    fun w c hc hw => Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw hc)
  unfold KS
  by_cases h6 : x = 6
  · subst h6
    rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)),
      hm _ _ (by norm_num) (word_lt _ _)]
    congr 1
  · by_cases h16 : x = 16
    · subst h16
      rw [word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)), hm _ _ (by norm_num) (word_lt _ _),
        word_mstore_disjoint _ _ (by omega)]
      congr 1
    · rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), if_neg h6, if_neg h16,
        Nat.xor_zero, spread_zero, Nat.zero_mul, Nat.xor_zero]

end MlDsaOptGlam65.Proofs.Exp
