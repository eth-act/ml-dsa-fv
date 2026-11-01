import MlDsaOpt44.Fn.Decode.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Meaning of one `dz` gather step (WP8)

* `zR_gW`: the raw word of step `kk` holds `18` bits of `V_k` from bit
  `gs + 18 kk` in lane `k`;
* `zv_pack`, `zf_and`: the stored word is `K − raw` lane-wise, the flag word
  has no `zBitsN` bit iff every raw value is in `(78, 262066)`;
* `le_rawZ`: the bits of the little-endian windows are the packed fields
  `rawZ`; `okZ_iff`: `okZ` is the conjunction of all field checks.
-/

namespace MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-! ## Lanes -/

theorem pack4_lt' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) : pack4 v < 2 ^ 256 := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem pack4_testBit {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) (i : Nat) :
    (pack4 v).testBit i = if i < 256 then (v (i / 64)).testBit (i % 64) else false := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  have e : pack4 v = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v 3 + v 2) + v 1) + v 0 := by unfold pack4; ring
  have b1 : 2 ^ 64 * v 3 + v 2 < 2 ^ 128 := by omega
  have b2 : 2 ^ 64 * (2 ^ 64 * v 3 + v 2) + v 1 < 2 ^ 192 := by omega
  rw [e, Nat.testBit_two_pow_mul_add _ h0, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ h2]
  by_cases a0 : i < 64
  · rw [if_pos a0, if_pos (by omega), Nat.div_eq_of_lt a0, Nat.mod_eq_of_lt a0]
  rw [if_neg a0]
  by_cases a1 : i - 64 < 64
  · rw [if_pos a1, if_pos (by omega), show i / 64 = 1 by omega, show i % 64 = i - 64 by omega]
  rw [if_neg a1]
  by_cases a2 : i - 64 - 64 < 64
  · rw [if_pos a2, if_pos (by omega), show i / 64 = 2 by omega, show i % 64 = i - 64 - 64 by omega]
  rw [if_neg a2]
  by_cases a3 : i < 256
  · rw [if_pos a3, show i / 64 = 3 by omega, show i % 64 = i - 64 - 64 - 64 by omega]
  · rw [if_neg a3]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by omega) (by omega)))

theorem pack4_or {a b : Nat → Nat} (ha : ∀ k, k < 4 → a k < 2 ^ 64) (hb : ∀ k, k < 4 → b k < 2 ^ 64) :
    pack4 a ||| pack4 b = pack4 (fun k => a k ||| b k) := by
  have hab : ∀ k, k < 4 → a k ||| b k < 2 ^ 64 := fun k hk => Nat.or_lt_two_pow (ha k hk) (hb k hk)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, pack4_testBit ha, pack4_testBit hb, pack4_testBit hab]
  split
  · rw [Nat.testBit_or]
  · rfl

theorem pack4_and {a b : Nat → Nat} (ha : ∀ k, k < 4 → a k < 2 ^ 64) (hb : ∀ k, k < 4 → b k < 2 ^ 64) :
    pack4 a &&& pack4 b = pack4 (fun k => a k &&& b k) := by
  have hab : ∀ k, k < 4 → a k &&& b k < 2 ^ 64 := fun k hk =>
    Nat.lt_of_le_of_lt Nat.and_le_left (ha k hk)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, pack4_testBit ha, pack4_testBit hb, pack4_testBit hab]
  split
  · rw [Nat.testBit_and]
  · rfl

theorem pack4_eq_zero {c : Nat → Nat} : pack4 c = 0 ↔ ∀ k, k < 4 → c k = 0 := by
  unfold pack4
  constructor
  · intro h k hk; interval_cases k <;> omega
  · intro h
    rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]; simp

/-! ## The gathered raw words -/

theorem mb_bit (j : Nat) :
    Nat.testBit 1645498280219470655563407987279682868948834857825835856559341567 j =
      decide (j % 64 < 18 ∧ j < 256) := by
  by_cases hj : j < 256
  · have h : ∀ j, j < 256 →
        Nat.testBit 1645498280219470655563407987279682868948834857825835856559341567 j =
          decide (j % 64 < 18 ∧ j < 256) := by decide +kernel
    exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by omega) (by omega : 256 ≤ j)))]
    exact (decide_eq_false (by omega)).symm

theorem m54_bit (j : Nat) : Nat.testBit 18014398509481983 j = decide (j < 54) := by
  rw [show (18014398509481983 : Nat) = 2 ^ 54 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem zR_lt (x : Nat) : zR x < 2 ^ 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

/-- Raw word `kk` of a gather step. -/
theorem zR_gW (V : Nat → Nat) (gs kk : Nat) (hkk : kk ≤ 2) :
    zR (gW gs (V 0) (V 1) (V 2) (V 3) / 2 ^ (18 * kk)) =
      pack4 (fun k => V k / 2 ^ (gs + 18 * kk) % 2 ^ 18) := by
  have hl : ∀ k, k < 4 → V k / 2 ^ (gs + 18 * kk) % 2 ^ 18 < 2 ^ 64 := fun k _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  apply eq_of_testBit_lt (zR_lt _) (pack4_lt' hl)
  intro i hi
  rw [pack4_testBit hl, if_pos hi, zR, Nat.testBit_and, mb_bit, Nat.testBit_div_two_pow, gW]
  simp only [Nat.testBit_or, Nat.testBit_and, m54_bit, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow,
    show (6277101735386680763835789423207666416102355444464034512896 : Nat) = 2 ^ 192 from rfl,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 from rfl,
    show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]
  by_cases hm : i % 64 < 18
  · obtain h | h | h | h : i / 64 = 0 ∨ i / 64 = 1 ∨ i / 64 = 2 ∨ i / 64 = 3 := by omega
    all_goals
      rw [h]
      simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
        Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
      exact congrArg (Nat.testBit _) (by omega)
  · simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]

theorem zR_gW0 (V : Nat → Nat) (gs : Nat) :
    zR (gW gs (V 0) (V 1) (V 2) (V 3)) = pack4 (fun k => V k / 2 ^ gs % 2 ^ 18) := by
  simpa using zR_gW V gs 0 (by omega)

theorem zR_gW1 (V : Nat → Nat) (gs : Nat) :
    zR (gW gs (V 0) (V 1) (V 2) (V 3) / 262144) = pack4 (fun k => V k / 2 ^ (gs + 18) % 2 ^ 18) := by
  simpa using zR_gW V gs 1 (by omega)

theorem zR_gW2 (V : Nat → Nat) (gs : Nat) :
    zR (gW gs (V 0) (V 1) (V 2) (V 3) / 68719476736) =
      pack4 (fun k => V k / 2 ^ (gs + 36) % 2 ^ 18) := by
  simpa using zR_gW V gs 2 (by omega)

/-! ## Stored and flag words -/

theorem zv_pack {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 18) :
    zv (pack4 r) = pack4 (fun k => 8511489 - r k) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [zv, pack4]; omega

/-- The flag bits checked after `dz`. -/
def zBitsN : Nat := pack4 fun _ => 2 ^ 50 + 2 ^ 25

theorem and_bits_eq_zero (y : Nat) :
    y &&& (2 ^ 50 + 2 ^ 25) = 0 ↔ y.testBit 50 = false ∧ y.testBit 25 = false := by
  constructor
  · intro h
    have e50 := congrArg (Nat.testBit · 50) h
    have e25 := congrArg (Nat.testBit · 25) h
    simp only [Nat.testBit_and, Nat.zero_testBit, Nat.reducePow, Nat.reduceAdd, testBit_lit, Bool.and_true] at e50 e25
    exact ⟨e50, e25⟩
  · rintro ⟨h50, h25⟩
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hj : j = 50
    · subst hj; rw [h50, Bool.false_and]
    by_cases hj' : j = 25
    · subst hj'; rw [h25, Bool.false_and]
    have : (2 ^ 50 + 2 ^ 25 : Nat).testBit j = false := by
      rw [show (2 ^ 50 + 2 ^ 25 : Nat) = 2 ^ 50 ||| 2 ^ 25 by decide, Nat.testBit_or,
        Nat.testBit_two_pow, Nat.testBit_two_pow]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [this, Bool.and_false]

/-- One lane of the flag word. -/
theorem lane_flag {r : Nat} (hr : r < 2 ^ 18) :
    ((25043021 + (8511489 - r)) ||| (78 + r) * 4294967296) &&& (2 ^ 50 + 2 ^ 25) = 0 ↔
      78 < r ∧ r < 262066 := by
  rw [and_bits_eq_zero, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_false_iff, Bool.or_eq_false_iff,
    Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not, Nat.reducePow]
  omega

theorem zf_pack {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 18) :
    zf (pack4 r) = pack4 (fun k => (25043021 + (8511489 - r k)) ||| (78 + r k) * 4294967296) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  have ea : 157197590578425089497557413537698244700129010769177211286849462349 + zv (pack4 r) =
      pack4 (fun k => 25043021 + (8511489 - r k)) := by simp only [zv, pack4]; omega
  have eb : (489613935360161099605733599630031180607565790085621957525582 + pack4 r) * 4294967296 =
      pack4 (fun k => (78 + r k) * 4294967296) := by simp only [pack4]; omega
  unfold zf
  rw [ea, eb, pack4_or (fun k hk => by have := h k hk; omega) (fun k hk => by have := h k hk; omega)]

theorem zf_and {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 18) :
    zf (pack4 r) &&& zBitsN = 0 ↔ ∀ k, k < 4 → 78 < r k ∧ r k < 262066 := by
  have hl : ∀ k, k < 4 → (25043021 + (8511489 - r k)) ||| (78 + r k) * 4294967296 < 2 ^ 64 :=
    fun k hk => Nat.or_lt_two_pow (by have := h k hk; omega) (by have := h k hk; omega)
  rw [zf_pack h, zBitsN, pack4_and hl (fun _ _ => by norm_num), pack4_eq_zero]
  exact forall_congr' fun k => imp_congr_right fun hk => lane_flag (h k hk)

theorem zf_lt {R : Nat} (hR : R ≤ 1645498280219470655563407987279682868948834857825835856559341567) :
    zf R < 2 ^ 256 := by
  unfold zf zv
  exact Nat.or_lt_two_pow (by omega) (by omega)

theorem zf_zR_lt (x : Nat) : zf (zR x) < 2 ^ 256 := zf_lt Nat.and_le_left

theorem or_and_eq_zero (a b z : Nat) : (a ||| b) &&& z = 0 ↔ a &&& z = 0 ∧ b &&& z = 0 := by
  rw [show (a ||| b) &&& z = (a &&& z) ||| (b &&& z) by
    apply Nat.eq_of_testBit_eq; intro j; simp only [Nat.testBit_and, Nat.testBit_or]
    cases a.testBit j <;> cases b.testBit j <;> cases z.testBit j <;> rfl, Nat.or_eq_zero_iff]

/-! ## Calldata fields -/

theorem byteAt_extract {cd : ByteArray} {a n j : Nat} (hfield : a + n ≤ cd.size) (hj : j < n) :
    (cd.extract a (a + n))[j]!.toNat = byteAt cd (a + j) := by
  have hs : j < (cd.extract a (a + n)).size := by rw [ByteArray.size_extract]; omega
  rw [getElem!_pos (cd.extract a (a + n)) j hs, ByteArray.getElem_extract, byteAt, dif_pos (by omega)]

theorem bitsToInteger_succ (v : ByteArray) (p c : Nat) :
    Fips204.bitsToInteger v p (c + 1) = Fips204.bitsToInteger v p c + Fips204.bit v (p + c) * 2 ^ c := by
  simp [Fips204.bitsToInteger, List.range_succ, List.map_append, List.sum_append]

theorem div_mod_eq_bitsToInteger (v : ByteArray) (x s p : Nat) :
    ∀ c, (∀ t, t < c → x / 2 ^ (s + t) % 2 = Fips204.bit v (p + t)) →
      x / 2 ^ s % 2 ^ c = Fips204.bitsToInteger v p c
  | 0, _ => by simp [Fips204.bitsToInteger, Nat.mod_one]
  | c + 1, h => by
    rw [Nat.mod_pow_succ, bitsToInteger_succ,
      div_mod_eq_bitsToInteger v x s p c (fun t ht => h t (by omega)),
      Nat.div_div_eq_div_mul, ← Nat.pow_add, h c (by omega), Nat.mul_comm]

theorem testBit_eq_div_mod (x i : Nat) : x / 2 ^ i % 2 = (x.testBit i).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

/-- The `18` bits of window `k` from bit `54 g + 18 kk` are the field `rawZ`. -/
theorem le_rawZ {cd : ByteArray} (hcd : HDR ≤ cd.size) {u g kk k : Nat} (hg : g ≤ 3) (hkk : kk ≤ 2)
    (hk : k < 4) (ht : 4 * u + 3 * g + kk < 256) :
    leNat cd (Z0 + 9 * u + 576 * k) 32 / 2 ^ (54 * g + 18 * kk) % 2 ^ 18 =
      rawZ cd k (4 * u + 3 * g + kk) := by
  unfold rawZ
  apply div_mod_eq_bitsToInteger
  intro j hj
  have hf : Z0 + 576 * k + 576 ≤ cd.size := by simp only [HDR, Z0] at hcd ⊢; omega
  rw [testBit_eq_div_mod, leNat_bit, if_pos (by omega), Fips204.bit,
    show Z0 + 576 * (k + 1) = Z0 + 576 * k + 576 by omega,
    byteAt_extract hf (by omega), testBit_eq_div_mod,
    show Z0 + 9 * u + 576 * k + (54 * g + 18 * kk + j) / 8 =
      Z0 + 576 * k + (18 * (4 * u + 3 * g + kk) + j) / 8 by omega,
    show (54 * g + 18 * kk + j) % 8 = (18 * (4 * u + 3 * g + kk) + j) % 8 by omega]

theorem rawZ_lt (cd : ByteArray) (k t : Nat) : rawZ cd k t < 2 ^ 18 :=
  MlDsa44.Proofs.Decode.bitsToInteger_lt _ _ 18

theorem rawZ_eq_ref (cd : ByteArray) (k t : Nat) :
    rawZ cd k t = MlDsa44.Proofs.Decode.rawZ cd k t := by
  unfold rawZ MlDsa44.Proofs.Decode.rawZ
  rw [show Z0 + 576 * (k + 1) = 1344 + 576 * k + 576 by simp only [Z0]; omega,
    show Z0 + 576 * k = 1344 + 576 * k from rfl, Nat.mul_comm 18 t]

/-- `okZ` is the conjunction of the field checks. -/
theorem okZ_iff {cd : ByteArray} (hcd : HDR ≤ cd.size) :
    okZ cd = true ↔ ∀ k, k < 4 → ∀ t, t < 256 → 78 < rawZ cd k t ∧ rawZ cd k t < 262066 := by
  unfold okZ zPolys sigOf
  rw [MlDsa44.Proofs.Decode.normBelow_eq (by simp only [HDR] at hcd; omega)]
  simp only [MlDsa44.Proofs.Decode.zAll, MlDsa44.Proofs.Decode.okZ, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, rawZ_eq_ref]

end MlDsaOpt44.Proofs.DecodeZ
