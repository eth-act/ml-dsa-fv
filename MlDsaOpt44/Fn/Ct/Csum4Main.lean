import MlDsaOpt44.Fn.Ct.Csum4Iter
import MlDsaOpt44.Fn.Ct.Csum4T
import MlDsaOpt44.Fn.Ct.Csum4Spec
/-!
# `csum` (v4, WP I): the stored words and the contract body

v4 keeps the running count replicated and pre-negated: before position `t`
the count word is `g_t = pack4 (spOff − N c t)` (`g_zero`, `g_step`: each
`CW` code `±REP` is subtracted), and every emitted word is
`g_(t+1) − pack4 (2^13 S'_r(t))` (one shift and mask of the transposed sum,
`extract`), lane-wise without borrow since `2^13 S' + n_neg < spOff`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOpt44.Proofs.CS4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.L10
open MlDsaOpt44.Proofs.CS

/-! ## Window entries are 10-bit -/

theorem bitsToInteger_lt' (v : ByteArray) (s : Nat) : ∀ c, Fips204.bitsToInteger v s c < 2 ^ c
  | 0 => by simp [Fips204.bitsToInteger]
  | c + 1 => by
    have ih := bitsToInteger_lt' v s c
    unfold Fips204.bitsToInteger at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    have hb : Fips204.bit v (s + c) ≤ 1 := by
      unfold Fips204.bit; have := Nat.mod_lt (v[(s + c) / 8]!.toNat / 2 ^ ((s + c) % 8)) (by decide : 0 < 2)
      omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_succ]
    have : Fips204.bit v (s + c) * 2 ^ c ≤ 2 ^ c := by
      calc _ ≤ 1 * 2 ^ c := Nat.mul_le_mul_right _ hb
        _ = 2 ^ c := Nat.one_mul _
    omega

theorem tEntry_le (cd : ByteArray) (r e : Nat) : tEntry cd r e ≤ 1023 := by
  unfold tEntry
  split_ifs
  · have := bitsToInteger_lt' (cd.extract (32 + 320 * r) (32 + 320 * (r + 1))) (10 * (e - 256)) 10
    unfold t1v; omega
  · omega

/-! ## The window sum -/

/-- Word `m` of the window sum at `bu`. -/
def W (M : ByteArray) (bu m : Nat) : Nat := word M (bu + word M (40960 + 32 * m))

def wsum (M : ByteArray) (bu : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wsum M bu n + W M bu n

def csn (M : ByteArray) (bu f n : Nat) : Nat := ((List.range n).map fun m => cell (W M bu m) f).sum

theorem csn_succ (M : ByteArray) (bu f n : Nat) : csn M bu f (n + 1) = csn M bu f n + cell (W M bu n) f := by
  simp [csn, List.range_succ]

theorem wsum_39 (M : ByteArray) (bu : Nat) : wsum M bu 39 = 0 + W M bu 0 + W M bu 1 + W M bu 2 + W M bu 3 + W M bu 4 + W M bu 5 + W M bu 6 + W M bu 7 + W M bu 8 + W M bu 9 + W M bu 10 + W M bu 11 + W M bu 12 + W M bu 13 + W M bu 14 + W M bu 15 + W M bu 16 + W M bu 17 + W M bu 18 + W M bu 19 + W M bu 20 + W M bu 21 + W M bu 22 + W M bu 23 + W M bu 24 + W M bu 25 + W M bu 26 + W M bu 27 + W M bu 28 + W M bu 29 + W M bu 30 + W M bu 31 + W M bu 32 + W M bu 33 + W M bu 34 + W M bu 35 + W M bu 36 + W M bu 37 + W M bu 38 := rfl

theorem s3_toNat (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    (hm0 : ∀ i, i < 11 → word m0 (40960 + 32 * i) = word M (40960 + 32 * i)) :
    (s3 m0 M bu cw sp g).toNat = wsum M bu 39 % 2 ^ 256 := by
  have e0 : word m0 40960 = word M 40960 := by simpa using hm0 0 (by norm_num)
  have e1 : word m0 40992 = word M 40992 := by simpa using hm0 1 (by norm_num)
  have e2 : word m0 41024 = word M 41024 := by simpa using hm0 2 (by norm_num)
  have e3 : word m0 41056 = word M 41056 := by simpa using hm0 3 (by norm_num)
  have e4 : word m0 41088 = word M 41088 := by simpa using hm0 4 (by norm_num)
  have e5 : word m0 41120 = word M 41120 := by simpa using hm0 5 (by norm_num)
  have e6 : word m0 41152 = word M 41152 := by simpa using hm0 6 (by norm_num)
  have e7 : word m0 41184 = word M 41184 := by simpa using hm0 7 (by norm_num)
  have e8 : word m0 41216 = word M 41216 := by simpa using hm0 8 (by norm_num)
  have e9 : word m0 41248 = word M 41248 := by simpa using hm0 9 (by norm_num)
  have e10 : word m0 41280 = word M 41280 := by simpa using hm0 10 (by norm_num)
  simp only [s3, s2, s1, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  simp only [c4s3, c4s2, c4s1, EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]
  rw [wsum_39]
  simp only [W, Nat.reduceMul, Nat.reduceAdd]
  apply congrArg (· % 2 ^ 256)
  ring

theorem wsum_cells (M : ByteArray) (bu : Nat) (hc : ∀ m f, m < 39 → f < 16 → cell (W M bu m) f ≤ 1023) :
    ∀ n, n ≤ 39 → wsum M bu n < 2 ^ 256 ∧ (∀ f, f < 16 → cell (wsum M bu n) f = csn M bu f n) ∧
      ∀ f, f < 16 → csn M bu f n ≤ 1023 * n
  | 0, _ => ⟨by simp [wsum], fun f _ => by simp [wsum, csn, cell], fun f _ => by simp [csn]⟩
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := wsum_cells M bu hc n (by omega)
    have hadd := cell_add (x := wsum M bu n) (y := W M bu n) h1 (word_lt M _) (fun f hf => by
      rw [h2 f hf]; have := h3 f hf; have := hc n f (by omega) hf; omega)
    refine ⟨hadd.1, fun f hf => ?_, fun f hf => ?_⟩
    · show cell (wsum M bu n + W M bu n) f = _
      rw [csn_succ, hadd.2 f hf, h2 f hf]
    · rw [csn_succ]; have := h3 f hf; have := hc n f (by omega) hf; omega

/-! ## Extracting the transposed cells (v4: moved to bits `13 … 28` of each lane) -/

theorem ut_lt (x : UInt256) : x.toNat < 2 ^ 256 := x.val.isLt

theorem mask13_bits : ∀ i, i < 256 →
    (3369941911376413686827244460163711965458833623645077397550107975680 : Nat).testBit i = decide (13 ≤ i % 64 ∧ i % 64 < 29) := by
  decide +kernel

theorem testBit_cell (x f e : Nat) : (cell x f).testBit e = (decide (e < 16) && x.testBit (16 * f + e)) := by
  unfold cell
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem lanes_cell13 (x k : Nat) : Lanes fun r => cell x (4 * k + r) * 2 ^ 13 := fun r _ => by
  show cell x (4 * k + r) * 2 ^ 13 < 2 ^ 64
  have := cell_lt x (4 * k + r); omega

theorem ext_nat {Tn xn : Nat} (hT : ∀ i, i < 256 → Tn.testBit i = xn.testBit (tp i)) {k : Nat} (hk : k < 4)
    {Y : Nat} (hY : ∀ i, i < 256 → 13 ≤ i % 64 → i % 64 < 29 → Y.testBit i = Tn.testBit (i + 16 * k - 13)) :
    (3369941911376413686827244460163711965458833623645077397550107975680 &&& Y) = pack4 fun r => cell xn (4 * k + r) * 2 ^ 13 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_pk (lanes_cell13 xn k)]
  by_cases hi : i < 256
  · rw [mask13_bits i hi, Nat.testBit_mul_two_pow]
    by_cases hm : 13 ≤ i % 64 ∧ i % 64 < 29
    · rw [hY i hi hm.1 hm.2, hT _ (by omega), testBit_cell]
      simp only [hm, hi, decide_true, Bool.true_and, show 13 ≤ i % 64 from hm.1,
        show i % 64 - 13 < 16 by omega]
      have e : tp (i + 16 * k - 13) = 16 * (4 * k + i / 64) + (i % 64 - 13) := by unfold tp; omega
      simp [e]
    · simp only [hm, decide_false, Bool.false_and, hi, decide_true, Bool.true_and]
      by_cases h13 : 13 ≤ i % 64
      · rw [testBit_cell]; simp [h13, show ¬ i % 64 - 13 < 16 by omega]
      · simp [h13]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num : (3369941911376413686827244460163711965458833623645077397550107975680 : Nat) < 2 ^ 256)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hi]

theorem extract0 (x T : UInt256) (hT : ∀ i, i < 256 → T.toNat.testBit i = x.toNat.testBit (tp i)) :
    (UInt256.ofNat 3369941911376413686827244460163711965458833623645077397550107975680).land (T.shiftLeft (UInt256.ofNat 13)) =
      UInt256.ofNat (pack4 fun r => cell x.toNat (4 * 0 + r) * 2 ^ 13) := by
  rw [← ofNat_toNat T, ofNat_shl _ (by norm_num), ofNat_land]
  congr 1
  refine ext_nat (Tn := T.toNat) hT (by norm_num) ?_
  intro i hi h1 h2
  rw [Nat.shiftLeft_eq, Nat.testBit_mul_two_pow, decide_eq_true (by omega), Bool.true_and]
  simp

theorem extract (x T : UInt256) (hT : ∀ i, i < 256 → T.toNat.testBit i = x.toNat.testBit (tp i))
    {k sh : Nat} (hk : k < 4) (hk0 : 0 < k) (hsh : sh = 16 * k - 13) :
    (UInt256.ofNat 3369941911376413686827244460163711965458833623645077397550107975680).land (T.shiftRight (UInt256.ofNat sh)) =
      UInt256.ofNat (pack4 fun r => cell x.toNat (4 * k + r) * 2 ^ 13) := by
  rw [← ofNat_toNat T, ofNat_shr _ (by omega), ofNat_land, Nat.mod_eq_of_lt (ut_lt T)]
  congr 1
  refine ext_nat (Tn := T.toNat) hT hk ?_
  intro i hi h1 h2
  rw [Nat.testBit_shiftRight, hsh]
  congr 1; omega

/-! ## The running count -/

theorem spOff_eq : spOff = 1072788607 := by
  unfold spOff; norm_num [Fips204.q, Fips204.gamma2]

theorem gval_lt (n : Nat) : pack4 (fun _ => spOff - n) < 2 ^ 256 := by
  rw [spOff_eq]; simp only [pack4]; omega

theorem gval_lt' (n : Nat) : pack4 (fun _ => 1072788607 - n) < 2 ^ 256 := by
  simp only [pack4]; omega

theorem g_zero {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {M : ByteArray}
    (hnn : word M 4000 = negCount c) :
    c4e M = UInt256.ofNat (pack4 fun _ => spOff - N c 0) := by
  have hz := N_zero h
  unfold c4e
  rw [hnn, ofNat_sub (by omega) (by norm_num), ofNat_mul, ofNat_sub]
  · congr 1; rw [spOff_eq]; simp only [pack4]; omega
  · omega
  · norm_num

theorem N_le (c : Fips204.Poly) (t : Nat) : N c t ≤ 256 := by
  unfold N
  have := List.length_filter_le (fun p => decide ((p < t ∧ c[p]! = -1) ∨ (t ≤ p ∧ c[p]! = 1)))
    (List.range 256)
  simp only [List.length_range] at this
  omega

theorem REP_val : REP = 6277101735386680764176071790128604879584176795969512275969 := by
  unfold REP pack4; norm_num

theorem g_step {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {t' : Nat} (ht : t' < 256) :
    UInt256.ofNat (pack4 fun _ => spOff - N c t') - UInt256.ofNat (codeOf c[t']!) =
      UInt256.ofNat (pack4 fun _ => spOff - N c (t' + 1)) := by
  have hs := N_step h ht
  have h1 := N_le c t'
  have h2 := N_le c (t' + 1)
  rw [spOff_eq] at *
  rcases h.coeff t' ht with hc | hc | hc
  · simp only [hc, codeOf, if_true] at hs ⊢
    simp at hs
    rw [ofNat_sub (by omega) (gval_lt' _), hs]; simp
  · have hne : (1 : Int) ≠ 0 := by decide
    have hne' : (1 : Int) ≠ -1 := by decide
    simp only [hc, codeOf, hne, hne', if_false, if_true] at hs ⊢
    simp at hs
    apply EvmProof.Word.word_ext
    rw [EvmProof.Word.word_toNat_sub, toNat_ofNat_of_lt (gval_lt' _),
      toNat_ofNat_of_lt (by rw [REP_val]; norm_num), toNat_ofNat_of_lt (gval_lt' _), REP_val]
    simp only [pack4]; omega
  · have hne : (-1 : Int) ≠ 0 := by decide
    have hne' : (-1 : Int) ≠ 1 := by decide
    simp only [hc, codeOf, hne, hne', if_false, if_true] at hs ⊢
    simp at hs
    rw [REP_val]
    have hle : 6277101735386680764176071790128604879584176795969512275969 ≤
        pack4 (fun _ => 1072788607 - N c t') := by simp only [pack4]; omega
    have heq : pack4 (fun _ => 1072788607 - N c t') - 6277101735386680764176071790128604879584176795969512275969 =
        pack4 (fun _ => 1072788607 - N c (t' + 1)) := by simp only [pack4]; omega
    rw [ofNat_sub hle (gval_lt' _), heq]

theorem pack4_congr {v w : Nat → Nat} (h : ∀ r, r < 4 → v r = w r) : pack4 v = pack4 w := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- An emitted word: the count word minus the shifted window sums, lane-wise without borrow. -/
theorem emit_sub {n : Nat} {S : Nat → Nat} (hS : ∀ r, r < 4 → S r ≤ 1023 * 39) (hn : n ≤ 256) :
    (UInt256.ofNat (pack4 fun _ => spOff - n) - UInt256.ofNat (pack4 fun r => S r * 2 ^ 13)).toNat =
      pack4 fun r => spOff - (2 ^ 13 * S r + n) := by
  have h0 := hS 0 (by omega); have h1 := hS 1 (by omega)
  have h2 := hS 2 (by omega); have h3 := hS 3 (by omega)
  rw [spOff_eq, ofNat_sub (by simp only [pack4]; omega) (gval_lt' _), toNat_ofNat_of_lt (by simp only [pack4]; omega)]
  simp only [pack4]; omega

/-! ## One iteration, in terms of the input memory `m` -/

section
variable {m : ByteArray} {c : Fips204.Poly} {cd : ByteArray} {ps : List Nat}

/-- What `csum` needs to know about its input memory. -/
structure Pre (m : ByteArray) (c : Fips204.Poly) (cd : ByteArray) (ps : List Nat) : Prop where
  facts : CFacts c ps
  cw : ∀ t, t < 256 → word m (CW + 32 * t) = codeOf c[t]!
  nn : word m NNEG = negCount c
  base : ∀ i, i < 39 → word m (BASES + 32 * i) = baseOf c ps[i]!
  tt : TTable m TT cd

theorem code_word (h : Pre m c cd ps) {u k a : Nat} (hu : u < 64) (hk : k < 4)
    (ha : a = 12288 + 128 * u + 32 * k) : word (stU m u).1 a = codeOf c[4 * u + k]! := by
  rw [stU_other m (by omega) u (by omega), ← h.cw (4 * u + k) (by omega)]
  congr 1; unfold CW; omega

/-- The count word after `k` codes of iteration `u`. -/
theorem g_iter (h : Pre m c cd ps) : ∀ u, u ≤ 64 →
    (stU m u).2 = UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u))
  | 0, _ => g_zero h.facts h.nn
  | u + 1, hu => by
    show c4g4 (stU m u).1 (12288 + 128 * u) (stU m u).2 = _
    unfold c4g4 c4g3 c4g2 c4g1
    rw [g_iter h u (by omega), code_word h (k := 0) (by omega) (by omega) (by omega),
      code_word h (k := 1) (by omega) (by omega) (by omega),
      code_word h (k := 2) (by omega) (by omega) (by omega),
      code_word h (k := 3) (by omega) (by omega) (by omega), Nat.add_zero,
      g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega), g_step h.facts (t' := 4 * u + 3) (by omega)]
    congr 3

theorem be16_frame (u : Nat) (hu : u ≤ 64) {a : Nat} (ha : a + 2 ≤ 26624) :
    be16 (stU m u).1 a = be16 m a := by
  unfold be16; rw [stU_byte m (by omega) u hu, stU_byte m (by omega) u hu]

/-- Cell `f` of window word `i` at iteration `u`. -/
theorem cell_W (h : Pre m c cd ps) {u i f : Nat} (hu : u < 64) (hi : i < 39) (hf : f < 16) :
    cell (W (stU m u).1 (20480 - 32 * u) i) f =
      tEntry cd (f % 4) (4 * u + f / 4 + 256 - ps[i]! + if c[ps[i]!]! = -1 then 256 else 0) := by
  have hp : ps[i]! < 256 := by
    have hmem : ps[i]! ∈ ps := by
      rw [getElem!_pos ps i (by rw [h.facts.len]; exact hi)]; exact List.getElem_mem _
    exact ((h.facts.mem _).1 hmem).1
  unfold W
  rw [stU_other m (a := 40960 + 32 * i) (by omega) u (by omega), show 40960 + 32 * i = BASES + 32 * i by rfl,
    h.base i hi, cell_word _ _ hf, be16_frame u (by omega) (by unfold baseOf; split_ifs <;> omega)]
  have ht := h.tt (4 * u + f / 4 + 256 - ps[i]! + if c[ps[i]!]! = -1 then 256 else 0)
    (by split_ifs <;> omega) (f % 4) (by omega)
  rw [← ht]
  congr 1
  unfold baseOf TT
  split_ifs <;> omega

theorem cell_W_le (h : Pre m c cd ps) {u : Nat} (hu : u < 64) :
    ∀ i f, i < 39 → f < 16 → cell (W (stU m u).1 (20480 - 32 * u) i) f ≤ 1023 := fun i f hi hf => by
  rw [cell_W h hu hi hf]; exact tEntry_le _ _ _

theorem base_stU {u : Nat} (hu : u ≤ 64) :
    ∀ i, i < 11 → word m (40960 + 32 * i) = word (stU m u).1 (40960 + 32 * i) := fun i hi =>
  (stU_other m (by omega) u hu).symm

/-- The window sums of iteration `u`. -/
theorem sum_cells (h : Pre m c cd ps) {u k r : Nat} (hu : u < 64) (hk : k < 4) (hr : r < 4) (cw sp : Nat)
    (g : UInt256) :
    cell (s3 m (stU m u).1 (20480 - 32 * u) cw sp g).toNat (4 * k + r) = sPrime c cd r (4 * u + k) ∧
      cell (s3 m (stU m u).1 (20480 - 32 * u) cw sp g).toNat (4 * k + r) ≤ 1023 * 39 := by
  obtain ⟨h1, h2, h3⟩ := wsum_cells _ _ (fun i f hi hf => cell_W_le h hu i f hi hf) 39 le_rfl
  rw [s3_toNat _ _ _ _ _ _ (base_stU (by omega)), Nat.mod_eq_of_lt h1, h2 _ (by omega)]
  refine ⟨?_, h3 _ (by omega)⟩
  rw [sPrime_ps h.facts, csn]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [cell_W h hu hi (by omega), show (4 * k + r) % 4 = r by omega, show (4 * k + r) / 4 = k by omega]

theorem emit_lanes (h : Pre m c cd ps) {u k : Nat} (hu : u < 64) (hk : k < 4) (cw sp : Nat) (g : UInt256)
    (hg : UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + k + 1)) = G) :
    (G - UInt256.ofNat (pack4 fun r => cell (s3 m (stU m u).1 (20480 - 32 * u) cw sp g).toNat (4 * k + r) * 2 ^ 13)).toNat =
      pack4 fun r => spOff - (2 ^ 13 * sPrime c cd r (4 * u + k) + nNeg c (4 * u + k)) := by
  rw [← hg, emit_sub (fun r hr => (sum_cells h hu hk hr cw sp g).2) (N_le _ _), nNeg_eq]
  exact pack4_congr fun r hr => by rw [(sum_cells h hu hk hr cw sp g).1]

/-- The word stored for `t = 4 u + k`. -/
theorem store_val (h : Pre m c cd ps) {u k : Nat} (hu : u < 64) (hk : k < 4) :
    word (stU m (u + 1)).1 (26624 + 128 * u + 32 * k) =
      pack4 fun r => spOff - (2 ^ 13 * sPrime c cd r (4 * u + k) + nNeg c (4 * u + k)) := by
  show word (csMem m (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2) _ = _
  have hg := g_iter h u (by omega)
  have hT := fun i (hi : i < 256) => tp_bits (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2
    (s3 m (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2) hi
  have c0 := code_word h (k := 0) (a := 12288 + 128 * u) hu (by omega) (by omega)
  have c1 := code_word h (k := 1) (a := 32 + (12288 + 128 * u)) hu (by omega) (by omega)
  have c2 := code_word h (k := 2) (a := 64 + (12288 + 128 * u)) hu (by omega) (by omega)
  have c3 := code_word h (k := 3) (a := 96 + (12288 + 128 * u)) hu (by omega) (by omega)
  have g1 : c4g1 (stU m u).1 (12288 + 128 * u) (stU m u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 0 + 1)) := by
    unfold c4g1; rw [hg, c0, Nat.add_zero, g_step h.facts (by omega)]
  have g2 : c4g2 (stU m u).1 (12288 + 128 * u) (stU m u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 1 + 1)) := by
    unfold c4g2; rw [g1, c1, Nat.add_zero, g_step h.facts (by omega)]
  have g3 : c4g3 (stU m u).1 (12288 + 128 * u) (stU m u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 2 + 1)) := by
    unfold c4g3; rw [g2, c2, g_step h.facts (by omega)]
  have g4 : c4g4 (stU m u).1 (12288 + 128 * u) (stU m u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 3 + 1)) := by
    unfold c4g4; rw [g3, c3, g_step h.facts (by omega)]
  interval_cases k
  · rw [show 26624 + 128 * u + 32 * 0 = 26624 + 128 * u by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w0 sT
    rw [extract0 _ _ hT]
    exact emit_lanes h hu (k := 0) (by omega) _ _ _ g1.symm
  · rw [show 26624 + 128 * u + 32 * 1 = 32 + (26624 + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w1 sT
    rw [extract _ _ hT (k := 1) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 1) (by omega) _ _ _ g2.symm
  · rw [show 26624 + 128 * u + 32 * 2 = 64 + (26624 + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w2 sT
    rw [extract _ _ hT (k := 2) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 2) (by omega) _ _ _ g3.symm
  · rw [show 26624 + 128 * u + 32 * 3 = 96 + (26624 + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w3 sT
    rw [extract _ _ hT (k := 3) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 3) (by omega) _ _ _ g4.symm

end

theorem stU_later (m : ByteArray) {a u : Nat} (ha : a + 32 ≤ 26624 + 128 * (u + 1)) :
    ∀ u', u + 1 ≤ u' → u' ≤ 64 → word (stU m u').1 a = word (stU m (u + 1)).1 a
  | 0, h1, _ => by omega
  | u' + 1, h1, h2 => by
    by_cases he : u + 1 = u' + 1
    · rw [he]
    · show word (csMem _ _ _ _ _ _) a = _
      rw [csMem_other _ _ _ _ _ _ (by omega), stU_later m ha u' (by omega) (by omega)]

/-- The contract body of `csum_call`. -/
theorem csum_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.csum ret tail) (m : ByteArray)
    (hb : ∀ i, i < Fips204.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ c : Fips204.Poly, c.size = 256 → (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) →
        CRep m c → TTable m TT s.executionEnv.calldata →
        ∀ t, t < 256 → word m' (SP + 32 * t) =
          pack4 fun r => spOff - (2 ^ 13 * sPrime c s.executionEnv.calldata r t + nNeg c t)) ∧
      FrameExcept m m' [(SP, SP + 8192)] ∧
      Call s Entry.csum [wd SP, wd TT] ret tail m [] m' Gas.csum := by
  have htail : tail.length ≤ 960 := by have := hr.depth; simp only [Stack.csum, Stack.leaf] at this; omega
  refine ⟨(stU m 64).1, ?_, fun a ha => ?_, ?_⟩
  · intro c hsz hco hrep htt t ht
    obtain ⟨hcw, hnn, ps, hlen, hnd, hmem, hbase⟩ := hrep
    have h : Pre m c s.executionEnv.calldata ps :=
      ⟨⟨hco, hlen, hnd, hmem⟩, hcw, hnn, fun i hi => hbase i hi, htt⟩
    rw [show SP + 32 * t = 26624 + 128 * (t / 4) + 32 * (t % 4) by unfold SP; omega,
      stU_later m (u := t / 4) (by omega) 64 (by omega) le_rfl, store_val h (by omega) (by omega),
      show 4 * (t / 4) + t % 4 = t by omega]
  · have h : a < 26624 ∨ 26624 + 8192 ≤ a := by
      have := ha (SP, SP + 8192) (by simp)
      simp only [SP] at this; omega
    exact stU_byte m h 64 le_rfl
  · rw [call_iff, Entry.csum, Gas.csum]
    have h := cs_run hs htail hr.jumpdest hr.small m (fun i hi => hb i hi)
    exact (h.mono (by norm_num)).of_eq (by simp [SP, TT]) rfl

end MlDsaOpt44.Proofs.CS4
