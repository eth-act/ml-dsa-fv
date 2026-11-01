import MlDsaOpt44.Fn.Ct.CsumIter
import MlDsaOpt44.Fn.Ct.CsumT
import MlDsaOpt44.Fn.Ct.CsumSpec
import MlDsaOpt44.Fn.Ball.Defs
/-!
# `csum` (WP10): the stored words and the contract body
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOpt44.Proofs.CS

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.L10

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

theorem s3_toNat (M : ByteArray) (bu cw sp : Nat) (g : UInt256) :
    (s3 M bu cw sp g).toNat = wsum M bu 39 % 2 ^ 256 := by
  simp only [s3, s2, s1, cs3o0, cs2o0, cs1o0, EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]
  rw [wsum_39]
  simp only [W, Nat.reduceMul, Nat.reduceAdd]
  apply congrArg (· % 2 ^ 256)
  omega

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

/-! ## Extracting the transposed cells -/

theorem ut_lt (x : UInt256) : x.toNat < 2 ^ 256 := x.val.isLt

theorem LM16_eq : (411369862228566123880278864766078120783549026323861987005628415 : Nat) =
    pack4 fun _ => 2 ^ 16 - 1 := by unfold pack4; norm_num

theorem lanes_cell (x k : Nat) : Lanes fun r => cell x (4 * k + r) := fun r _ =>
  Nat.lt_of_lt_of_le (cell_lt _ _) (by norm_num)

theorem lanes_m16 : Lanes fun _ => 2 ^ 16 - 1 := fun r _ => by norm_num

theorem extract_bits (T : Nat) (x : Nat) (k : Nat) (hk : k < 4)
    (hT : ∀ i, i < 256 → T.testBit i = x.testBit (tp i)) :
    (pack4 (fun _ => 2 ^ 16 - 1) &&& (T >>> (16 * k))) = pack4 fun r => cell x (4 * k + r) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_pk lanes_m16, testBit_pk (lanes_cell x k), Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 256
  · by_cases he : i % 64 < 16
    · rw [hT _ (by omega)]
      unfold cell
      rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      simp only [hi, he, decide_true, Bool.true_and]
      congr 1; unfold tp; omega
    · simp only [hi, he, decide_true, decide_false, Bool.true_and, Bool.false_and]
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (cell_lt _ _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · simp [hi]

theorem extract (M : ByteArray) (bu cw sp : Nat) (g x : UInt256) {k sh : Nat} (hk : k < 4) (hsh : sh = 16 * k)
    (hk0 : 0 < k) :
    (UInt256.ofNat 411369862228566123880278864766078120783549026323861987005628415).land
        ((cs4o0 M bu cw sp g x).shiftRight (UInt256.ofNat sh)) =
      UInt256.ofNat (pack4 fun r => cell x.toNat (4 * k + r)) := by
  rw [← ofNat_toNat (cs4o0 M bu cw sp g x), ofNat_shr _ (by omega),
    Nat.mod_eq_of_lt (ut_lt _), ofNat_land, LM16_eq, hsh,
    extract_bits _ _ k hk (fun i hi => tp_bits M bu cw sp g x hi)]

theorem extract0 (M : ByteArray) (bu cw sp : Nat) (g x : UInt256) :
    (UInt256.ofNat 411369862228566123880278864766078120783549026323861987005628415).land
        (cs4o0 M bu cw sp g x) =
      UInt256.ofNat (pack4 fun r => cell x.toNat (4 * 0 + r)) := by
  rw [← ofNat_toNat (cs4o0 M bu cw sp g x), ofNat_land, LM16_eq,
    ← extract_bits _ _ 0 (by omega) (fun i hi => tp_bits M bu cw sp g x hi), Nat.mul_zero,
    Nat.shiftRight_zero]

/-- The emitted word. -/
theorem emit_val {G : Nat} (hG : G < 2 ^ 16) (Y : Nat → Nat) (hY : ∀ r, r < 4 → Y r < 2 ^ 16) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 * UInt256.ofNat G +
      (UInt256.ofNat (pack4 Y)).shiftLeft (UInt256.ofNat 13)).toNat = pack4 fun r => 2 ^ 13 * Y r + G := by
  have h0 := hY 0 (by omega); have h1 := hY 1 (by omega)
  have h2 := hY 2 (by omega); have h3 := hY 3 (by omega)
  rw [ofNat_mul, ofNat_shl _ (by norm_num), EvmProof.Word.ofNat_add_mod, toNat_ofNat_of_lt]
  · unfold pack4; rw [Nat.shiftLeft_eq]; ring
  · unfold pack4; rw [Nat.shiftLeft_eq]; omega

theorem pack4_congr {v w : Nat → Nat} (h : ∀ r, r < 4 → v r = w r) : pack4 v = pack4 w := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem N_lt (c : Fips204.Poly) (t' : Nat) : N c t' < 2 ^ 16 := by
  unfold N
  have := List.length_filter_le (fun p => decide ((p < t' ∧ c[p]! = -1) ∨ (t' ≤ p ∧ c[p]! = 1)))
    (List.range 256)
  simp only [List.length_range] at this
  omega

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

theorem g_iter (h : Pre m c cd ps) : ∀ u, u ≤ 64 → (stU m u).2 = UInt256.ofNat (N c (4 * u))
  | 0, _ => by
    show UInt256.ofNat 39 - UInt256.ofNat (word m 4000) = _
    rw [show word m 4000 = negCount c from h.nn, g_zero h.facts]
  | u + 1, hu => by
    show cs5g (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2
      (sT (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2) = _
    unfold cs5g
    rw [g_iter h u (by omega), code_word h (k := 0) (by omega) (by omega) (by omega),
      code_word h (k := 1) (by omega) (by omega) (by omega),
      code_word h (k := 2) (by omega) (by omega) (by omega),
      code_word h (k := 3) (by omega) (by omega) (by omega), Nat.add_zero,
      g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega), g_step h.facts (t' := 4 * u + 3) (by omega)]
    congr 2

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

/-- The window sums of iteration `u`. -/
theorem sum_cells (h : Pre m c cd ps) {u k r : Nat} (hu : u < 64) (hk : k < 4) (hr : r < 4) (cw sp : Nat)
    (g : UInt256) :
    cell (s3 (stU m u).1 (20480 - 32 * u) cw sp g).toNat (4 * k + r) = sPrime c cd r (4 * u + k) := by
  obtain ⟨h1, h2, -⟩ := wsum_cells _ _ (fun i f hi hf => cell_W_le h hu i f hi hf) 39 le_rfl
  rw [s3_toNat, Nat.mod_eq_of_lt h1, h2 _ (by omega), sPrime_ps h.facts, csn]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [cell_W h hu hi (by omega), show (4 * k + r) % 4 = r by omega, show (4 * k + r) / 4 = k by omega]

/-- The word stored for `t = 4 u + k`. -/
theorem store_val (h : Pre m c cd ps) {u k : Nat} (hu : u < 64) (hk : k < 4) :
    word (stU m (u + 1)).1 (26624 + 128 * u + 32 * k) =
      pack4 fun r => 2 ^ 13 * sPrime c cd r (4 * u + k) + nNeg c (4 * u + k) := by
  show word (csMem (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2) _ = _
  have hg := g_iter h u (by omega)
  interval_cases k
  · rw [show 26624 + 128 * u + 32 * 0 = 26624 + 128 * u by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w0 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), Nat.add_zero, g_step h.facts (by omega),
      extract0, emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 0) (by omega) hr, nNeg_eq, Nat.add_zero]
  · rw [show 26624 + 128 * u + 32 * 1 = 32 + (26624 + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w1 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), code_word h (k := 1) hu (by omega) (by omega),
      Nat.add_zero, g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      extract _ _ _ _ _ _ (k := 1) (by omega) rfl (by omega), emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 1) (by omega) hr, nNeg_eq]
  · rw [show 26624 + 128 * u + 32 * 2 = 64 + (26624 + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w2 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), code_word h (k := 1) hu (by omega) (by omega),
      code_word h (k := 2) hu (by omega) (by omega),
      Nat.add_zero, g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega),
      extract _ _ _ _ _ _ (k := 2) (by omega) rfl (by omega), emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 2) (by omega) hr, nNeg_eq]
  · rw [show 26624 + 128 * u + 32 * 3 = 96 + (26624 + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w3 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), code_word h (k := 1) hu (by omega) (by omega),
      code_word h (k := 2) hu (by omega) (by omega), code_word h (k := 3) hu (by omega) (by omega),
      Nat.add_zero, g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega), g_step h.facts (t' := 4 * u + 3) (by omega),
      extract _ _ _ _ _ _ (k := 3) (by omega) rfl (by omega), emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 3) (by omega) hr, nNeg_eq]

end

theorem stU_later (m : ByteArray) {a u : Nat} (ha : a + 32 ≤ 26624 + 128 * (u + 1)) :
    ∀ u', u + 1 ≤ u' → u' ≤ 64 → word (stU m u').1 a = word (stU m (u + 1)).1 a
  | 0, h1, _ => by omega
  | u' + 1, h1, h2 => by
    by_cases he : u + 1 = u' + 1
    · rw [he]
    · show word (csMem _ _ _ _ _) a = _
      rw [csMem_other _ _ _ _ _ (by omega), stU_later m ha u' (by omega) (by omega)]

/-- The contract body of `csum_call`. -/
theorem csum_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.csum ret tail) (m : ByteArray)
    (hb : ∀ i, i < Fips204.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ c : Fips204.Poly, c.size = 256 → (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) →
        CRep m c → TTable m TT s.executionEnv.calldata →
        ∀ t, t < 256 → word m' (SP + 32 * t) =
          pack4 fun r => 2 ^ 13 * sPrime c s.executionEnv.calldata r t + nNeg c t) ∧
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

end MlDsaOpt44.Proofs.CS
