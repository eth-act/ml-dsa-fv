import MlDsaOpt44.Fn.Ntt.Sem
/-!
# Butterflies against the layer models, pass invariants, stores and loops (WP7)

* `ct_step`/`gs_step`/`gsS_step`/`premont_step`: one butterfly (or one
  `premont` load) of the bytecode realises one butterfly of `fwdL`/`invL`;
* `PassInv` bookkeeping across the eight (or four) stores of a loop body;
* `word_wrU`, `frame_wrU`: reading back and framing the stores;
* `reach_iter`: a loop whose memory is known only through an invariant.
-/

namespace MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs

theorem divmod_hi {ia len : Nat} (h : ia % (2 * len) < len) :
    (ia + len) % (2 * len) = ia % (2 * len) + len ∧ (ia + len) / (2 * len) = ia / (2 * len) := by
  have h2 : 0 < 2 * len := by omega
  have e := Nat.div_add_mod ia (2 * len)
  have hlt : ia % (2 * len) + len < 2 * len := by omega
  have hx : ia + len = (ia % (2 * len) + len) + 2 * len * (ia / (2 * len)) := by
    generalize 2 * len * (ia / (2 * len)) = X at e ⊢
    omega
  constructor
  · rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [hx, Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-! ## Butterflies against the models -/

theorem fwdL_succ (h : Nat → F) (L : Nat) : fwdL h (L + 1) = fwdLayer (128 / 2 ^ L) (fwdL h L) := rfl

theorem invL_succ (h : Nat → F) (L : Nat) :
    invL h (L + 1) = invLayer (2 ^ L) (2 ^ (8 - L)) (invL h L) := rfl

theorem ct_step (h : Nat → Nat → F) (L len ia ib m z : Nat) {xa xb : UInt256}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hz : z = zm m)
    (ha : LOK xa (Bf L) (fun k => fwdL (h k) L ia)) (hb : LOK xb (Bf L) (fun k => fwdL (h k) L ib)) :
    LOK (ctA xa xb (UInt256.ofNat z)) (Bf (L + 1)) (fun k => fwdL (h k) (L + 1) ia) ∧
      LOK (ctB (UInt256.ofNat 105209460187928082099348286046428385038300376303896864318478598146)
        xa xb (UInt256.ofNat z)) (Bf (L + 1)) (fun k => fwdL (h k) (L + 1) ib) := by
  subst hz hib
  have hBf : Bf L ≤ 2 ^ 28 := by unfold Bf; omega
  have hB1 : Bf (L + 1) = Bf L + 2 * 8380417 := by unfold Bf; ring
  have hzq : zm m < 2 ^ 23 := Nat.lt_trans (zm_lt m) (by norm_num)
  obtain ⟨h1, h2⟩ := ct_core ha hb hBf hzq (zm_cast m)
  obtain ⟨hhi, hdiv⟩ := divmod_hi hlo
  rw [hB1]
  constructor
  · refine h1.congr (fun k _ => ?_)
    rw [fwdL_succ, ← hlen]
    unfold fwdLayer
    rw [if_pos hlo, ← hm]
  · refine h2.congr (fun k _ => ?_)
    rw [fwdL_succ, ← hlen]
    unfold fwdLayer
    rw [if_neg (by rw [hhi]; omega), hdiv, ← hm, Nat.add_sub_cancel]

theorem Bi_le {L : Nat} (hL : L < 8) : Bi L ≤ 9662627968 := by
  unfold Bi Bu; interval_cases L <;> norm_num

theorem gs_step (h : Nat → Nat → F) (L len m0 ia ib m z : Nat) {xa xb : UInt256}
    (hL : L < 7) (hlen : len = 2 ^ L) (hm0 : m0 = 2 ^ (8 - L)) (hlo : ia % (2 * len) < len)
    (hib : ib = ia + len) (hm : m = m0 - ia / (2 * len) - 1) (hz : z = zm m)
    (ha : LOK xa (Bi L) (fun k => invL (h k) L ia)) (hb : LOK xb (Bi L) (fun k => invL (h k) L ib)) :
    LOK (gsA xa xb) (Bi (L + 1)) (fun k => invL (h k) (L + 1) ia) ∧
      LOK (gsB (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
        xa xb (UInt256.ofNat z)) (Bi (L + 1)) (fun k => invL (h k) (L + 1) ib) := by
  subst hz hib
  have hB1 : Bi (L + 1) = 2 * Bi L := by unfold Bi; ring
  have hBu : Bu ≤ 2 * Bi L := by
    unfold Bi
    calc Bu ≤ 2 ^ L * Bu := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ 2 * (2 ^ L * Bu) := by omega
  obtain ⟨h1, h2⟩ := gs_core ha hb (Bi_le (by omega)) hBu (zm_lt m) (zm_cast m)
  obtain ⟨hhi, hdiv⟩ := divmod_hi hlo
  rw [hB1]
  constructor
  · refine h1.congr (fun k _ => ?_)
    rw [invL_succ, ← hlen, ← hm0]
    unfold invLayer
    rw [if_pos hlo]
  · refine h2.congr (fun k _ => ?_)
    rw [invL_succ, ← hlen, ← hm0]
    unfold invLayer
    rw [if_neg (by rw [hhi]; omega), hdiv, ← hm, Nat.add_sub_cancel]

theorem f41978 : ((41978 : Nat) : F) = Sc * R := by decide +kernel

theorem z4404704 : ((4404704 : Nat) : F) = (Sc * ζ 1) * R := by
  unfold ζ
  decide +kernel

theorem gsS_step (h : Nat → Nat → F) (ia ib : Nat) {xa xb : UInt256}
    (hlo : ia < 128) (hib : ib = ia + 128)
    (ha : LOK xa (Bi 7) (fun k => invL (h k) 7 ia)) (hb : LOK xb (Bi 7) (fun k => invL (h k) 7 ib)) :
    LOK (gsAs (UInt256.ofNat 41978) xa xb) Bu (fun k => Sc * invL (h k) 8 ia) ∧
      LOK (gsB (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
        xa xb (UInt256.ofNat 4404704)) Bu (fun k => Sc * invL (h k) 8 ib) := by
  subst hib
  obtain ⟨h1, h2⟩ := gsS_core ha hb (Bi_le (by norm_num)) (by norm_num) f41978 (by norm_num) z4404704
  constructor
  · refine h1.congr (fun k _ => ?_)
    rw [show invL (h k) 8 = invLayer 128 2 (invL (h k) 7) from rfl]
    unfold invLayer
    rw [if_pos (by omega)]
  · refine h2.congr (fun k _ => ?_)
    rw [show invL (h k) 8 = invLayer 128 2 (invL (h k) 7) from rfl]
    unfold invLayer
    rw [if_neg (by omega), show 2 - (ia + 128) / (2 * 128) - 1 = 1 by omega, Nat.add_sub_cancel]
    ring

theorem premont_step (h : Nat → Nat → F) (t w : Nat)
    (hw : LOK (UInt256.ofNat w) (2 ^ 58) (fun k => h k t)) :
    LOK (UInt256.ofNat (montE w)) (Bi 0) (fun k => invL (scaleR h k) 0 t) :=
  (premont_core hw).mono (by norm_num [Bi])

/-! ## Pass invariants -/

section
variable {M M' : ByteArray} {P : Nat} {D D' S : Nat → Prop} [DecidablePred D] [DecidablePred D']
  {Bin Bout : Nat} {Pre Post : Nat → Nat → F}

theorem passInv_pre (hI : PassInv M P D Bin Bout Pre Post) {t : Nat} (ht : t < 256) (hD : ¬ D t) :
    LOK (UInt256.ofNat (word M (P + 32 * t))) Bin (fun k => Pre k t) := by
  have := hI t ht
  simp only [if_neg hD] at this
  exact this

theorem passInv_store (hI : PassInv M P D Bin Bout Pre Post) (hD' : ∀ t, D' t ↔ D t ∨ S t)
    (hnew : ∀ t, t < 256 → S t →
      LOK (UInt256.ofNat (word M' (P + 32 * t))) Bout (fun k => Post k t))
    (hold : ∀ t, t < 256 → ¬ S t → word M' (P + 32 * t) = word M (P + 32 * t)) :
    PassInv M' P D' Bin Bout Pre Post := by
  intro t ht
  by_cases hS : S t
  · have hd : D' t := (hD' t).2 (Or.inr hS)
    simp only [if_pos hd]
    exact hnew t ht hS
  · rw [hold t ht hS]
    have := hI t ht
    by_cases hd : D t
    · simp only [if_pos hd, if_pos ((hD' t).2 (Or.inl hd))] at this ⊢
      exact this
    · have hd' : ¬ D' t := fun h' => ((hD' t).1 h').elim hd hS
      simp only [if_neg hd, if_neg hd'] at this ⊢
      exact this

/-- Start a pass from the words of the previous one. -/
theorem passInv_init (h : ∀ t, t < 256 → LOK (UInt256.ofNat (word M (P + 32 * t))) Bin (fun k => Pre k t))
    (hnone : ∀ t, ¬ D t) : PassInv M P D Bin Bout Pre Post := by
  intro t ht
  simp only [if_neg (hnone t)]
  exact h t ht

/-- End of a pass: every word is processed. -/
theorem passInv_done (hI : PassInv M P D Bin Bout Pre Post) (hall : ∀ t, t < 256 → D t) :
    ∀ t, t < 256 → LOK (UInt256.ofNat (word M (P + 32 * t))) Bout (fun k => Post k t) := by
  intro t ht
  have := hI t ht
  simp only [if_pos (hall t ht)] at this
  exact this

end

/-! ## Stores -/

theorem word_wrU (m : ByteArray) (a x : Nat) (v : UInt256) (h : x = a ∨ x + 32 ≤ a ∨ a + 32 ≤ x) :
    word (wrU m a v) x = if x = a then v.toNat else word m x := by
  unfold wrU
  rcases h with rfl | h
  · rw [if_pos rfl, word_mstore _ _ _ (show v.toNat < 2 ^ 256 from v.val.isLt)]
  · rw [if_neg (by omega), word_mstore_disjoint _ _ h]

theorem frame_wrU {m m' : ByteArray} {P a : Nat} (v : UInt256)
    (h : FrameExcept m m' [(P, P + 8192)]) (ha1 : P ≤ a) (ha2 : a + 32 ≤ P + 8192) :
    FrameExcept m (wrU m' a v) [(P, P + 8192)] := by
  unfold wrU
  refine (h.trans (FrameExcept.mstore _ _ _)).mono ?_
  intro r hr
  refine ⟨(P, P + 8192), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

theorem tblAt_frame {m m' : ByteArray} {P : Nat} (htbl : TblAt m)
    (hf : FrameExcept m m' [(P, P + 8192)]) (hP : 12032 ≤ P) : TblAt m' := by
  intro i hi
  rw [FrameExcept.word hf (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; unfold TBL; omega)]
  exact htbl i hi

/-! ## Zeta records -/

theorem nttRec_B (b u : Nat) (hb : b < 8) (hu : u < 7) :
    nttRec (7 * b + u) = if u = 0 then zm (8 + b) else if u = 1 then zm (16 + 2 * b)
      else if u = 2 then zm (17 + 2 * b) else zm (32 + 4 * b + (u - 3)) := by
  have h1 : (7 * b + u) / 7 = b := by omega
  have h2 : (7 * b + u) % 7 = u := by omega
  simp only [nttRec, show 7 * b + u < 56 by omega, if_true, h1, h2]

theorem nttRec_C (b u : Nat) (hu : u < 3) :
    nttRec (56 + 3 * b + u) = if u = 0 then zm (64 + b) else if u = 1 then zm (128 + 2 * b)
      else zm (129 + 2 * b) := by
  have h1 : (56 + 3 * b + u - 56) / 3 = b := by omega
  have h2 : (56 + 3 * b + u - 56) % 3 = u := by omega
  simp only [nttRec, show ¬ 56 + 3 * b + u < 56 by omega, if_false, h1, h2]

theorem recB {b : Nat} (hb : b < 8) :
    nttRec (7 * b) = zm (8 + b) ∧ nttRec (7 * b + 1) = zm (16 + 2 * b) ∧
      nttRec (7 * b + 2) = zm (17 + 2 * b) ∧ nttRec (7 * b + 3) = zm (32 + 4 * b) ∧
      nttRec (7 * b + 4) = zm (32 + 4 * b + 1) ∧ nttRec (7 * b + 5) = zm (32 + 4 * b + 2) ∧
      nttRec (7 * b + 6) = zm (32 + 4 * b + 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using nttRec_B b 0 hb (by norm_num)
  · simpa using nttRec_B b 1 hb (by norm_num)
  · simpa using nttRec_B b 2 hb (by norm_num)
  · simpa using nttRec_B b 3 hb (by norm_num)
  · simpa using nttRec_B b 4 hb (by norm_num)
  · simpa using nttRec_B b 5 hb (by norm_num)
  · simpa using nttRec_B b 6 hb (by norm_num)

theorem recC {b : Nat} (_hb : b < 64) :
    nttRec (56 + 3 * b) = zm (64 + b) ∧ nttRec (56 + 3 * b + 1) = zm (128 + 2 * b) ∧
      nttRec (56 + 3 * b + 2) = zm (129 + 2 * b) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using nttRec_C b 0 (by norm_num)
  · simpa using nttRec_C b 1 (by norm_num)
  · simpa using nttRec_C b 2 (by norm_num)

/-! ## Immediate zetas of passes A -/

theorem zmi1 : zm 1 = 25847 := by decide +kernel
theorem zmi2 : zm 2 = 5771523 := by decide +kernel
theorem zmi3 : zm 3 = 7861508 := by decide +kernel
theorem zmi4 : zm 4 = 237124 := by decide +kernel
theorem zmi5 : zm 5 = 7602457 := by decide +kernel
theorem zmi6 : zm 6 = 7504169 := by decide +kernel
theorem zmi7 : zm 7 = 466468 := by decide +kernel

theorem frame_trans1 {a b c : ByteArray} {P : Nat} (h1 : FrameExcept a b [(P, P + 8192)])
    (h2 : FrameExcept b c [(P, P + 8192)]) : FrameExcept a c [(P, P + 8192)] :=
  (h1.trans h2).mono (fun r hr => ⟨(P, P + 8192), by simp, by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨le_rfl, le_rfl⟩⟩)

theorem land127 (x : Nat) : 127 &&& x = x % 128 := by
  rw [Nat.and_comm, show (127 : Nat) = 2 ^ 7 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

/-! ## Loops with an invariant on memory -/

theorem reach_iter {S : Nat → ByteArray → State} {Q : Nat → ByteArray → Prop} {c : Nat} :
    ∀ n, (∀ i M, i < n → Q i M → ∃ M', Q (i + 1) M' ∧ Reach (S i M) (S (i + 1) M') c) →
      ∀ M, Q 0 M → ∃ M', Q n M' ∧ Reach (S 0 M) (S n M') (n * c)
  | 0, _, M, hM => ⟨M, hM, by simpa using Reach.refl (S 0 M)⟩
  | n + 1, h, M, hM => by
    obtain ⟨M₁, hP₁, hR₁⟩ := reach_iter n (fun i M hi => h i M (by omega)) M hM
    obtain ⟨M₂, hP₂, hR₂⟩ := h n M₁ (by omega) hP₁
    exact ⟨M₂, hP₂, by simpa [Nat.succ_mul] using hR₁.trans hR₂⟩

end MlDsaOpt44.Proofs.NttW
