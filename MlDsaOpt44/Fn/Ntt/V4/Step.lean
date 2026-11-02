import MlDsaOpt44.Fn.Ntt.V4.Sem
/-!
# v4 butterflies against the layer models, pass invariants, the UseHint store (WP G, H)

* `ct4m_step` (table zetas, Montgomery) / `ct4s_step` (pass A, Shoup): one
  forward butterfly of the bytecode realises one butterfly of `fwdL` and keeps
  the bias interval;
* `gs4_step` / `gsS4_step`: the v3 inverse lemmas for the swap-free `gsB4`;
* `PI` bookkeeping (generic predicates per word);
* `uh_store`: a stored UseHint word satisfies `UHP`; `uh_rd` reads the `SP`/`HP`
  words through the pass's own stores.
-/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.NttV4

theorem LI.congr {x : UInt256} {L : Nat} {g g' : Nat → F} (h : LI x L g)
    (hg : ∀ k, k < 4 → g k = g' k) : LI x L g' :=
  fun k hk => ⟨(h k hk).1, (h k hk).2.1, (h k hk).2.2.trans (hg k hk)⟩

/-! ## Forward butterflies against `fwdL` -/

theorem ct4_model {h : Nat → Nat → F} {L len ia ib m : Nat} {xa u : UInt256} {zv : F}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hzv : zv = ζ m)
    (ha : LI xa L (fun k => fwdL (h k) L ia))
    (hu : ∀ k, k < 4 → lane u.toNat k < U4 ∧ ((lane u.toNat k : Nat) : F) = zv * fwdL (h k) L ib) :
    LI (ftA xa u) (L + 1) (fun k => fwdL (h k) (L + 1) ia) ∧
      LI (ftB xa u) (L + 1) (fun k => fwdL (h k) (L + 1) ib) := by
  subst hib hzv
  obtain ⟨h1, h2⟩ := ct4_core hL ha hu
  obtain ⟨hhi, hdiv⟩ := divmod_hi hlo
  constructor
  · refine h1.congr (fun k _ => ?_)
    rw [fwdL_succ, ← hlen]
    unfold fwdLayer
    rw [if_pos hlo, ← hm]
  · refine h2.congr (fun k _ => ?_)
    rw [fwdL_succ, ← hlen]
    unfold fwdLayer
    rw [if_neg (by rw [hhi]; omega), hdiv, ← hm, Nat.add_sub_cancel]

/-- Forward butterfly with a table zeta (passes B, C). -/
theorem ct4m_step (h : Nat → Nat → F) (L len ia ib m z : Nat) {xa xb : UInt256}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hz : z = zm m)
    (ha : LI xa L (fun k => fwdL (h k) L ia)) (hb : LI xb L (fun k => fwdL (h k) L ib)) :
    LI (ftA xa (montU (UInt256.ofNat z * xb))) (L + 1) (fun k => fwdL (h k) (L + 1) ia) ∧
      LI (ftB xa (montU (UInt256.ofNat z * xb))) (L + 1) (fun k => fwdL (h k) (L + 1) ib) := by
  subst hz
  exact ct4_model hL hlen hlo hib hm rfl ha
    (montu_lanes (by omega) hb (Nat.lt_trans (zm_lt m) (by norm_num)) (zm_cast m))

/-- Forward butterfly with an immediate zeta by Shoup's method (pass A). -/
theorem ct4s_step (h : Nat → Nat → F) (L len ia ib m : Nat) {zs zt : Nat} {xa xb : UInt256}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hS : ShoupOK zs zt m)
    (ha : LI xa L (fun k => fwdL (h k) L ia)) (hb : LI xb L (fun k => fwdL (h k) L ib)) :
    LI (ftA xa (shU zs zt xb)) (L + 1) (fun k => fwdL (h k) (L + 1) ia) ∧
      LI (ftB xa (shU zs zt xb)) (L + 1) (fun k => fwdL (h k) (L + 1) ib) :=
  ct4_model hL hlen hlo hib hm rfl ha (shu_lanes (by omega) hb hS)

/-! ## Shoup constants of pass A (`Kernel.shoup`, `ZETAS[m]`) -/

theorem shoup1 : ShoupOK 2464201481 4808194 1 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩
theorem shoup2 : ShoupOK 1929875197 3765607 2 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩
theorem shoup3 : ShoupOK 1927777020 3761513 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩
theorem shoup4 : ShoupOK 2654200252 5178923 4 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩
theorem shoup5 : ShoupOK 2817056487 5496691 5 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩
theorem shoup6 : ShoupOK 2682805975 5234739 6 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩
theorem shoup7 : ShoupOK 2654233052 5178987 7 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by unfold ζ; decide +kernel⟩

/-! ## Inverse butterflies (swap-free `b'`) -/

theorem gs4_step (h : Nat → Nat → F) (L len m0 ia ib m z : Nat) {xa xb : UInt256}
    (hL : L < 7) (hlen : len = 2 ^ L) (hm0 : m0 = 2 ^ (8 - L)) (hlo : ia % (2 * len) < len)
    (hib : ib = ia + len) (hm : m = m0 - ia / (2 * len) - 1) (hz : z = zm m)
    (ha : LOK xa (Bi L) (fun k => invL (h k) L ia)) (hb : LOK xb (Bi L) (fun k => invL (h k) L ib)) :
    LOK (gsA xa xb) (Bi (L + 1)) (fun k => invL (h k) (L + 1) ia) ∧
      LOK (gsB4 (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
        xa xb (UInt256.ofNat z)) (Bi (L + 1)) (fun k => invL (h k) (L + 1) ib) := by
  rw [gsB4_eq]; exact gs_step h L len m0 ia ib m z hL hlen hm0 hlo hib hm hz ha hb

theorem gsS4_step (h : Nat → Nat → F) (ia ib : Nat) {xa xb : UInt256}
    (hlo : ia < 128) (hib : ib = ia + 128)
    (ha : LOK xa (Bi 7) (fun k => invL (h k) 7 ia)) (hb : LOK xb (Bi 7) (fun k => invL (h k) 7 ib)) :
    LOK (gsAs (UInt256.ofNat 41978) xa xb) Bu (fun k => Sc * invL (h k) 8 ia) ∧
      LOK (gsB4 (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
        xa xb (UInt256.ofNat 4404704)) Bu (fun k => Sc * invL (h k) 8 ib) := by
  rw [gsB4_eq]; exact gsS_step h ia ib hlo hib ha hb

/-! ## Pass invariants -/

section
variable {M M' : ByteArray} {P : Nat} {D D' S : Nat → Prop} [DecidablePred D] [DecidablePred D']
  {Pre Post : Nat → Nat → Prop}

theorem passInvG_pre (hI : PI M P D Pre Post) {t : Nat} (ht : t < 256) (hD : ¬ D t) :
    Pre t (word M (P + 32 * t)) := by
  have := hI t ht
  simp only [if_neg hD] at this
  exact this

theorem passInvG_store (hI : PI M P D Pre Post) (hD' : ∀ t, D' t ↔ D t ∨ S t)
    (hnew : ∀ t, t < 256 → S t → Post t (word M' (P + 32 * t)))
    (hold : ∀ t, t < 256 → ¬ S t → word M' (P + 32 * t) = word M (P + 32 * t)) :
    PI M' P D' Pre Post := by
  intro t ht
  by_cases hS : S t
  · simp only [if_pos ((hD' t).2 (Or.inr hS))]
    exact hnew t ht hS
  · rw [hold t ht hS]
    have := hI t ht
    by_cases hd : D t
    · simp only [if_pos hd, if_pos ((hD' t).2 (Or.inl hd))] at this ⊢
      exact this
    · have hd' : ¬ D' t := fun h' => ((hD' t).1 h').elim hd hS
      simp only [if_neg hd, if_neg hd'] at this ⊢
      exact this

theorem passInvG_init (h : ∀ t, t < 256 → Pre t (word M (P + 32 * t))) (hnone : ∀ t, ¬ D t) :
    PI M P D Pre Post := by
  intro t ht
  simp only [if_neg (hnone t)]
  exact h t ht

theorem passInvG_done (hI : PI M P D Pre Post) (hall : ∀ t, t < 256 → D t) :
    ∀ t, t < 256 → Post t (word M (P + 32 * t)) := by
  intro t ht
  have := hI t ht
  simp only [if_pos (hall t ht)] at this
  exact this

end

/-! ## The fused UseHint store -/

theorem uh_store {m0 M : ByteArray} {g : Nat → F} {x : UInt256} {t : Nat}
    (hSH : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (SP + 32 * t)) r ≤ spOff ∧
      lane (word m0 (HP + 32 * t)) r ≤ 1)
    (hF : FrameExcept m0 M [(43264, 43264 + 8192)]) (ht : t < 256) (hx : LOK x Bu g) :
    UHP m0 t (uh4W x (word M (SP + 32 * t)) (word M (HP + 32 * t))).toNat g := by
  have eS : word M (SP + 32 * t) = word m0 (SP + 32 * t) :=
    FrameExcept.word hF (by simp only [avoids_cons, avoids_nil, and_true]; unfold SP; omega)
  have eH : word M (HP + 32 * t) = word m0 (HP + 32 * t) :=
    FrameExcept.word hF (by simp only [avoids_cons, avoids_nil, and_true]; unfold HP; omega)
  rw [eS, eH]
  intro r hr
  refine ⟨lane x.toNat r, (hx r hr).1, (hx r hr).2, ?_⟩
  exact uh4W_lanes (word_lt _ _) (word_lt _ _)
    (fun r hr => uh_x_lt (by have := (hx r hr).1; unfold Bu at this; omega) (hSH t ht r hr).1)
    (fun r hr => (hSH t ht r hr).2) r hr

end MlDsaOpt44.Proofs.Ntt4

/-- Read an `SP`/`HP` word through the stores of the pass (all in `ACC`). -/
macro "uh_rd" : tactic => `(tactic|
  simp (disch := (simp only [MlDsaOpt44.Proofs.SP, MlDsaOpt44.Proofs.HP]; omega)) only
    [MlDsaOpt44.Proofs.NttW.word_wrU, if_neg])
