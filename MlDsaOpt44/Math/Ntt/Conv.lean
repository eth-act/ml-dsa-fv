import MlDsaOpt44.Math.Ntt.Model
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
/-!
# The NTT convolution theorem for Algorithms 41/42

* `Nf_eval8`: `NTT(w)[b] = w(rr 8 b)` in `ZMod q`, where `rr 8 b` runs over the
  256 roots of `X^256 + 1` (layer invariant: block `b` of layer `L` agrees with
  `w` on the roots of `X^(256/2^L) − rr L b`);
* `If_Nf`: layer `K` of Algorithm 42 undoes layer `7 − K` of Algorithm 41 up
  to a factor 2, so `NTT⁻¹ ∘ NTT = id` (`256 · 8347681 ≡ 1`);
* `conv`: `NTT⁻¹(NTT c ∘ NTT f)` is the negacyclic product `c · f`.
-/

namespace MlDsaOpt44.Proofs.NttConv

open MlDsa44 Fips204 Finset

def zF (m : Nat) : F := ((zetas m : Int) : F)

/-- The root of block `b` after `L` layers. -/
def rr : Nat → Nat → F
  | 0, _ => -1
  | L + 1, b => if b % 2 = 0 then zF (2 ^ L + b / 2) else -zF (2 ^ L + b / 2)

set_option maxRecDepth 10000 in
theorem chk_sq : ∀ L, L < 8 → ∀ b, b < 2 ^ L → zF (2 ^ L + b) ^ 2 = rr L b := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem chk_inv : ∀ L, L < 8 → ∀ b, b < 2 ^ L → zF (2 ^ (L + 1) - 1 - b) * zF (2 ^ L + b) = -1 := by
  decide +kernel

theorem chk_scale : (8347681 : F) * 2 ^ 8 = 1 := by decide

theorem rr_even (L b : Nat) : rr (L + 1) (2 * b) = zF (2 ^ L + b) := by
  simp only [rr, Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left b (by omega : 0 < 2)]

theorem rr_odd (L b : Nat) : rr (L + 1) (2 * b + 1) = -zF (2 ^ L + b) := by
  simp only [rr, if_neg (by omega : ¬ (2 * b + 1) % 2 = 0),
    show (2 * b + 1) / 2 = b by omega]

def ev (u : Nat → F) (x : F) : F := ∑ j ∈ range 256, u j * x ^ j

theorem div_facts : ∀ L, L < 8 → 256 / 2 ^ (L + 1) = 128 / 2 ^ L ∧ 256 / 2 ^ L = 2 * (128 / 2 ^ L) := by
  decide

set_option maxRecDepth 10000 in
theorem Nf_eval (u : Nat → F) : ∀ L, L ≤ 8 → ∀ b, b < 2 ^ L → ∀ x : F, x ^ (256 / 2 ^ L) = rr L b →
    ∑ j ∈ range (256 / 2 ^ L), Nf u L (256 / 2 ^ L * b + j) * x ^ j = ev u x
  | 0, _, b, hb, x, _ => by
    have : b = 0 := by simp only [Nat.pow_zero] at hb; omega
    subst this
    show ∑ j ∈ range (256 / 2 ^ 0), u (256 / 2 ^ 0 * 0 + j) * x ^ j = ∑ j ∈ range 256, u j * x ^ j
    simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_zero, Nat.div_one]
  | L + 1, hL, b', hb', x, hx => by
    obtain ⟨e1, e2⟩ := div_facts L (by omega)
    obtain ⟨h1, -, -, -⟩ := layer_facts L (by omega)
    obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' b'
    all_goals
      subst hb
      have hb : b < 2 ^ L := by rw [Nat.pow_succ] at hb'; omega
      have IH := Nf_eval u L (by omega) b hb x
      have hz := chk_sq L (by omega) b hb
      rw [e1] at hx ⊢
      rw [e2] at IH
      show ∑ j ∈ range _, NL L (Nf u L) _ * _ = _
      unfold NL
      unfold zF at hz
      generalize 128 / 2 ^ L = len at *
      rw [← IH (by rw [pow_mul', hx]; first | rw [rr_even]; exact hz | rw [rr_odd, neg_sq]; exact hz),
        show 2 * len = len + len by omega, sum_range_add]
    · rw [rr_even] at hx; unfold zF at hx
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      rw [show len * (2 * b) + j = 2 * len * b + j by ring, CL_lo hj, ← hx,
        show 2 * len * b + j + len = 2 * len * b + (len + j) by omega, pow_add]
      ring_nf
    · rw [rr_odd] at hx; unfold zF at hx
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      rw [show len * (2 * b + 1) + j = 2 * len * b + (len + j) by ring, CL_hi (by omega) (by omega),
        show 2 * len * b + (len + j) - len = 2 * len * b + j by omega,
        show ((zetas (2 ^ L + b) : Int) : F) = -x ^ len by rw [hx, neg_neg], pow_add]
      ring_nf

theorem Nf_eval8 (u : Nat → F) {b : Nat} (hb : b < 256) : Nf u 8 b = ev u (rr 8 b) := by
  have := Nf_eval u 8 le_rfl b hb (rr 8 b) (by simp)
  simpa using this

theorem rr_pow : ∀ L, L ≤ 8 → ∀ b, b < 2 ^ L → rr L b ^ (2 ^ L) = -1
  | 0, _, _, _ => by simp [rr]
  | L + 1, hL, b', hb' => by
    obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' b'
    all_goals
      subst hb
      have hb : b < 2 ^ L := by rw [Nat.pow_succ] at hb'; omega
      rw [← rr_pow L (by omega) b hb, ← chk_sq L (by omega) b hb, Nat.pow_succ, pow_mul']
    · rw [rr_even]
    · rw [rr_odd, neg_sq]

/-! ## Inverse -/

theorem IL_smul (K : Nat) (a : F) (u : Nat → F) (i : Nat) :
    IL K (fun j => a * u j) i = a * IL K u i := by
  unfold IL CL; split <;> ring

theorem IL_sub (K : Nat) (u v : Nat → F) (i : Nat) :
    IL K (fun j => u j - v j) i = IL K u i - IL K v i := by
  unfold IL CL; split <;> ring

theorem If_sub (u v : Nat → F) : ∀ K i, If (fun j => u j - v j) K i = If u K i - If v K i
  | 0, _ => rfl
  | K + 1, i => by
    show IL K (If (fun j => u j - v j) K) i = IL K (If u K) i - IL K (If v K) i
    rw [show If (fun j => u j - v j) K = fun j => If u K j - If v K j from funext (If_sub u v K),
      IL_sub]

theorem pow_facts : ∀ K, K < 8 → 128 / 2 ^ (7 - K) = 2 ^ K ∧ 128 / 2 ^ K = 2 ^ (7 - K) ∧
    8 - K = 7 - K + 1 := by decide

theorem cancel {K : Nat} (hK : K < 8) (v : Nat → F) {i : Nat} (hi : i < 256) :
    IL K (NL (7 - K) v) i = 2 * v i := by
  obtain ⟨p1, p2, p3⟩ := pow_facts K hK
  obtain ⟨-, -, h1, h2⟩ := layer_facts K hK
  have hinv := chk_inv (7 - K) (by omega)
  rw [← p2] at hinv
  unfold IL NL
  rw [p1, p3]
  unfold zF at hinv
  generalize 2 ^ K = len at *
  generalize 128 / len = nb at *
  obtain ⟨b, o, rfl, ho, hb⟩ := decomp h1 h2 hi
  subst p2
  have hz := hinv b hb
  by_cases hlo : o < len
  · rw [CL_lo hlo, CL_lo hlo, show 2 * len * b + o + len = 2 * len * b + (o + len) by omega,
      CL_hi (by omega) (by omega), show 2 * len * b + (o + len) - len = 2 * len * b + o by omega]
    ring
  · rw [CL_hi (by omega) ho, CL_hi (by omega) ho,
      show 2 * len * b + o - len = 2 * len * b + (o - len) by omega, CL_lo (by omega),
      show 2 * len * b + (o - len) + len = 2 * len * b + o by omega,
      show 2 ^ (7 - K + 1) - b - 1 = 2 ^ (7 - K + 1) - 1 - b by omega]
    push_cast
    linear_combination (-2 * v (2 * len * b + o)) * hz

theorem If_Nf (u : Nat → F) : ∀ K, K ≤ 8 → ∀ i, i < 256 → If (Nf u 8) K i = 2 ^ K * Nf u (8 - K) i
  | 0, _, _, _ => by simp [If]
  | K + 1, hK, i, hi => by
    show IL K (If (Nf u 8) K) i = _
    rw [IL_congr (by omega) (If_Nf u K (by omega)) hi, IL_smul,
      show 8 - K = 7 - K + 1 by omega]
    show 2 ^ K * IL K (NL (7 - K) (Nf u (7 - K))) i = _
    rw [cancel (by omega) _ hi, show 8 - (K + 1) = 7 - K by omega, pow_succ]
    ring

theorem inv_ntt (u : Nat → F) {i : Nat} (hi : i < 256) : 8347681 * If (Nf u 8) 8 i = u i := by
  rw [If_Nf u 8 le_rfl i hi, ← mul_assoc, chk_scale, one_mul]; rfl

/-! ## Products -/

/-- Negacyclic product in `ZMod q`. -/
def negF (c t : Nat → F) (k : Nat) : F :=
  ∑ p ∈ range 256, if p ≤ k then c p * t (k - p) else -(c p * t (k + 256 - p))

theorem shift (t : Nat → F) {x : F} (hx : x ^ 256 = -1) {p : Nat} (hp : p ≤ 256) :
    ∑ k ∈ range 256, (if p ≤ k then t (k - p) else -t (k + 256 - p)) * x ^ k =
      x ^ p * ∑ j ∈ range 256, t j * x ^ j := by
  conv_lhs => rw [show range 256 = range (p + (256 - p)) by rw [Nat.add_sub_cancel' hp]]
  conv_rhs => rw [show range 256 = range ((256 - p) + p) by rw [Nat.sub_add_cancel hp]]
  rw [sum_range_add, sum_range_add, mul_add, mul_sum, mul_sum, add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply sum_congr rfl
    intro j hj
    rw [if_pos (by omega), show p + j - p = j by omega, pow_add]; ring
  · apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [if_neg (by omega), show 256 - p + k = k + 256 - p by omega]
    have : x ^ p * x ^ (k + 256 - p) = -x ^ k := by
      rw [← pow_add, show p + (k + 256 - p) = 256 + k by omega, pow_add, hx]; ring
    linear_combination (-t (k + 256 - p)) * this

theorem ev_negF (c t : Nat → F) {x : F} (hx : x ^ 256 = -1) :
    ev (negF c t) x = ev c x * ev t x := by
  unfold ev negF
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [mem_range] at hp
  have e : ∀ k, (if p ≤ k then c p * t (k - p) else -(c p * t (k + 256 - p))) * x ^ k =
      c p * ((if p ≤ k then t (k - p) else -t (k + 256 - p)) * x ^ k) := by
    intro k; split <;> ring
  simp only [e]
  rw [← mul_sum, shift t hx (by omega)]
  ring

/-- **Convolution theorem**: if `V ≡ NTT c ∘ NTT f`, then `NTT⁻¹ V ≡ c · f`. -/
theorem conv (c f V : Poly) (hc : c.size = 256) (hf : f.size = 256) (hV : V.size = 256)
    (h : ∀ j, j < 256 → toF V j = toF (ntt c) j * toF (ntt f) j) {k : Nat} (hk : k < 256) :
    toF (nttInv V) k = negF (toF c) (toF f) k := by
  obtain ⟨-, hc'⟩ := ntt_spec c hc
  obtain ⟨-, hf'⟩ := ntt_spec f hf
  obtain ⟨-, hV'⟩ := nttInv_spec V hV
  have hV2 : ∀ j, j < 256 → toF V j = Nf (negF (toF c) (toF f)) 8 j := by
    intro j hj
    have hx := rr_pow 8 le_rfl j hj
    rw [h j hj, hc' j hj, hf' j hj, Nf_eval8 _ hj, Nf_eval8 _ hj, Nf_eval8 _ hj, ev_negF _ _ hx]
  rw [hV' k hk, If_congr hV2 8 le_rfl k hk, inv_ntt _ hk]

end MlDsaOpt44.Proofs.NttConv
