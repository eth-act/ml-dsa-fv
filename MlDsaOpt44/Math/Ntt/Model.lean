import MlDsaOpt44.Math.Ntt.Layer
import MlDsa44.Proofs.Math.Sampling.Rej
/-!
# `ntt` and `nttInv` as iterated closed-form layers over `ZMod q`
-/

namespace MlDsaOpt44.Proofs.NttConv

open MlDsa44 Fips204 MlDsa44.Proofs.NttModel

/-- Layer `L` of Algorithm 41 (`len = 128 / 2^L`, block `b` uses `zetas (2^L + b)`). -/
def NL (L : Nat) (u : Nat → F) : Nat → F :=
  CL (128 / 2 ^ L) (fun z x y => x + z * y) (fun z x y => x - z * y)
    (fun b => ((zetas (2 ^ L + b) : Int) : F)) u

def Nf (u : Nat → F) : Nat → Nat → F
  | 0 => u
  | L + 1 => NL L (Nf u L)

/-- Layer `K` of Algorithm 42 (`len = 2^K`, block `b` uses `−zetas (2^(8−K) − b − 1)`). -/
def IL (K : Nat) (u : Nat → F) : Nat → F :=
  CL (2 ^ K) (fun _ x y => x + y) (fun z x y => z * (x - y))
    (fun b => ((-zetas (2 ^ (8 - K) - b - 1) : Int) : F)) u

def If (u : Nat → F) : Nat → Nat → F
  | 0 => u
  | K + 1 => IL K (If u K)

theorem layer_facts : ∀ L, L < 8 → 0 < 128 / 2 ^ L ∧ 2 * (128 / 2 ^ L) * 2 ^ L = 256 ∧
    0 < 2 ^ L ∧ 2 * 2 ^ L * (128 / 2 ^ L) = 256 := by decide

theorem layerN_eq (len m0 : Nat) (w : Poly) :
    ∀ b, layerN len m0 w b = layerG (bfN len) len (fun b => zetas (m0 + b + 1)) w b
  | 0 => rfl
  | b + 1 => by
    show blockN len (zetas (m0 + b + 1)) (layerN len m0 w b) (2 * len * b) len = _
    rw [layerN_eq len m0 w b]; rfl

theorem layerI_eq (len m0 : Nat) (w : Poly) :
    ∀ b, layerI len m0 w b = layerG (bfI len) len (fun b => -zetas (m0 - b - 1)) w b
  | 0 => rfl
  | b + 1 => by
    show blockI len (-zetas (m0 - b - 1)) (layerI len m0 w b) (2 * len * b) len = _
    rw [layerI_eq len m0 w b]; rfl

theorem nttL_spec (f : Poly) (hf : f.size = 256) : ∀ L, L ≤ 8 →
    (nttL f L).size = 256 ∧ ∀ i, i < 256 → toF (nttL f L) i = Nf (toF f) L i
  | 0, _ => ⟨hf, fun _ _ => rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, he⟩ := nttL_spec f hf L (by omega)
    obtain ⟨h1, h2, -, -⟩ := layer_facts L (by omega)
    obtain ⟨hs', he'⟩ := layerG_spec (bfN_spec _ h1) h1 h2 (fun b => zetas (2 ^ L - 1 + b + 1))
      (nttL f L) hs
    show (layerN (128 / 2 ^ L) (2 ^ L - 1) (nttL f L) (2 ^ L)).size = 256 ∧
      ∀ i, i < 256 → toF (layerN (128 / 2 ^ L) (2 ^ L - 1) (nttL f L) (2 ^ L)) i = NL L (Nf (toF f) L) i
    rw [layerN_eq]
    refine ⟨hs', fun i hi => ?_⟩
    rw [he' i hi]
    have hz : (fun b => ((zetas (2 ^ L - 1 + b + 1) : Int) : F)) =
        fun b => ((zetas (2 ^ L + b) : Int) : F) := by
      funext b; rw [show 2 ^ L - 1 + b + 1 = 2 ^ L + b by have := Nat.one_le_two_pow (n := L); omega]
    rw [hz]
    exact CL_congr h1 h2 he hi

theorem ntt_spec (f : Poly) (hf : f.size = 256) :
    (ntt f).size = 256 ∧ ∀ i, i < 256 → toF (ntt f) i = Nf (toF f) 8 i := by
  rw [ntt_eq]; exact nttL_spec f hf 8 le_rfl

theorem nttIL_spec (f : Poly) (hf : f.size = 256) : ∀ L, L ≤ 8 →
    (nttIL f L).size = 256 ∧ ∀ i, i < 256 → toF (nttIL f L) i = If (toF f) L i
  | 0, _ => ⟨hf, fun _ _ => rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, he⟩ := nttIL_spec f hf L (by omega)
    obtain ⟨-, -, h1, h2⟩ := layer_facts L (by omega)
    obtain ⟨hs', he'⟩ := layerG_spec (bfI_spec _ h1) h1 h2 (fun b => -zetas (2 ^ (8 - L) - b - 1))
      (nttIL f L) hs
    show (layerI (2 ^ L) (2 ^ (8 - L)) (nttIL f L) (128 / 2 ^ L)).size = 256 ∧
      ∀ i, i < 256 → toF (layerI (2 ^ L) (2 ^ (8 - L)) (nttIL f L) (128 / 2 ^ L)) i =
        IL L (If (toF f) L) i
    rw [layerI_eq]
    refine ⟨hs', fun i hi => ?_⟩
    rw [he' i hi]
    exact CL_congr h1 h2 he hi

theorem nttIL_size (f : Poly) : ∀ L, (nttIL f L).size = f.size
  | 0 => rfl
  | L + 1 => by
    show (layerI (2 ^ L) (2 ^ (8 - L)) (nttIL f L) (128 / 2 ^ L)).size = _
    rw [layerI_eq, layerG_size (bfI_size _), nttIL_size f L]

/-! ## The final scaling loop -/

theorem scaleI_spec (w : Poly) : ∀ k, (scaleI w k).size = w.size ∧
    ∀ i, (scaleI w k)[i]! = if i < k ∧ i < w.size then 8347681 * w[i]! % q else w[i]!
  | 0 => ⟨rfl, fun i => by rw [if_neg (by omega)]; rfl⟩
  | k + 1 => by
    obtain ⟨hs, he⟩ := scaleI_spec w k
    have e : scaleI w (k + 1) = scStep (scaleI w k) k := by
      simp only [scaleI, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.zero_add, Nat.one_mul]
    rw [e]
    refine ⟨by rw [scStep, MlDsa44.Proofs.Sampling.size_set!, hs], fun i => ?_⟩
    rw [scStep, MlDsa44.Proofs.Sampling.getElem!_set!, he k, hs, he i]
    by_cases h1 : i = k
    · subst h1; by_cases h2 : i < w.size <;> simp [h2]
    · by_cases h2 : i < k
      · have h3 : i ≤ k := by omega
        simp [h1, h2, h3]
      · have : ¬ i < k + 1 := by omega
        simp [h1, h2, this]

theorem nttInv_spec (x : Poly) (hx : x.size = 256) :
    (nttInv x).size = 256 ∧ ∀ i, i < 256 → toF (nttInv x) i = 8347681 * If (toF x) 8 i := by
  rw [nttInv_eq]
  obtain ⟨hs, he⟩ := scaleI_spec (nttIL x 8) 256
  obtain ⟨hs', he'⟩ := nttIL_spec x hx 8 le_rfl
  refine ⟨by rw [hs, hs'], fun i hi => ?_⟩
  have e2 := he' i hi
  unfold toF at e2 ⊢
  rw [he i, if_pos ⟨hi, by rw [hs']; exact hi⟩, cast_emod, Int.cast_mul, e2, Int.cast_ofNat]

theorem nttInv_reduced (x : Poly) {t : Nat} (ht : t < 256) :
    (0 : Int) ≤ (nttInv x)[t]! ∧ (nttInv x)[t]! < (q : Int) := by
  rw [nttInv_eq]
  obtain ⟨-, he⟩ := scaleI_spec (nttIL x 8) 256
  rw [he t]
  split
  · exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  · rename_i h
    have h' : ¬ t < (nttIL x 8).size := fun h' => h ⟨ht, h'⟩
    simp [getElem!_neg, h', q]

theorem IL_congr {K : Nat} (hK : K < 8) {u v : Nat → F} (h : ∀ j, j < 256 → u j = v j)
    {i : Nat} (hi : i < 256) : IL K u i = IL K v i := by
  obtain ⟨-, -, h1, h2⟩ := layer_facts K hK
  exact CL_congr h1 h2 h hi

theorem If_congr {u v : Nat → F} (h : ∀ j, j < 256 → u j = v j) : ∀ K, K ≤ 8 →
    ∀ i, i < 256 → If u K i = If v K i
  | 0, _ => h
  | K + 1, hK => fun _ hi => IL_congr (by omega) (If_congr h K (by omega)) hi

theorem NL_congr {L : Nat} (hL : L < 8) {u v : Nat → F} (h : ∀ j, j < 256 → u j = v j)
    {i : Nat} (hi : i < 256) : NL L u i = NL L v i := by
  obtain ⟨h1, h2, -, -⟩ := layer_facts L hL
  exact CL_congr h1 h2 h hi

theorem Nf_congr {u v : Nat → F} (h : ∀ j, j < 256 → u j = v j) : ∀ L, L ≤ 8 →
    ∀ i, i < 256 → Nf u L i = Nf v L i
  | 0, _ => h
  | L + 1, hL => fun _ hi => NL_congr (by omega) (Nf_congr h L (by omega)) hi

end MlDsaOpt44.Proofs.NttConv
