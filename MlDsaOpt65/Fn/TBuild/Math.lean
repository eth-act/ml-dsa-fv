import MlDsaOpt44.Fn.Ct.TBuildMath
import MlDsa.Bridge44
import MlDsaOpt65.Fn.TBuild.Defs
set_option warningAsError true
/-!
# `tbuild`: the table invariant for a table pointer `T` and calldata offset `off`

Generalisation of the invariant part of `MlDsaOpt44/Fn/Ct/TBuildMath.lean` (pinned there to
`TT = 20480` and rows 0–3 at offset 32). The bit-level facts about the stored words
(`tbW_cell`, `tbN_cell`, `be16_of_word`, `word_st3_*`, `be16_st3`) are the 44 lemmas.
-/

namespace MlDsaOpt65.Proofs.TB

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.TB

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ

/-- Field `k` of word-loop visit `j` of window `r` is coefficient `4 (v0 + j) + k` of row `r`. -/
theorem le_t1f {cd : ByteArray} {off : Nat} (hcd : off + 1280 ≤ cd.size) {a v0 j k r : Nat}
    (ha : a = off + 5 * v0 + 320 * r) (hv : v0 + j < 64) (hj : j ≤ 5) (hk : k < 4) (hr : r < 4) :
    leNat cd a 32 / 2 ^ (10 * k + 40 * j) % 2 ^ 10 = t1f cd off r (4 * (v0 + j) + k) := by
  unfold t1f
  rw [MlDsa.Bridge44.bitsToInteger_eq]
  apply div_mod_eq_bitsToInteger
  intro t ht
  have hf : off + 320 * r + 320 ≤ cd.size := by omega
  rw [testBit_eq_div_mod, leNat_bit, if_pos (by omega), MlDsa44.Fips204.bit,
    show off + 320 * (r + 1) = off + 320 * r + 320 by omega,
    byteAt_extract hf (by omega), testBit_eq_div_mod,
    show a + (10 * k + 40 * j + t) / 8 = off + 320 * r + (10 * (4 * (v0 + j) + k) + t) / 8 by omega,
    show (10 * k + 40 * j + t) % 8 = (10 * (4 * (v0 + j) + k) + t) % 8 by omega]

theorem t1f_lt (cd : ByteArray) (off r i : Nat) : t1f cd off r i < 2 ^ 10 := by
  unfold t1f
  rw [MlDsa.Bridge44.bitsToInteger_eq]
  exact MlDsa44.Proofs.Decode.bitsToInteger_lt _ _ 10

theorem frame_st3 (M : ByteArray) {T pa X : Nat} (hpa : T + 2048 ≤ pa) (hpa2 : pa ≤ T + 4064) :
    FrameExcept M (TB.st3 M pa X) [(T, T + 6144)] := by
  unfold TB.st3
  refine FrameExcept.mono ((FrameExcept.mstore M pa X).trans
    ((FrameExcept.mstore _ (2048 + pa) (tbN X)).trans (FrameExcept.mstore _ (pa - 2048) (tbN X)))) ?_
  intro r hr
  refine ⟨(T, T + 6144), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> constructor <;> simp only <;> omega

/-- The table entries of coefficient word `v` (`P` copy, upper and lower `N` copies). -/
def Good (cd M : ByteArray) (T off v : Nat) : Prop :=
  ∀ k, k < 4 → ∀ r, r < 4 →
    be16 M (T + 4094 - 32 * v - 8 * k - 2 * r) = t1f cd off r (4 * v + k) ∧
    be16 M (T + 6142 - 32 * v - 8 * k - 2 * r) = 1023 - t1f cd off r (4 * v + k) ∧
    be16 M (T + 2046 - 32 * v - 8 * k - 2 * r) = 1023 - t1f cd off r (4 * v + k)

/-- Words `v < n` done, nothing outside the table touched. -/
def Inv (cd m M : ByteArray) (T off n : Nat) : Prop :=
  FrameExcept m M [(T, T + 6144)] ∧ ∀ v, v < n → Good cd M T off v

theorem inv_zero (cd m : ByteArray) (T off : Nat) : Inv cd m m T off 0 :=
  ⟨FrameExcept.refl m _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- One word-loop visit: word `v0 + j` of the chunk with windows at `o = off + 5 v0`. -/
theorem inv_visit {cd m M : ByteArray} {T off : Nat} (hcd : off + 1280 ≤ cd.size) {n v0 j o : Nat}
    (hI : Inv cd m M T off n) (ho : o = off + 5 * v0) (hn : v0 + j ≤ n) (hn64 : n ≤ 64)
    (hv : v0 + j < 64) (hj : j ≤ 5) :
    Inv cd m (TB.st3 M (T + 4064 - 32 * (v0 + j)) (tbW (40 * j) (leNat cd o 32) (leNat cd (320 + o) 32)
      (leNat cd (640 + o) 32) (leNat cd (960 + o) 32))) T off (max n (v0 + j + 1)) := by
  generalize hX : tbW (40 * j) (leNat cd o 32) (leNat cd (320 + o) 32)
      (leNat cd (640 + o) 32) (leNat cd (960 + o) 32) = X
  have hXlt : X < 2 ^ 256 := hX ▸ tbW_lt _ _ _ _ _
  have hcell : ∀ k, k < 4 → ∀ r, r < 4 →
      X / 2 ^ (16 * (4 * k + r)) % 2 ^ 16 = t1f cd off r (4 * (v0 + j) + k) := by
    intro k hk r hr
    rw [← hX, tbW_cell _ _ _ _ _ (by omega), show (4 * k + r) % 4 = r by omega,
      show (4 * k + r) / 4 = k by omega]
    interval_cases r
    · simp only [sel, ↓reduceIte]
      exact le_t1f hcd (by omega) hv hj hk (by norm_num)
    · simp only [sel, ↓reduceIte, Nat.one_ne_zero]
      exact le_t1f hcd (by omega) hv hj hk (by norm_num)
    · simp only [sel, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
      exact le_t1f hcd (by omega) hv hj hk (by norm_num)
    · simp only [sel, Nat.reduceEqDiff, ↓reduceIte]
      exact le_t1f hcd (by omega) hv hj hk (by norm_num)
  set pa := T + 4064 - 32 * (v0 + j) with hpa
  have wP := word_st3_P M (pa := pa) (X := X) (by omega) hXlt
  have wN1 := word_st3_N1 M (pa := pa) (X := X) (by omega)
  have wN2 := word_st3_N2 M pa X
  refine ⟨hI.1.trans (frame_st3 M (T := T) (by omega) (by omega)) |>.mono ?_, fun w hw => ?_⟩
  · intro r hr; exact ⟨(T, T + 6144), by simp, by simp at hr; subst hr; simp⟩
  intro k hk r hr
  by_cases hwv : w = v0 + j
  · subst hwv
    have hc := hcell k hk r hr
    have hc' : X / 2 ^ (16 * (4 * k + r)) % 2 ^ 16 < 1024 := by rw [hc]; exact t1f_lt _ _ _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [show T + 4094 - 32 * (v0 + j) - 8 * k - 2 * r = pa + 30 - 2 * (4 * k + r) by omega,
        be16_of_word wP (by omega), hc]
    · rw [show T + 6142 - 32 * (v0 + j) - 8 * k - 2 * r = 2048 + pa + 30 - 2 * (4 * k + r) by omega,
        be16_of_word wN1 (by omega), tbN_cell X (by omega) hc', hc]
    · rw [show T + 2046 - 32 * (v0 + j) - 8 * k - 2 * r = pa - 2048 + 30 - 2 * (4 * k + r) by omega,
        be16_of_word wN2 (by omega), tbN_cell X (by omega) hc', hc]
  · have hw' : w < n := by omega
    obtain ⟨g1, g2, g3⟩ := hI.2 w hw' k hk r hr
    refine ⟨?_, ?_, ?_⟩
    · rw [be16_st3 (by omega) (by omega) (by omega), g1]
    · rw [be16_st3 (by omega) (by omega) (by omega), g2]
    · rw [be16_st3 (by omega) (by omega) (by omega), g3]

/-- The final table. -/
theorem inv_table {cd m M : ByteArray} {T off : Nat} (hI : Inv cd m M T off 64) :
    TTable M T off cd := by
  intro e he r hr
  unfold tEntry
  split_ifs with h
  · obtain ⟨g, -, -⟩ := hI.2 ((e - 256) / 4) (by omega) ((e - 256) % 4) (by omega) r hr
    rw [show T + 6142 - 8 * e - 2 * r = T + 4094 - 32 * ((e - 256) / 4) - 8 * ((e - 256) % 4) - 2 * r by
      omega, g, show 4 * ((e - 256) / 4) + (e - 256) % 4 = e - 256 by omega]
  · by_cases hlo : e < 256
    · obtain ⟨-, g, -⟩ := hI.2 (e / 4) (by omega) (e % 4) (by omega) r hr
      rw [show T + 6142 - 8 * e - 2 * r = T + 6142 - 32 * (e / 4) - 8 * (e % 4) - 2 * r by omega,
        g, show 4 * (e / 4) + e % 4 = e % 256 by omega]
    · obtain ⟨-, -, g⟩ := hI.2 ((e - 512) / 4) (by omega) ((e - 512) % 4) (by omega) r hr
      rw [show T + 6142 - 8 * e - 2 * r = T + 2046 - 32 * ((e - 512) / 4) - 8 * ((e - 512) % 4) - 2 * r by
        omega, g, show 4 * ((e - 512) / 4) + (e - 512) % 4 = e % 256 by omega]

end MlDsaOpt65.Proofs.TB
