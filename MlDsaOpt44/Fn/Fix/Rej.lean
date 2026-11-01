import MlDsaOpt44.Layout
import MlDsa44.Proofs.Math.Sampling.Rej
import MlDsa44.Proofs.Math.Shake.Bytes
set_option warningAsError true
/-!
# `fix`: the accepted-candidate list and `rejNTTPolyOf`

`accL c n` is the list of the candidates `c t < q` among `t < n`, in order.
The bytecode's compaction keeps exactly this list in lane `s` of `ABUF`;
`rejNTTPolyOf_accL` reads the spec result off it.
-/

namespace MlDsaOpt44.Proofs.Fix

open MlDsaOptCommon
open MlDsa44
open MlDsa44.Proofs.Sampling

/-- Accepted candidates among the first `n`. -/
def accL (c : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => if c n < Fips204.q then accL c n ++ [c n] else accL c n

theorem accL_succ_acc {c : Nat → Nat} {n : Nat} (h : c n < Fips204.q) :
    accL c (n + 1) = accL c n ++ [c n] := by simp [accL, h]

theorem accL_succ_rej {c : Nat → Nat} {n : Nat} (h : ¬ c n < Fips204.q) :
    accL c (n + 1) = accL c n := by simp [accL, h]

theorem accL_length_le (c : Nat → Nat) : ∀ n, (accL c n).length ≤ n
  | 0 => by simp [accL]
  | n + 1 => by
    have := accL_length_le c n
    by_cases h : c n < Fips204.q
    · rw [accL_succ_acc h, List.length_append]; simp; omega
    · rw [accL_succ_rej h]; omega

theorem accL_extend (c : Nat → Nat) (n : Nat) : ∀ d, ∃ r, accL c (n + d) = accL c n ++ r
  | 0 => ⟨[], by simp⟩
  | d + 1 => by
    obtain ⟨r, hr⟩ := accL_extend c n d
    by_cases h : c (n + d) < Fips204.q
    · exact ⟨r ++ [c (n + d)], by rw [← Nat.add_assoc, accL_succ_acc h, hr, List.append_assoc]⟩
    · exact ⟨r, by rw [← Nat.add_assoc, accL_succ_rej h, hr]⟩

theorem accL_mono_length (c : Nat → Nat) {n n' : Nat} (h : n ≤ n') :
    (accL c n).length ≤ (accL c n').length := by
  obtain ⟨r, hr⟩ := accL_extend c n (n' - n)
  rw [show n' = n + (n' - n) by omega, hr, List.length_append]; omega

theorem accL_prefix (c : Nat → Nat) {n n' i : Nat} (h : n ≤ n') (hi : i < (accL c n).length) :
    (accL c n')[i]! = (accL c n)[i]! := by
  obtain ⟨r, hr⟩ := accL_extend c n (n' - n)
  rw [show n' = n + (n' - n) by omega, hr]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]

theorem accL_last (c : Nat → Nat) {n : Nat} (h : c n < Fips204.q) :
    (accL c (n + 1))[(accL c n).length]! = c n := by
  rw [accL_succ_acc h]; simp

theorem accL_all (c : Nat → Nat) : ∀ n, (∀ t, t < n → c t < Fips204.q) →
    (accL c n).length = n ∧ ∀ i, i < n → (accL c n)[i]! = c i
  | 0, _ => by simp [accL]
  | n + 1, h => by
    obtain ⟨h1, h2⟩ := accL_all c n (fun t ht => h t (by omega))
    rw [accL_succ_acc (h n (by omega))]
    refine ⟨by simp [h1], fun i hi => ?_⟩
    by_cases hin : i < n
    · rw [← h2 i hin]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (h1 ▸ hin)]
    · rw [show i = n by omega]; simp [h1]

theorem accL_congr {c c' : Nat → Nat} : ∀ n, (∀ t, t < n → c t = c' t) → accL c n = accL c' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [accL, h n (by omega), accL_congr n (fun t ht => h t (by omega))]

/-! ## Link with the spec fold -/

theorem rejFold_accL (s : ByteArray) (c : Nat → Nat) : ∀ n, (∀ t, t < n → rejZv s t = c t) →
    (rejFold s n).2 = min (accL c n).length 256 ∧
      ∀ i, i < (rejFold s n).2 → (rejFold s n).1[i]! = (((accL c n)[i]! : Nat) : Int)
  | 0, _ => by simp [rejFold_zero, accL]
  | n + 1, h => by
    obtain ⟨h1, h2⟩ := rejFold_accL s c n (fun t ht => h t (by omega))
    have hsz := (rejFold_inv s n).1
    rw [rejFold_succ]
    unfold rejStep
    rw [h n (by omega)]
    by_cases hq : c n < Fips204.q
    · rw [accL_succ_acc hq]
      by_cases h256 : (rejFold s n).2 < 256
      · have hL : (rejFold s n).2 = (accL c n).length := by omega
        rw [if_pos ⟨h256, hq⟩]
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun i hi => ?_⟩
        simp only at hi ⊢
        rw [getElem!_set!]
        by_cases hin : i = (rejFold s n).2
        · rw [if_pos ⟨hin, by omega⟩, hin, hL]
          simp
        · rw [if_neg (fun hh => hin hh.1), h2 i (by omega)]
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (show i < (accL c n).length by omega)]
      · rw [if_neg (fun hh => h256 hh.1)]
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun i hi => ?_⟩
        rw [h2 i hi]
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (show i < (accL c n).length by omega)]
    · rw [accL_succ_rej hq, if_neg (fun hh => hq hh.2)]
      exact ⟨h1, h2⟩

/-- `rejNTTPolyOf` over 336 candidates, read off the accepted list. -/
theorem rejNTTPolyOf_accL (s : ByteArray) (c : Nat → Nat) (hc : ∀ t, t < 336 → rejZv s t = c t) :
    ((Fips204.rejNTTPolyOf s).isSome = decide (256 ≤ (accL c 336).length)) ∧
      ∀ a, Fips204.rejNTTPolyOf s = some a → ∀ t, t < 256 → (a[t]!).toNat = (accL c 336)[t]! := by
  obtain ⟨h1, h2⟩ := rejFold_accL s c 336 hc
  rw [rejNTTPolyOf_eq]
  by_cases h : (rejFold s 336).2 < 256
  · rw [if_pos h]
    refine ⟨by simp; omega, fun a ha => by simp at ha⟩
  · rw [if_neg h]
    refine ⟨by simp; omega, fun a ha t ht => ?_⟩
    simp only [Option.some.injEq] at ha
    rw [← ha, h2 t (by omega)]
    simp

/-! ## Bytes of the squeezed stream -/

/-- Byte `j` of the squeezed block of a state (`sbyte` of `Fn/Blk.lean`). -/
def sb (S : Fips202.SpongeState) (j : Nat) : Nat := laneOf S (j / 8) / 2 ^ (8 * (j % 8)) % 256

open EvmSemantics.Crypto in
theorem byteAt_squeeze (st : Fips202.SpongeState) : ∀ b j, j < 168 * b →
    MlDsa44.Proofs.byteAt (Fips202.squeeze 168 st b) j = sb (Keccak.permute^[j / 168] st) (j % 168)
  | 0, j, h => by omega
  | b + 1, j, h => by
    rw [MlDsa44.Proofs.Shake.squeeze_succ, MlDsa44.Proofs.Shake.byteAt_append,
      MlDsa44.Proofs.Math.squeeze_size_of_rate 168 st b (Or.inr rfl)]
    by_cases hj : j < b * 168
    · rw [if_pos hj]; exact byteAt_squeeze st b j (by omega)
    · rw [if_neg hj, MlDsa44.Proofs.Shake.byteAt_stateBytes, if_pos (by omega),
        show j / 168 = b by omega, show j % 168 = j - b * 168 by omega]
      unfold sb laneOf MlDsa44.Proofs.Shake.lb
      rw [show (256 : Nat) ^ ((j - b * 168) % 8) = 2 ^ (8 * ((j - b * 168) % 8)) by
        rw [pow_mul]; norm_num]

open EvmSemantics.Crypto in
/-- The bytecode's candidate `t` is the spec's triple `t` of the 1008-byte stream. -/
theorem rejZv_squeeze (I : Fips202.SpongeState) {t : Nat} (ht : t < 336) :
    rejZv (Fips202.squeeze 168 (Keccak.permute I) 6) t =
      sb (permN (t / 56 + 1) I) (3 * (t % 56)) + 256 * sb (permN (t / 56 + 1) I) (3 * (t % 56) + 1) +
        65536 * (sb (permN (t / 56 + 1) I) (3 * (t % 56) + 2) % 128) := by
  have hb : ∀ j, j < 3 → (Fips202.squeeze 168 (Keccak.permute I) 6)[3 * t + j]!.toNat =
      sb (permN (t / 56 + 1) I) (3 * (t % 56) + j) := by
    intro j hj
    rw [← MlDsa44.Proofs.Shake.byteAt_eq_getElem!, byteAt_squeeze _ 6 _ (by omega),
      show (3 * t + j) / 168 = t / 56 by omega, show (3 * t + j) % 168 = 3 * (t % 56) + j by omega]
    unfold permN
    rw [Function.iterate_succ_apply]
  unfold rejZv
  rw [or3_eq _ _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _)]
  have h0 := hb 0 (by omega); have h1 := hb 1 (by omega); have h2 := hb 2 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2]; omega

end MlDsaOpt44.Proofs.Fix
