import MlDsa44.Proofs.Fn.Hint.EncodeRowBlocks
import MlDsa44.Proofs.Fn.Hint.UseHintBlocks
import MlDsa44.Proofs.Math.Hint.Pack
/-!
# `useHint` and `encodeRow`

Yul:
* `useHint(hb, r) -> r1`: Algorithm 40 (with Algorithm 36) on `r ∈ [0, q)`
  using unsigned arithmetic: `r0' = r mod 2γ₂`, negative iff `r0' > γ₂`;
* `encodeRow(i)`: for `g < 64`, four `useHint(HB[256 i + t], ACC[t])` values
  of 6 bits packed into three bytes at `W1 + 64 + 192 i + 3 g`
  (`w1Encode` row `i`, Algorithm 28).
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budgets: exact worst cases.
namespace Gas

/-- Worst path: `hi ≠ q − 1` (114) then the `hb = 1, r0 > 0` adjustment (108). -/
def useHint : Nat := 222

/-- Entry 41, exit 43; per group: loop test 30, four inner iterations of
`92 + useHint + 58`, the three `MSTORE8`s and loop step 138. -/
def encodeRow : Nat := 64 * (4 * (useHint + 150) + 168) + 84

end Gas

theorem useHint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.useHint ret tail) (m : ByteArray) {hb r : Nat} (hhb : hb ≤ 1)
    (hrq : r < Fips204.q) :
    Call s Entry.useHint [wd hb, wd r] ret tail m
      [wd (Fips204.useHint hb r).toNat] m Gas.useHint := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.useHint, Stack.leaf] at this; omega
  have hq : r < 8380417 := hrq
  -- compose a first half ending at the join point (pc 4203) with the second half
  have fin : ∀ p hi n r1 c, p ≤ 1 → r1 < 44 → Hint.yulUseHint hb r = Hint.adjust hb p r1 →
      c + (if p = 1 then 108 else 98) ≤ 222 →
      Infra.Reach (Hint.uhEntry s hb r ret tail m)
        (Hint.uhJoin s p hi n (r % 190464) hb r r1 ret tail m) c →
      Call s Entry.useHint [wd hb, wd r] ret tail m
        [wd (Fips204.useHint hb r).toNat] m Gas.useHint := by
    intro p hi n r1 c hp hr1 hv hc h1
    rw [Infra.call_iff, Entry.useHint, Gas.useHint]
    exact ((h1.trans (Hint.uh_second hs hr htl m hi n _ r hhb hp hr1)).mono
      hc).of_eq
      (by simp) (by simp [Hint.useHint_eq hb r hhb hq, hv])
  by_cases hneg : r % 190464 > 95232
  · by_cases hhi : r - r % 190464 + 190464 = 8380416
    · exact fin 0 _ 1 0 119 (by omega) (by omega) (by simp [Hint.yulUseHint, hneg, hhi])
        (by decide) (Hint.uh_first_neg_top hs htl m hb hq hneg hhi)
    · exact fin 0 _ 1 _ 114 (by omega) (by omega) (by simp [Hint.yulUseHint, hneg, hhi])
        (by decide) (Hint.uh_first_neg hs htl m hb hq hneg hhi)
  · by_cases hhi : r - r % 190464 + 0 = 8380416
    · have hz : r % 190464 = 0 := by omega
      exact fin 0 _ 0 0 119 (by omega) (by omega) (by simp [Hint.yulUseHint, hneg, hhi])
        (by decide) (Hint.uh_first_zero_top hs htl m hb hq hz hhi)
    · exact fin _ _ 0 _ 114 (by split <;> omega) (by omega)
        (by simp only [Hint.yulUseHint, if_neg hneg, Nat.add_zero] at hhi ⊢
            simp only [hhi, hneg, if_false, not_false_eq_true, true_and])
        (by split <;> simp) (Hint.uh_first_pos hs htl m hb hq hneg rfl hhi)

/-- Row `i` of `w1 = UseHint(h, w)`, with the hint bits read from `HB`. -/
def w1Row (m : ByteArray) (i : Nat) (f : Fips204.Poly) : Fips204.Poly :=
  (Array.range 256).map fun j => Fips204.useHint (byteAt m (HB + 256 * i + j)) f[j]!

/-- Coefficient `t` of row `i` as the call `useHint(HB[256 i + t], ACC[t])` computes it. -/
def uRow (m : ByteArray) (i t : Nat) : Nat :=
  (Fips204.useHint (byteAt m (HB + 256 * i + t) : Int) (word m (ACC + 32 * t) : Int)).toNat

/-- Memory after `g` groups of row `i` (`v_g = groupAcc (uRow m i) g 4`). -/
def erMem (m : ByteArray) (i g : Nat) : ByteArray :=
  Hint.storeGroups m (78656 + (64 + 192 * i)) (fun g => Hint.groupAcc (uRow m i) g 4) g

theorem uRow_lt {m : ByteArray} {i t : Nat} (hb : byteAt m (HB + 256 * i + t) ≤ 1)
    (hw : word m (ACC + 32 * t) < Fips204.q) : uRow m i t < 44 := by
  unfold uRow
  rw [Hint.useHint_eq _ _ hb hw]
  exact Hint.yulUseHint_lt _ _ hw

/-- One inner iteration of `encodeRow`: coefficient `t = 4 g + e` through `useHint`. -/
theorem encodeRow_iter {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.encodeRow ret tail) {m : ByteArray} {i : Nat} (hi : i < 4)
    (hbits : ∀ j, j < 256 → byteAt m (HB + 256 * i + j) ≤ 1)
    (hwq : ∀ t, t < 256 → word m (ACC + 32 * t) < Fips204.q) {g e : Nat} (hg : g < 64)
    (he : e < 4) :
    Infra.Reach (Hint.erInner s e (Hint.groupAcc (uRow m i) g e) g i ret tail (erMem m i g))
      (Hint.erInner s (e + 1) (Hint.groupAcc (uRow m i) g (e + 1)) g i ret tail (erMem m i g))
      (92 + Gas.useHint + 58) := by
  have ht : g * 4 + e < 256 := by omega
  have hby : byteAt (erMem m i g) (76256 + i * 256 + (g * 4 + e)) =
      byteAt m (HB + 256 * i + (g * 4 + e)) := by
    rw [erMem, Hint.byteAt_storeGroups_out m _ _ g _ (by left; omega),
      show 76256 + i * 256 + (g * 4 + e) = HB + 256 * i + (g * 4 + e) by simp only [HB]; omega]
  have hw : word (erMem m i g) (59872 + (g * 4 + e) * 32) = word m (ACC + 32 * (g * 4 + e)) := by
    rw [show 59872 + (g * 4 + e) * 32 = ACC + 32 * (g * 4 + e) by simp only [ACC]; omega]
    refine Infra.FrameExcept.word (Hint.FrameExcept.storeGroups m _ _ g) ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    left
    simp only [ACC]
    omega
  have hcall := Infra.call_iff.mp (useHint_call hs
    (hr.callee (B' := Stack.useHint) (ret' := 4334)
      (extra := [wd (g * 4 + e), wd e, wd (Hint.groupAcc (uRow m i) g e), wd g,
        wd (76256 + i * 256), wd (78656 + (64 + 192 * i)), wd i, wd ret])
      (by simp [Stack.encodeRow]) (by simp) (by simp only [Infra.isValidJumpDest_lit])
      (by decide))
    (erMem m i g) (hbits _ ht) (hwq _ ht))
  have h := ((Hint.er_call (v := Hint.groupAcc (uRow m i) g e) hs hr hi hg he hby hw).trans
    (hcall.of_eq (by simp [Entry.useHint]) rfl)).trans (Hint.er_after hs hr (erMem m i g) he)
  exact h.of_eq rfl (by rw [Hint.groupAcc_succ]; rfl)

/-- One outer iteration of `encodeRow`: group `g` packed into three bytes. -/
theorem encodeRow_group {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.encodeRow ret tail) {m : ByteArray} {i : Nat} (hi : i < 4)
    (hbits : ∀ j, j < 256 → byteAt m (HB + 256 * i + j) ≤ 1)
    (hwq : ∀ t, t < 256 → word m (ACC + 32 * t) < Fips204.q) {g : Nat} (hg : g < 64) :
    Infra.Reach (Hint.erOuter s g i ret tail (erMem m i g))
      (Hint.erOuter s (g + 1) i ret tail (erMem m i (g + 1)))
      (30 + 4 * (92 + Gas.useHint + 58) + 138) := by
  have hloop := Infra.Reach.loop
    (I := fun e => Hint.erInner s e (Hint.groupAcc (uRow m i) g e) g i ret tail (erMem m i g)) 4
    (fun e he => encodeRow_iter hs hr hi hbits hwq hg he)
  have hu : ∀ e, e < 4 → uRow m i (g * 4 + e) < 44 := fun e he =>
    uRow_lt (hbits _ (by omega)) (hwq _ (by omega))
  have hv : Hint.groupAcc (uRow m i) g 4 < 2 ^ 24 := by
    rw [Hint.groupAcc_four _ _ (fun e he => by have := hu e he; omega)]
    have h0 := hu 0 (by decide)
    have h1 := hu 1 (by decide)
    have h2 := hu 2 (by decide)
    have h3 := hu 3 (by decide)
    simp only [Nat.add_zero] at h0
    omega
  exact (((Hint.er_head hs hr _ hg).trans hloop).trans (Hint.er_store hs hr _ hi hg hv)).of_eq
    rfl rfl

theorem encodeRow_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.encodeRow ret tail) {m : ByteArray} {i : Nat} (hi : i < 4) {f : Fips204.Poly}
    (hf : PolyAt m ACC f) (hred : Reduced f)
    (hbits : ∀ j, j < 256 → byteAt m (HB + 256 * i + j) ≤ 1) :
    ∃ m', BytesAt m' (W1 + 64 + 192 * i)
        (Fips204.simpleBitPack (w1Row m i f) ((Fips204.q - 1) / (2 * Fips204.gamma2) - 1)) ∧
      FrameExcept m m' [(W1 + 64 + 192 * i, W1 + 64 + 192 * (i + 1))] ∧
      Call s Entry.encodeRow [wd i] ret tail m [] m' Gas.encodeRow := by
  have hwq : ∀ t, t < 256 → word m (ACC + 32 * t) < Fips204.q := by
    intro t ht
    have h1 := hf.2 t ht
    have h2 := (hred t ht).2
    omega
  -- coefficient `n` of `w1Row` is the value the call computes
  have hw1 : ∀ n, n < 256 → (w1Row m i f)[n]!.toNat = uRow m i n := by
    intro n hn
    rw [w1Row, getElem!_pos _ n (by simp; omega)]
    simp only [Array.getElem_map, Array.getElem_range, uRow]
    rw [← hf.2 n hn]
  have hA : ∀ n, n < 256 → uRow m i n < 64 := fun n hn => by
    have := uRow_lt (hbits n hn) (hwq n hn); omega
  refine ⟨erMem m i 64, ?_, ?_, ?_⟩
  · rw [show (Fips204.q - 1) / (2 * Fips204.gamma2) - 1 = 43 by decide]
    intro j hj
    rw [Hint.simpleBitPack43_size] at hj
    rw [Hint.simpleBitPack43_get _ (uRow m i) hw1 hA j hj,
      show W1 + 64 + 192 * i + j = 78656 + (64 + 192 * i) + j by simp only [W1]; omega]
    exact Hint.byteAt_storeGroups m _ _ 64 j (by omega)
  · have := Hint.FrameExcept.storeGroups m (78656 + (64 + 192 * i))
      (fun g => Hint.groupAcc (uRow m i) g 4) 64
    rw [show W1 + 64 + 192 * i = 78656 + (64 + 192 * i) by simp only [W1]; omega,
      show W1 + 64 + 192 * (i + 1) = 78656 + (64 + 192 * i) + 3 * 64 by simp only [W1]; omega]
    exact this
  · rw [Infra.call_iff, Entry.encodeRow]
    have hloop := Infra.Reach.loop (I := fun g => Hint.erOuter s g i ret tail (erMem m i g)) 64
      (fun g hg => encodeRow_group hs hr hi hbits hwq hg)
    have h := ((Hint.er_entry hs hr m i).trans hloop).trans (Hint.er_exit hs hr (erMem m i 64))
    refine (h.mono ?_).of_eq (by simp) (by simp)
    unfold Gas.encodeRow
    omega

end MlDsa44.Proofs
