import MlDsa44.Proofs.Fn.Shake
import MlDsa44.Proofs.Fn.Sampling
import MlDsa44.Proofs.Fn.Row.Blocks
import MlDsa44.Proofs.Fn.Row.Math
set_option warningAsError true
/-!
# One iteration of `computeRow`'s outer loop

`for j < 4`: seed bytes, `shake`, `rejSample(AP)`, `ACC += AP ∘ ZH[j]`.
The invariant `OuterInv` keeps the frame, the reduced range of `ACC`, and
(for every row `aRow` that matches the successful samples so far) the partial
sum `Σ_{j' < j} Â[i][j'] ∘ ẑ[j']`.
-/

namespace MlDsa44.Proofs.Row

open EvmSemantics
open EvmSemantics.EVM

/-- The regions `computeRow` may write. -/
def rowFrame : List (Nat × Nat) :=
  [(ST, RC), (AP, AP + POLY), (ACC, ACC + POLY), (TP, TP + POLY),
    (XOF, XOF + 0x420), (SEEDA + 32, SEEDA + 34), (PADB, PADB + 192)]

/-- Close an `Infra.Avoids` goal over the fixed layout. -/
macro "avoid" : tactic => `(tactic| (simp only [rowFrame, List.cons_append, List.nil_append,
  List.append_nil, Infra.avoids_cons, Infra.avoids_nil, Infra.avoids_append, and_true,
  ST, RC, ZETA, ZH, CH, AP, ACC, TP, XOF, SEEDA, PADB, POLY]; omega))

/-- `Â[i][j]` from the seed `ρ`. -/
def aE (rho : ByteArray) (i j : Nat) : Option Fips204.Poly :=
  Fips204.rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i])

/-- The partial row sum `Σ_{j' < j} aRow[j'] ∘ ẑ[j']`. -/
def azP (aRow zHat : Array Fips204.Poly) (j : Nat) : Fips204.Poly :=
  (List.range j).foldl
    (fun acc j => Fips204.addNTT acc (Fips204.multiplyNTT aRow[j]! zHat[j]!)) Fips204.zeroPoly

/-- `good` after `j` iterations. -/
def goodN (rho : ByteArray) (i j : Nat) : Nat :=
  if (List.range j).all fun j => (aE rho i j).isSome then 1 else 0

def OuterInv (m : ByteArray) (rho : ByteArray) (i : Nat) (zHat : Array Fips204.Poly)
    (j : Nat) (M : ByteArray) : Prop :=
  FrameExcept m M rowFrame ∧ (∀ t, t < 256 → word M (ACC + 32 * t) < Fips204.q) ∧
    ∀ aRow : Array Fips204.Poly, (∀ j', j' < j → aE rho i j' = some aRow[j']!) →
      ∀ t, t < 256 → (word M (ACC + 32 * t) : Int) = (azP aRow zHat j)[t]!

/-- Outer-loop cost per iteration. -/
def outerCost : Nat := 85 + Gas.shake 168 34 6 + 20 + Gas.rejSample + 29 + 256 * 131 + 56

theorem azP_succ_get (aRow zHat : Array Fips204.Poly) (j : Nat) {t : Nat} (ht : t < 256) :
    (azP aRow zHat (j + 1))[t]! =
      ((azP aRow zHat j)[t]! + aRow[j]![t]! * zHat[j]![t]! % (Fips204.q : Int)) %
        (Fips204.q : Int) := by
  rw [azP, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← azP,
    Fips204.addNTT, getElem!_range_map _ ht, Fips204.multiplyNTT, getElem!_range_map _ ht]

theorem goodN_succ (rho : ByteArray) (i j : Nat) :
    goodN rho i (j + 1) = goodN rho i j &&& (if (aE rho i j).isSome then 1 else 0) := by
  unfold goodN
  rw [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range j).all fun j => (aE rho i j).isSome <;>
    cases (aE rho i j).isSome <;> rfl

theorem stack_computeRow : Stack.computeRow = 320 := by
  simp [Stack.computeRow, Stack.shake, Stack.keccakF, Stack.xorBlock, Stack.loadLE64,
    Stack.storeLE64, Stack.bswap64, Stack.rejSample, Stack.zeroPoly, Stack.unpack, Stack.ntt,
    Stack.nttInv, Stack.leaf]

theorem activeWords_ge {s : State} (hs : Ctx s) : 2535 ≤ s.activeWords.toNat := by
  have h := hs.sized
  have h' : fixedWords = 2535 := rfl
  omega

theorem outer_step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.computeRow ret tail) {m rho : ByteArray} {i j : Nat} (hi : i < 4)
    (hj : j < 4) (hrc : RCTable m) {zHat : Array Fips204.Poly}
    (hzs : ∀ j, j < 4 → PolyAt m (ZH + POLY * j) zHat[j]!)
    (hrs : rho.size = 32) (hrho : BytesAt m SEEDA rho) (M : ByteArray)
    (hP : OuterInv m rho i zHat j M) :
    ∃ M', OuterInv m rho i zHat (j + 1) M' ∧
      Infra.Reach (callState s 4432 (wd j :: wd i :: wd (goodN rho i j) :: wd ret :: tail) M)
        (callState s 4432 (wd (j + 1) :: wd i :: wd (goodN rho i (j + 1)) :: wd ret :: tail) M')
        outerCost := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; rw [stack_computeRow] at this; omega
  have haw := activeWords_ge hs
  have haw' : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  obtain ⟨hfr, -, hacc⟩ := hP
  -- the two seed bytes
  let M1 := MachineState.writeBytes (MachineState.writeBytes M (ByteArray.mk #[UInt8.ofNat j])
    (SEEDA + 32)) (ByteArray.mk #[UInt8.ofNat i]) (SEEDA + 33)
  have hfr1 : FrameExcept M M1 [(SEEDA + 32, SEEDA + 32 + 1), (SEEDA + 33, SEEDA + 33 + 1)] :=
    Infra.FrameExcept.trans (frame_mstore8 _ _ _) (frame_mstore8 _ _ _)
  have hm1 := Infra.FrameExcept.trans hfr hfr1
  have hrc1 : RCTable M1 := Infra.RCTable.frame hrc hm1 (by avoid)
  have hrho1 : BytesAt M1 SEEDA rho := Infra.BytesAt.frame hrho hm1 (by rw [hrs]; avoid)
  have hseed : MachineState.readPadded M1 SEEDA 34 =
      rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i] := by
    refine readPadded_seed hrs hrho1 ?_ ?_ (by omega) (by omega)
    · rw [byteAt_mstore8_other _ _ (by omega), byteAt_mstore8_self, Nat.mod_eq_of_lt (by omega)]
    · rw [byteAt_mstore8_self, Nat.mod_eq_of_lt (by omega)]
  -- shake
  obtain ⟨M2, hbs2, hfr2, hcall2⟩ := shake_call (rate := 168) (ptr := SEEDA) (len := 34)
    (out := XOF) (blocks := 6) hs
    (hr.callee (B' := Stack.shake) (ret' := 4481)
      (extra := [wd j, wd i, wd (goodN rho i j), wd ret]) (by decide) (by simp)
      (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    (Or.inr rfl) ⟨by norm_num, le_rfl⟩ hrc1 (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨by simp only [SEEDA]; omega, by simp only [XOF]; omega⟩
  rw [hseed] at hbs2
  -- rejSample
  obtain ⟨M3, hpoly3, hfr3, hcall3⟩ := rejSample_call (dst := AP) hs
    (hr.callee (B' := Stack.rejSample) (ret' := 4493)
      (extra := [wd j, wd i, wd (goodN rho i j), wd ret]) (by decide) (by simp)
      (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    hbs2 (size_squeeze6 _) (by decide) (by simp only [AP, POLY]; omega)
  have hA : aE rho i j = Fips204.rejNTTPolyOf (Fips202.squeeze 168
      (Fips202.absorb 168 (Fips202.pad 168 0x1F
        (rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i]))) 6) :=
    rejNTTPoly_eq_squeeze _
  -- accumulate
  let zj := ZH + POLY * j
  let v : Nat → Nat := fun t =>
    (word M3 (ACC + 32 * t) + word M3 (AP + 32 * t) * word M3 (zj + 32 * t) % Fips204.q) %
      Fips204.q
  have hvq : ∀ t, v t < Fips204.q := fun t => Nat.mod_lt _ (by unfold Fips204.q; omega)
  have hv256 : ∀ t, v t < 2 ^ 256 := fun t =>
    Nat.lt_trans (hvq t) (by unfold Fips204.q; norm_num)
  let mem : Nat → ByteArray := Infra.storeWords M3 ACC v
  let I : Nat → State := fun t => callState s 4507
    (wd t :: wd zj :: wd j :: wd i :: wd (goodN rho i (j + 1)) :: wd ret :: tail) (mem t)
  have hbody : ∀ t, t < 256 → Infra.Reach (I t) (I (t + 1)) 131 := by
    intro t ht
    have hfw := Infra.FrameExcept.storeWords M3 ACC v t
    refine (b_inner hs (ret := ret) htail haw haw' hj ht rfl (mem t)).of_eq rfl ?_
    simp only [I, mem, Infra.storeWords_succ]
    congr 3
    simp only [v]
    rw [Infra.FrameExcept.word hfw (by avoid), Infra.FrameExcept.word hfw (by avoid),
      Infra.FrameExcept.word hfw (by avoid)]
  have hloop := Infra.Reach.loop 256 hbody
  have hflag : goodN rho i j &&& (if (Fips204.rejNTTPolyOf (Fips202.squeeze 168
      (Fips202.absorb 168 (Fips202.pad 168 0x1F
        (rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i]))) 6)).isSome then 1 else 0) =
      goodN rho i (j + 1) := by
    rw [goodN_succ, hA]
  have h1 := b_toShake hs (ret := ret) htail haw haw' (g := goodN rho i j) hi hj M
  have h2 := Infra.call_iff.mp hcall2
  have h3 := b_toRej hs (ret := ret) htail haw haw' (i := i) (j := j) (g := goodN rho i j) M2
  have h4 := Infra.call_iff.mp hcall3
  have h5 := b_innerInit hs (ret := ret) htail haw haw' (i := i) (j := j) (g := goodN rho i j)
    (f := if (Fips204.rejNTTPolyOf (Fips202.squeeze 168
      (Fips202.absorb 168 (Fips202.pad 168 0x1F
        (rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i]))) 6)).isSome then 1 else 0) M3
  rw [hflag] at h5
  have h6 := b_innerExit hs (ret := ret) htail haw haw' (i := i) (j := j) (g := goodN rho i (j + 1))
    (zj := zj) (mem 256)
  refine ⟨mem 256, ⟨?_, ?_, ?_⟩, ?_⟩
  · have := Infra.FrameExcept.trans (Infra.FrameExcept.trans (Infra.FrameExcept.trans hm1 hfr2)
      hfr3) (Infra.FrameExcept.storeWords M3 ACC v 256)
    exact Infra.FrameExcept.mono this (by decide)
  · intro t ht
    rw [Infra.word_storeWords (hv256 t) 256 ht]
    exact hvq t
  · intro aRow hrow t ht
    rw [Infra.word_storeWords (hv256 t) 256 ht, azP_succ_get _ _ _ ht]
    have hf13 := Infra.FrameExcept.trans (Infra.FrameExcept.trans hfr1 hfr2) hfr3
    have hacc' := hacc aRow (fun j' hj' => hrow j' (by omega)) t ht
    have hw1 : word M3 (ACC + 32 * t) = word M (ACC + 32 * t) :=
      Infra.FrameExcept.word hf13 (by avoid)
    have hw2 := ((hpoly3 aRow[j]! (by rw [← hA]; exact hrow j (by omega))).1).2 t ht
    have hw3 := (Infra.PolyAt.frame (hzs j hj)
      (Infra.FrameExcept.trans (Infra.FrameExcept.trans hm1 hfr2) hfr3) (by avoid)).2 t ht
    simp only [v]
    rw [acc_step _ _ _ _ _ hw2 hw3, hw1, hacc']
  · have := (((((h1.trans h2).trans h3).trans h4).trans h5).trans hloop).trans h6
    exact this

end MlDsa44.Proofs.Row
