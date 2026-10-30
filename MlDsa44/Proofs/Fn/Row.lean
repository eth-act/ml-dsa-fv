import MlDsa44.Proofs.Fn.Shake
import MlDsa44.Proofs.Fn.Sampling
import MlDsa44.Proofs.Fn.Decode
import MlDsa44.Proofs.Fn.Row.Outer
/-!
# `computeRow`: one row of `w'Approx = NTT⁻¹(Â ∘ ẑ − ĉ ∘ t̂₁)`

Yul: `computeRow(i) -> good`. Zero `ACC`; for `j < 4`: set the seed bytes
`SEEDA[32] = j`, `SEEDA[33] = i`, squeeze six SHAKE128 blocks of
`ρ ‖ j ‖ i` into `XOF`, `rejSample(AP)`, accumulate `AP ∘ ZH[j]` into `ACC`.
Then unpack `t1[i]` from calldata scaled by `2^13` into `TP`, `ntt(TP)`,
subtract `CH ∘ TP`, and `nttInv(ACC)`. `good` iff every `RejNTTPoly`
succeeded within the Appendix C limit.

The straight-line blocks are in `Row/Blocks.lean`, one outer-loop iteration
in `Row/Outer.lean`, and the pure facts in `Row/Math.lean`.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

namespace Gas

/-- Exact cost: entry, `zeroPoly`, four outer iterations (seed, `shake`,
`rejSample`, 256 accumulate steps), 256 unpack steps, `ntt`, 256 subtract
steps, `nttInv`, return. -/
def computeRow : Nat :=
  26 + zeroPoly + 3 +
    4 * (85 + shake 168 34 6 + 20 + rejSample + 29 + 256 * 131 + 56) + 31 +
    256 * (65 + unpack + 50) + 46 + ntt + 3 + 256 * 142 + 46 + nttInv + 14

end Gas

/-- `Â[i][j] = RejNTTPoly(ρ ‖ j ‖ i)` (Algorithm 32). -/
def aEntry (rho : ByteArray) (i j : Nat) : Option Fips204.Poly :=
  Fips204.rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i])

/-- `NTT(t1[i] · 2^d)` for the public key `pk`. -/
def t1Hat (pk : ByteArray) (i : Nat) : Fips204.Poly :=
  Fips204.ntt (((Fips204.pkDecode pk).2[i]!).map (· * 2 ^ Fips204.d))

/-- Row `i` of `NTT⁻¹(Â ∘ ẑ − ĉ ∘ t̂₁)` from row `i` of `Â`. -/
def rowApprox (aRow zHat : Array Fips204.Poly) (cHat t1H : Fips204.Poly) : Fips204.Poly :=
  let az := (List.range Fips204.l).foldl
    (fun acc j => Fips204.addNTT acc (Fips204.multiplyNTT aRow[j]! zHat[j]!)) Fips204.zeroPoly
  Fips204.nttInv ((Array.range 256).map fun j =>
    (az[j]! - (Fips204.multiplyNTT cHat t1H)[j]!) % Fips204.q)

-- `hzHat` and `hcred` are part of the shared contract but not needed here.
set_option linter.unusedVariables false in
open Row in
theorem computeRow_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.computeRow ret tail) {m : ByteArray} {i : Nat} (hi : i < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size)
    (hrc : RCTable m) (hz : ZetaTable m)
    {zHat : Array Fips204.Poly} (hzHat : zHat.size = 4)
    (hzs : ∀ j, j < 4 → PolyAt m (ZH + POLY * j) zHat[j]! ∧ Reduced zHat[j]!)
    {cHat : Fips204.Poly} (hc : PolyAt m CH cHat) (hcred : Reduced cHat)
    (hrho : BytesAt m SEEDA (pkOf s.executionEnv.calldata |>.extract 0 32)) :
    ∃ m',
      (∃ f, PolyAt m' ACC f ∧ Reduced f) ∧
      (∀ aRow : Array Fips204.Poly, aRow.size = 4 →
        (∀ j, j < 4 → aEntry ((pkOf s.executionEnv.calldata).extract 0 32) i j = some aRow[j]!) →
          PolyAt m' ACC (rowApprox aRow zHat cHat (t1Hat (pkOf s.executionEnv.calldata) i)) ∧
          Reduced (rowApprox aRow zHat cHat (t1Hat (pkOf s.executionEnv.calldata) i))) ∧
      FrameExcept m m' [(ST, RC), (AP, AP + POLY), (ACC, ACC + POLY), (TP, TP + POLY),
        (XOF, XOF + 0x420), (SEEDA + 32, SEEDA + 34), (PADB, PADB + 192)] ∧
      Call s Entry.computeRow [wd i] ret tail m
        [flag ((List.range 4).all fun j =>
          (aEntry ((pkOf s.executionEnv.calldata).extract 0 32) i j).isSome)] m'
        Gas.computeRow := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; rw [stack_computeRow] at this; omega
  have haw := activeWords_ge hs
  have haw' : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hq : (0 : Int) < (Fips204.q : Int) := by unfold Fips204.q; norm_num
  generalize hcdd : s.executionEnv.calldata = cd at hcd hrho ⊢
  generalize hrhod : (pkOf cd).extract 0 32 = rho at hrho ⊢
  have hrs : rho.size = 32 := by
    rw [← hrhod, pkOf, ByteArray.size_extract, ByteArray.size_extract]; omega
  -- zeroPoly(ACC)
  obtain ⟨M0, hz0, hfr0, hcall0⟩ := zeroPoly_call (p := ACC) hs
    (hr.callee (B' := Stack.zeroPoly) (ret' := 4430) (extra := [wd i, wd 1, wd ret])
      (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    m (by simp only [ACC, POLY]; omega)
  have hP0 : OuterInv m rho i zHat 0 M0 := by
    refine ⟨Infra.FrameExcept.mono hfr0 (by decide), fun t ht => ?_, fun aRow _ t ht => hz0.2 t ht⟩
    have h := hz0.2 t ht
    rw [Fips204.zeroPoly, getElem!_pos _ t (by simpa using ht), Array.getElem_replicate] at h
    have : word M0 (ACC + 32 * t) = 0 := by omega
    rw [this]; unfold Fips204.q; omega
  -- the outer loop
  obtain ⟨MA, hPA, hloopA⟩ := reach_iter
    (S := fun j M => callState s 4432 (wd j :: wd i :: wd (goodN rho i j) :: wd ret :: tail) M)
    (P := OuterInv m rho i zHat) (c := outerCost) 4
    (fun j hj M hP => outer_step hs hr hi hj hrc (fun j hj => (hzs j hj).1) hrs hrho M hP)
    M0 hP0
  obtain ⟨hfrA, hbndA, haccA⟩ := hPA
  -- unpack t1[i] scaled by 2^13 into TP
  let g4 := goodN rho i 4
  let off := 32 + 320 * i
  let bits : Nat → Nat := fun t => Fips204.bitsToInteger (cd.extract off (off + 320)) (t * 10) 10
  let u : Nat → Nat := fun t => bits t * 2 ^ 13
  have hu : ∀ t, u t < Fips204.q := fun t => bits10_scaled_lt _ t
  have hu256 : ∀ t, u t < 2 ^ 256 := fun t =>
    Nat.lt_trans (hu t) (by unfold Fips204.q; norm_num)
  let memU : Nat → ByteArray := Infra.storeWords MA TP u
  let U : Nat → State := fun t =>
    callState s 4579 (wd t :: wd i :: wd g4 :: wd ret :: tail) (memU t)
  have hbodyU : ∀ t, t < 256 → Infra.Reach (U t) (U (t + 1)) (65 + Gas.unpack + 50) := by
    intro t ht
    have h1 := b_toUnpack hs (ret := ret) htail haw haw' (i := i) (g := g4) ht (memU t)
    have h2 := Infra.call_iff.mp (unpack_call (off := off) (n := 320) (i := t) (c := 10) hs
      (hr.callee (B' := Stack.unpack) (ret' := 4609) (extra := [wd t, wd i, wd g4, wd ret])
        (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
      (memU t) ⟨by norm_num, by norm_num⟩ (by rw [hcdd]; omega) (by omega))
    rw [hcdd] at h2
    have h3 := b_fromUnpack hs (ret := ret) htail haw haw' (i := i) (g := g4) ht
      (bitsToInteger_lt (cd.extract off (off + 320)) (t * 10) 10) (memU t)
    exact ((h1.trans h2).trans h3).of_eq rfl (by simp only [U, memU, Infra.storeWords_succ]; rfl)
  have hloopU := Infra.Reach.loop 256 hbodyU
  let MB := memU 256
  -- ntt(TP)
  let tpoly : Fips204.Poly := (Array.range 256).map fun t => ((u t : Nat) : Int)
  have hfrB : FrameExcept MA MB [(TP, TP + 32 * 256)] := Infra.FrameExcept.storeWords MA TP u 256
  have hzB : ZetaTable MB :=
    Infra.ZetaTable.frame hz (Infra.FrameExcept.trans hfrA hfrB) (by avoid)
  obtain ⟨MC, hnttC, -, hfrC, hcallC⟩ := ntt_call (p := TP) (f := tpoly) hs
    (hr.callee (B' := Stack.ntt) (ret' := 4646) (extra := [wd i, wd g4, wd ret])
      (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    ⟨by simp [tpoly], fun t ht => by
      rw [Infra.word_storeWords (hu256 t) 256 ht, getElem!_range_map _ ht]⟩
    (fun t ht => by
      rw [getElem!_range_map _ ht]
      exact ⟨by positivity, by exact_mod_cast hu t⟩)
    hzB (by decide) (by simp only [TP, POLY]; omega)
  have ht1 : t1Hat (pkOf cd) i = Fips204.ntt tpoly := by
    rw [t1Hat, pkOf, t1_scaled cd hi]
  -- ACC -= CH ∘ TP
  let w : Nat → Nat := fun t =>
    (word MC (ACC + 32 * t) +
      (Fips204.q - word MC (CH + 32 * t) * word MC (TP + 32 * t) % Fips204.q)) % Fips204.q
  have hw : ∀ t, w t < Fips204.q := fun t => Nat.mod_lt _ (by unfold Fips204.q; omega)
  have hw256 : ∀ t, w t < 2 ^ 256 := fun t =>
    Nat.lt_trans (hw t) (by unfold Fips204.q; norm_num)
  let memS : Nat → ByteArray := Infra.storeWords MC ACC w
  let V : Nat → State := fun t =>
    callState s 4648 (wd t :: wd i :: wd g4 :: wd ret :: tail) (memS t)
  have hbodyS : ∀ t, t < 256 → Infra.Reach (V t) (V (t + 1)) 142 := by
    intro t ht
    have hfw := Infra.FrameExcept.storeWords MC ACC w t
    refine (b_sub hs (ret := ret) htail haw haw' (i := i) (g := g4) ht (memS t)).of_eq rfl ?_
    simp only [V, memS, Infra.storeWords_succ]
    congr 3
    simp only [w]
    rw [Infra.FrameExcept.word hfw (by avoid), Infra.FrameExcept.word hfw (by avoid),
      Infra.FrameExcept.word hfw (by avoid)]
  have hloopS := Infra.Reach.loop 256 hbodyS
  let MD := memS 256
  -- nttInv(ACC)
  let fpoly : Fips204.Poly := (Array.range 256).map fun t => ((w t : Nat) : Int)
  have hfrD : FrameExcept MC MD [(ACC, ACC + 32 * 256)] :=
    Infra.FrameExcept.storeWords MC ACC w 256
  have hfrAD := Infra.FrameExcept.trans (Infra.FrameExcept.trans
    (Infra.FrameExcept.trans hfrA hfrB) hfrC) hfrD
  have hzD : ZetaTable MD := Infra.ZetaTable.frame hz hfrAD (by avoid)
  obtain ⟨ME, hE, hEred, hfrE, hcallE⟩ := nttInv_call (p := ACC) (f := fpoly) hs
    (hr.callee (B' := Stack.nttInv) (ret' := 4726) (extra := [wd i, wd g4, wd ret])
      (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    ⟨by simp [fpoly], fun t ht => by
      rw [Infra.word_storeWords (hw256 t) 256 ht, getElem!_range_map _ ht]⟩
    (fun t ht => by
      rw [getElem!_range_map _ ht]
      exact ⟨by positivity, by exact_mod_cast hw t⟩)
    hzD (by decide) (by simp only [ACC, POLY]; omega)
  refine ⟨ME, ⟨_, hE, hEred⟩, ?_, ?_, ?_⟩
  · -- the row value
    intro aRow _ hrow
    suffices h : rowApprox aRow zHat cHat (t1Hat (pkOf cd) i) = Fips204.nttInv fpoly by
      rw [h]; exact ⟨hE, hEred⟩
    rw [rowApprox, ht1]
    congr 1
    apply Array.ext (by simp [fpoly])
    intro t h1 _
    have ht : t < 256 := by simpa using h1
    simp only [Array.getElem_map, Array.getElem_range, fpoly, w]
    rw [sub_step]
    have hfrC' : FrameExcept MA MC ([(TP, TP + 32 * 256)] ++ [(TP, TP + POLY)]) :=
      Infra.FrameExcept.trans hfrB hfrC
    have hx : word MC (ACC + 32 * t) = word MA (ACC + 32 * t) :=
      Infra.FrameExcept.word hfrC' (by avoid)
    have hy := (Infra.PolyAt.frame hc (Infra.FrameExcept.trans
      (Infra.FrameExcept.trans hfrA hfrB) hfrC) (by avoid)).2 t ht
    have hzz := hnttC.2 t ht
    rw [hx, haccA aRow (fun j hj => hrow j hj) t ht, hy, hzz, Fips204.multiplyNTT,
      getElem!_range_map _ ht]
    rfl
  · -- the frame
    exact Infra.FrameExcept.mono (Infra.FrameExcept.trans hfrAD hfrE) (by decide)
  · -- the trace
    rw [Infra.call_iff]
    have e1 := b_entry hs (ret := ret) htail haw haw' (i := i) m
    have e2 := Infra.call_iff.mp hcall0
    have e3 := b_outerInit hs (ret := ret) htail haw haw' (i := i) M0
    have e4 := b_outerExit hs (ret := ret) htail haw haw' (i := i) (g := g4) MA
    have e5 := b_toNtt hs (ret := ret) htail haw haw' (i := i) (g := g4) MB
    have e6 := Infra.call_iff.mp hcallC
    have e7 := b_subInit hs (ret := ret) htail haw haw' (i := i) (g := g4) MC
    have e8 := b_toNttInv hs (ret := ret) htail haw haw' (i := i) (g := g4) MD
    have e9 := Infra.call_iff.mp hcallE
    have e10 := b_final hs htail haw haw' (i := i) (g := g4) hr ME
    have hall := ((((((((((((e1.trans e2).trans e3).trans hloopA).trans e4).trans
      hloopU).trans e5).trans e6).trans e7).trans hloopS).trans e8).trans e9).trans e10)
    exact hall
