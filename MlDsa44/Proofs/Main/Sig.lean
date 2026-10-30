import MlDsa44.Proofs.Main.Hashes
set_option warningAsError true
/-!
# Signature decoding, the challenge, and `ρ`

From the return of the `μ` absorption (pc 5112) to the row-loop head
(pc 5200): `ok := decodeZ(); ok &= decodeHint()`, the challenge
`c = SampleInBall(c̃)` from `shake256(c̃)` squeezed into `XOF`, `ntt(CH)`, and
`ρ` copied to `SEEDA`.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.Infra

/-- `‖z‖∞ < γ₁ − β`. -/
def fzOf (cd : ByteArray) : Bool := Fips204.normBelow (zOf cd) (Fips204.gamma1 - Fips204.beta)

/-- The hint decodes. -/
def fhOf (cd : ByteArray) : Bool := (Fips204.hintBitUnpack (hintBytesOf cd)).isSome

/-- `c̃`. -/
def cTildeOf (cd : ByteArray) : ByteArray := cd.extract 1312 1344

/-- `SampleInBall(c̃)` succeeds. -/
def fcOf (cd : ByteArray) : Bool :=
  (Fips204.sampleInBallOf (Fips204.H (cTildeOf cd) Fips204.sampleInBallLimit)).isSome

/-- `ẑ[i] = NTT(z[i] mod q)`. -/
def zHatOf (cd : ByteArray) (i : Nat) : Fips204.Poly :=
  Fips204.ntt ((zOf cd)[i]!.map (· % (Fips204.q : Int)))

/-- `ρ`. -/
def rhoOf (cd : ByteArray) : ByteArray := (pkOf cd).extract 0 32

/-- Memory facts that hold from the row-loop head on. -/
structure Inv (cd M : ByteArray) (cH : Fips204.Poly) : Prop where
  rc : RCTable M
  zeta : ZetaTable M
  mu : BytesAt M W1 (muOf cd)
  zh : ∀ i, i < 4 → PolyAt M (ZH + POLY * i) (zHatOf cd i) ∧ Reduced (zHatOf cd i)
  bits : ∀ i, i < 4 → ∀ j, j < 256 → byteAt M (HB + 256 * i + j) ≤ 1
  hint : ∀ h, Fips204.hintBitUnpack (hintBytesOf cd) = some h → HintAt M h
  ch : PolyAt M CH cH
  chRed : Reduced cH
  seed : BytesAt M SEEDA (rhoOf cd)

theorem muOf_size (cd : ByteArray) : (muOf cd).size = 64 := H_size _ _

theorem rhoOf_size {cd : ByteArray} (h : 3732 ≤ cd.size) : (rhoOf cd).size = 32 := by
  simp [rhoOf, pkOf, ByteArray.size_extract]; omega

theorem Inv.frame {cd M M' : ByteArray} {cH : Fips204.Poly} {rs : List (Nat × Nat)}
    (hI : Inv cd M cH) (hf : FrameExcept M M' rs) (hcd : 3732 ≤ cd.size)
    (h1 : Avoids rs RC (RC + 768)) (h2 : Avoids rs ZETA (ZETA + POLY)) (h3 : Avoids rs W1 (W1 + 64))
    (h4 : Avoids rs ZH (ZH + 4 * POLY)) (h5 : Avoids rs HB (HB + 1024)) (h6 : Avoids rs CH (CH + POLY))
    (h7 : Avoids rs SEEDA (SEEDA + 32)) : Inv cd M' cH where
  rc := RCTable.frame hI.rc hf h1
  zeta := ZetaTable.frame hI.zeta hf h2
  mu := BytesAt.frame hI.mu hf (by rw [muOf_size]; exact h3)
  zh := fun i hi => ⟨PolyAt.frame (hI.zh i hi).1 hf
      (h4.mono (by simp only [POLY]; omega) (by simp only [POLY]; omega)), (hI.zh i hi).2⟩
  bits := fun i hi j hj => by
    rw [FrameExcept.byteAt hf (h5.mono (by omega) (by omega))]; exact hI.bits i hi j hj
  hint := fun h hh => HintAt.frame (hI.hint h hh) hf h5
  ch := PolyAt.frame hI.ch hf h6
  chRed := hI.chRed
  seed := BytesAt.frame hI.seed hf (by rw [rhoOf_size hcd]; exact h7)

theorem _root_.MlDsa44.Proofs.PolyAt.unique {m : ByteArray} {b : Nat} {p p' : Fips204.Poly}
    (h : PolyAt m b p) (h' : PolyAt m b p') : p = p' := by
  apply Array.ext (by rw [h.1, h'.1])
  intro i hi hi'
  have hi256 : i < 256 := by rw [h.1] at hi; exact hi
  have e := (h.2 i hi256).symm.trans (h'.2 i hi256)
  rwa [getElem!_pos p i hi, getElem!_pos p' i hi'] at e

theorem ite_land (a b : Bool) :
    ((if a = true then 1 else 0) &&& (if b = true then 1 else 0) : Nat) =
      if (a && b) = true then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- Cost from the return of the `μ` absorption to the row-loop head. -/
def sigCost : Nat :=
  17 + Gas.decodeZ + 17 + Gas.decodeHint + 21 + 6 + 29 + Gas.shake 136 32 2 + 17 +
    Gas.sampleInBall + 29 + Gas.ntt + 9 + 6 + 2

section blocks
variable {s : State} (hs : Ctx s)
include hs

theorem sig_block1 (mlen : Nat) (M : ByteArray) :
    Reach (callState s 5112 [wd mlen] M) (callState s 4000 [wd 0, wd 5121, wd mlen] M) 17 := by
  evm_reach [3273, 3274, 3275, 3276, 3277]

theorem sig_block2 (mlen : Nat) (b : Bool) (M : ByteArray) :
    Reach (callState s 5121 [flag b, wd mlen] M)
      (callState s 3786 [wd 0, wd 5130, flag b, wd mlen] M) 17 := by
  evm_reach [3278, 3279, 3280, 3281, 3282] with [flag]

theorem sig_block3 (mlen : Nat) (a b : Bool) (M : ByteArray) :
    Reach (callState s 5130 [flag b, flag a, wd mlen] M)
      (callState s 5144 [wd SEEDC, wd 1312, wd 32, flag (a && b), wd mlen] M) 21 := by
  evm_reach [3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290] with [flag, ite_land, SEEDC]

theorem sig_block4 (mlen : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5145 [flag a, wd mlen] M)
      (callState s 2680 [wd 136, wd SEEDC, wd 32, wd XOF, wd 2, wd 5166, flag a, wd mlen] M) 29 := by
  evm_reach [3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299] with [flag, SEEDC, XOF]

theorem sig_block5 (mlen : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5166 [flag a, wd mlen] M)
      (callState s 3637 [wd 0, wd 5175, flag a, wd mlen] M) 17 := by
  evm_reach [3300, 3301, 3302, 3303, 3304] with [flag]

theorem sig_block6 (mlen : Nat) (a b : Bool) (M : ByteArray) :
    Reach (callState s 5175 [flag b, flag a, wd mlen] M)
      (callState s 3107 [wd CH, wd 5190, flag (a && b), wd mlen] M) 29 := by
  evm_reach [3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313] with [flag, ite_land, CH]

theorem sig_block7 (mlen : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5190 [flag a, wd mlen] M)
      (callState s 5198 [wd SEEDA, wd 0, wd 32, flag a, wd mlen] M) 9 := by
  evm_reach [3314, 3315, 3316, 3317] with [flag, SEEDA]

theorem sig_block8 (mlen : Nat) (a : Bool) (M : ByteArray) :
    Reach (callState s 5199 [flag a, wd mlen] M) (callState s 5200 [wd 0, flag a, wd mlen] M) 2 := by
  evm_reach [3319] with [flag]

end blocks

theorem frame_cdc (m cd : ByteArray) (d src n : Nat) :
    FrameExcept m (MachineState.writeBytes m (MachineState.readPadded cd src n) d) [(d, d + n)] := by
  simpa using FrameExcept.writeBytes m (MachineState.readPadded cd src n) d

theorem cTildeOf_size {cd : ByteArray} (h : 3732 ≤ cd.size) : (cTildeOf cd).size = 32 := by
  simp [cTildeOf, ByteArray.size_extract]; omega

theorem sig_phase {s : State} (hs : Ctx s) {mlen : Nat}
    (hmlen : mlen + 3732 = s.executionEnv.calldata.size)
    (hW : MSGIN + mlen + 288 ≤ 32 * s.activeWords.toNat) {M : ByteArray}
    (hrc : RCTable M) (hz : ZetaTable M) (hmu : BytesAt M W1 (muOf s.executionEnv.calldata)) :
    ∃ M' cH, Inv s.executionEnv.calldata M' cH ∧
      (∀ c, Fips204.sampleInBallOf (Fips204.H (cTildeOf s.executionEnv.calldata)
          Fips204.sampleInBallLimit) = some c → cH = Fips204.ntt (c.map (· % (Fips204.q : Int)))) ∧
      Reach (callState s 5112 [wd mlen] M)
        (callState s 5200 [wd 0, flag ((fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata) &&
          fcOf s.executionEnv.calldata), wd mlen] M') sigCost := by
  have hcd : 3732 ≤ s.executionEnv.calldata.size := by omega
  have hfit := hs.calldataFits
  -- z
  obtain ⟨M1, hzh1, hf1, hC1⟩ := decodeZ_call hs
    (retOK_top (ret := 5121) (tail := [wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.decodeZ, Stack.unpack, Stack.ntt, Stack.leaf])) hz hcd
  have hR1 : Reach (callState s 4000 [wd 0, wd 5121, wd mlen] M)
      (callState s 5121 [flag (fzOf s.executionEnv.calldata), wd mlen] M1) Gas.decodeZ :=
    (Infra.call_iff.mp hC1).of_eq (by simp [Entry.decodeZ]) (by simp [fzOf])
  -- h
  obtain ⟨M2, hbits2, hhint2, hf2, hC2⟩ := decodeHint_call hs
    (retOK_top (ret := 5130) (tail := [flag (fzOf s.executionEnv.calldata), wd mlen])
      (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.decodeHint, Stack.leaf])) M1 hcd
  have hR2 : Reach (callState s 3786 [wd 0, wd 5130, flag (fzOf s.executionEnv.calldata), wd mlen] M1)
      (callState s 5130 [flag (fhOf s.executionEnv.calldata), flag (fzOf s.executionEnv.calldata),
        wd mlen] M2) Gas.decodeHint :=
    (Infra.call_iff.mp hC2).of_eq (by simp [Entry.decodeHint]) (by simp [fhOf])
  -- c̃ → XOF
  have hR3 := reach_calldatacopy hs 3291 (pc := 5144) (d := SEEDC) (src := 1312) (n := 32)
      (rest := [flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata), wd mlen]) (m := M2)
      (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
      (by unfold SEEDC; norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold SEEDC MSGIN at *; omega) (by simp)
  have hf3 := frame_cdc M2 s.executionEnv.calldata SEEDC 1312 32
  have hct : BytesAt (MachineState.writeBytes M2 (MachineState.readPadded s.executionEnv.calldata 1312 32)
      SEEDC) SEEDC (cTildeOf s.executionEnv.calldata) :=
    bytesAt_calldatacopy M2 _ SEEDC 1312 32 (by omega)
  generalize hM3 : MachineState.writeBytes M2 (MachineState.readPadded s.executionEnv.calldata 1312 32)
    SEEDC = M3 at hR3 hf3 hct
  have hctr : MachineState.readPadded M3 SEEDC 32 = cTildeOf s.executionEnv.calldata := by
    have := readPadded_of_bytesAt hct
    rwa [cTildeOf_size hcd] at this
  have hrc3 : RCTable M3 :=
    RCTable.frame (RCTable.frame (RCTable.frame hrc hf1 (by avoid)) hf2 (by avoid)) hf3 (by avoid)
  obtain ⟨M4, hb4, hf4, hC4⟩ := shake_call hs
    (retOK_top (ret := 5166) (tail := [flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata),
        wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.shake, Stack.keccakF, Stack.xorBlock, Stack.loadLE64, Stack.storeLE64,
        Stack.bswap64, Stack.leaf]))
    (m := M3) (rate := 136) (ptr := SEEDC) (len := 32) (out := XOF) (blocks := 2)
    (Or.inl rfl) (by norm_num) hrc3 (by unfold ZETA SEEDC; omega) (by unfold PADB SEEDC; omega)
    (by unfold ZETA XOF; omega) (by unfold PADB XOF; omega) (by unfold SEEDC XOF; omega)
    (by unfold SEEDC XOF MSGIN at *; omega)
  have hR4 : Reach (callState s 2680 [wd 136, wd SEEDC, wd 32, wd XOF, wd 2, wd 5166,
        flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata), wd mlen] M3)
      (callState s 5166 [flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata), wd mlen] M4)
      (Gas.shake 136 32 2) :=
    (Infra.call_iff.mp hC4).of_eq (by simp [Entry.shake]) (by simp)
  rw [hctr] at hb4
  have hbs : BytesAt M4 XOF (Fips204.H (cTildeOf s.executionEnv.calldata) Fips204.sampleInBallLimit) :=
    bytesAt_H hb4 (by unfold Fips204.sampleInBallLimit; norm_num)
  -- c
  have hz4 : ZetaTable M4 := ZetaTable.frame (ZetaTable.frame (ZetaTable.frame (ZetaTable.frame hz hf1
    (by avoid)) hf2 (by avoid)) hf3 (by avoid)) hf4 (by avoid)
  obtain ⟨M5, ⟨cH0, hcH0, hred0⟩, hsome5, hf5, hC5⟩ := sampleInBall_call hs
    (retOK_top (ret := 5175) (tail := [flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata),
        wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.sampleInBall, Stack.zeroPoly, Stack.leaf])) hbs (H_size _ _)
  have hR5 : Reach (callState s 3637 [wd 0, wd 5175,
        flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata), wd mlen] M4)
      (callState s 5175 [flag (fcOf s.executionEnv.calldata),
        flag (fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata), wd mlen] M5)
      Gas.sampleInBall :=
    (Infra.call_iff.mp hC5).of_eq (by simp [Entry.sampleInBall]) (by simp [fcOf])
  have hz5 : ZetaTable M5 := ZetaTable.frame hz4 hf5 (by avoid)
  obtain ⟨M6, hch6, hred6, hf6, hC6⟩ := ntt_call hs
    (retOK_top (ret := 5190) (tail := [flag ((fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata) &&
        fcOf s.executionEnv.calldata), wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.ntt, Stack.leaf])) hcH0 hred0 hz5 (by unfold ZETA POLY CH; omega)
    (by unfold CH POLY MSGIN at *; omega)
  have hR6 : Reach (callState s 3107 [wd CH, wd 5190,
        flag ((fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata) && fcOf s.executionEnv.calldata),
        wd mlen] M5)
      (callState s 5190 [flag ((fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata) &&
        fcOf s.executionEnv.calldata), wd mlen] M6) Gas.ntt :=
    (Infra.call_iff.mp hC6).of_eq (by simp [Entry.ntt]) (by simp)
  -- ρ
  have hR7 := reach_calldatacopy hs 3318 (pc := 5198) (d := SEEDA) (src := 0) (n := 32)
      (rest := [flag ((fzOf s.executionEnv.calldata && fhOf s.executionEnv.calldata) &&
        fcOf s.executionEnv.calldata), wd mlen]) (m := M6)
      (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
      (by unfold SEEDA; norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold SEEDA MSGIN at *; omega) (by simp)
  have hf7 := frame_cdc M6 s.executionEnv.calldata SEEDA 0 32
  have hseed : BytesAt (MachineState.writeBytes M6 (MachineState.readPadded s.executionEnv.calldata 0 32)
      SEEDA) SEEDA (rhoOf s.executionEnv.calldata) := by
    have := bytesAt_calldatacopy M6 s.executionEnv.calldata SEEDA 0 32 (by omega)
    rwa [show rhoOf s.executionEnv.calldata = s.executionEnv.calldata.extract 0 (0 + 32) by
      simp [rhoOf, pkOf, ByteArray.extract_extract]]
  generalize hM7 : MachineState.writeBytes M6 (MachineState.readPadded s.executionEnv.calldata 0 32)
    SEEDA = M7 at hR7 hf7 hseed
  -- invariant
  refine ⟨M7, Fips204.ntt cH0, ?_, ?_, ?_⟩
  · have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf1 hf2) hf3) hf4) hf5) hf6) hf7
    have hf27 := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans hf2 hf3) hf4) hf5) hf6) hf7
    have hf37 := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans hf3 hf4) hf5) hf6) hf7
    exact {
      rc := RCTable.frame hrc hf (by avoid)
      zeta := ZetaTable.frame hz hf (by avoid)
      mu := BytesAt.frame hmu hf (by rw [muOf_size]; avoid)
      zh := fun i hi => by
        refine ⟨PolyAt.frame (hzh1 i hi).1 hf27 ?_, (hzh1 i hi).2⟩
        have : i ≤ 3 := by omega
        avoid
      bits := fun i hi j hj => by
        rw [FrameExcept.byteAt hf37 (by avoid)]; exact hbits2 i hi j hj
      hint := fun h hh => HintAt.frame (hhint2 h hh) hf37 (by avoid)
      ch := PolyAt.frame hch6 hf7 (by avoid)
      chRed := hred6
      seed := hseed }
  · intro c hc
    rw [PolyAt.unique hcH0 (hsome5 c hc).1]
  · have h := (sig_block1 hs mlen M).trans hR1
    have h := h.trans (sig_block2 hs mlen _ M1)
    have h := h.trans hR2
    have h := h.trans (sig_block3 hs mlen _ _ M2)
    have h := h.trans hR3
    have h := h.trans (sig_block4 hs mlen _ M3)
    have h := h.trans hR4
    have h := h.trans (sig_block5 hs mlen _ M4)
    have h := h.trans hR5
    have h := h.trans (sig_block6 hs mlen _ _ M5)
    have h := h.trans hR6
    have h := h.trans (sig_block7 hs mlen _ M6)
    have h := h.trans hR7
    have h := h.trans (sig_block8 hs mlen _ M7)
    exact h.mono (le_of_eq (by unfold sigCost; omega))

end MlDsa44.Proofs.Main
