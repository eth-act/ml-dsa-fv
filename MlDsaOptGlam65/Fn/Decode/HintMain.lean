import MlDsaOptGlam65.Fn.Decode.HintLoop
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Decode/HintMain.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `dhint` end to end (ML-DSA-65, WP G2)

Entry, the 6 unrolled rows (`row_step` with each row's block lemmas), the trailing
scan and the exit; the result flag is `hintGood 6 55` of the model, hence `okH` by
`hintBitUnpack_eq`. Twin of `MlDsaOpt44/Fn/Decode/HintMain.lean`.
-/

namespace MlDsaOptGlam65.Proofs.DecodeH

open MlDsaOpt65.Proofs MlDsaOpt65.Proofs.DecodeH

open MlDsaOpt44.Proofs.DecodeH
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

set_option maxRecDepth 100000 in
theorem dhint_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.dhint ret tail) (m : ByteArray)
    (hz : ZeroOn m HP (HP + 0x4000)) :
    ∃ m', (∀ g, g < 2 → ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
        word m' (HP + 0x2000 * g + 32 * t) = pack4 b) ∧
      (∀ h, hintOf s.executionEnv.calldata = some h → ∀ r, r < 8 → ∀ t, t < 256 →
        lane (word m' (HP + 0x2000 * (r / 4) + 32 * t)) (r % 4) = (h[r]![t]!).toNat) ∧
      FrameExcept m m' [(HP, HP + 0x4000)] ∧
      Call s Entry.dhint [] ret tail m [flag (okH s.executionEnv.calldata)] m' Gas.dhint := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.dhint, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  have hmem : 84224 ≤ 32 * s.activeWords.toNat := by simp only [memWords] at hsz; omega
  have B0 : RowBlocks s ret tail 0 1 67840 7777 7804 7875 :=
    ⟨fun M G _ _ h1 h2 h3 => h0_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h0_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h0_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h0_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h0_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h0_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B1 : RowBlocks s ret tail 1 18446744073709551616 67840 7875 7902 7981 :=
    ⟨fun M G _ _ h1 h2 h3 => h1_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h1_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h1_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h1_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h1_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h1_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B2 : RowBlocks s ret tail 2 340282366920938463463374607431768211456 67840 7981 8008 8095 :=
    ⟨fun M G _ _ h1 h2 h3 => h2_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h2_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h2_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h2_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h2_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h2_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B3 : RowBlocks s ret tail 3 6277101735386680763835789423207666416102355444464034512896 67840 8095 8122 8217 :=
    ⟨fun M G _ _ h1 h2 h3 => h3_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h3_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h3_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h3_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h3_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h3_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B4 : RowBlocks s ret tail 4 1 76032 8217 8244 8315 :=
    ⟨fun M G _ _ h1 h2 h3 => h4_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h4_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h4_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h4_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h4_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h4_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B5 : RowBlocks s ret tail 5 18446744073709551616 76032 8315 8342 8421 :=
    ⟨fun M G _ _ h1 h2 h3 => h5_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h5_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h5_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h5_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h5_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h5_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have he := h_entry (ret := ret) (tail := tail) hs htl m
  obtain ⟨M1, hi1, hl1, hu1, r1⟩ := row_step B0 (by norm_num) (by norm_num) (by norm_num [HP]) (hs0 6) (inv_zero hz)
    (by simp [hs0])
  obtain ⟨M2, hi2, hl2, hu2, r2⟩ := row_step B1 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi1 hu1
  obtain ⟨M3, hi3, hl3, hu3, r3⟩ := row_step B2 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi2 hu2
  obtain ⟨M4, hi4, hl4, hu4, r4⟩ := row_step B3 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi3 hu3
  obtain ⟨M5, hi5, hl5, hu5, r5⟩ := row_step B4 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi4 hu4
  obtain ⟨M6, hi6, hl6, hu6, r6⟩ := row_step B5 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi5 hu5
  generalize hst1 : outerStep 55 (yv s.executionEnv.calldata) (hs0 6) 0 = st1 at hi1 hl1 hu1 r1 hi2 hl2 hu2 r2 hi3 hl3 hu3 r3 hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6
  generalize hst2 : outerStep 55 (yv s.executionEnv.calldata) st1 1 = st2 at hi2 hl2 hu2 r2 hi3 hl3 hu3 r3 hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6
  generalize hst3 : outerStep 55 (yv s.executionEnv.calldata) st2 2 = st3 at hi3 hl3 hu3 r3 hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6
  generalize hst4 : outerStep 55 (yv s.executionEnv.calldata) st3 3 = st4 at hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6
  generalize hst5 : outerStep 55 (yv s.executionEnv.calldata) st4 4 = st5 at hi5 hl5 hu5 r5 hi6 hl6 hu6 r6
  generalize hst6 : outerStep 55 (yv s.executionEnv.calldata) st5 5 = st6 at hi6 hl6 hu6 r6
  have hfin := tscan (ret := ret) hs htl M6 (a := st6.index) st6.good (55 - st6.index) (by omega)
  rw [show st6.index + (55 - st6.index) = 55 by omega] at hfin
  have hex := h_texit hs hr htl M6
    (flag (st6.good && (List.range' st6.index (55 - st6.index)).all
      (fun idx => yv s.executionEnv.calldata idx == 0)))
  have hrun := (he.trans (r1.trans ( r2.trans ( r3.trans ( r4.trans ( r5.trans ( r6.trans (hfin.trans hex))))))))
  -- the spec
  have hspec : hintOf s.executionEnv.calldata = if hintGood 6 55 (yv s.executionEnv.calldata) then
      some (outerAll 6 55 (yv s.executionEnv.calldata)).H else none :=
    hintBitUnpack_eq P (s.executionEnv.calldata.extract H0 HDR)
  have hall : outerAll 6 55 (yv s.executionEnv.calldata) = st6 := by
    rw [← hst6, ← hst5, ← hst4, ← hst3, ← hst2, ← hst1]; unfold outerAll
    rw [show List.range' 0 6 = [0, 1, 2, 3, 4, 5] from rfl]
    simp only [List.foldl_cons, List.foldl_nil]
  have hgood : hintGood 6 55 (yv s.executionEnv.calldata) =
      (st6.good && (List.range' st6.index (55 - st6.index)).all
        (fun idx => yv s.executionEnv.calldata idx == 0)) := by
    unfold hintGood; rw [hall]
  obtain ⟨hwf, hw, hfr⟩ := hi6
  refine ⟨M6, fun g hg t ht => ⟨fun j => bits st6.H t (4 * g + j), fun r _ => bits_le hwf ht _, hw g hg t ht⟩,
    fun h hh => ?_, hfr, ?_⟩
  · rw [hspec] at hh
    split at hh
    · have e := Option.some.inj hh
      subst e
      intro r hr t ht
      rw [hall, hw (r / 4) (by omega) t ht, lane_pack4' (fun j _ => by have := bits_le hwf ht (4 * (r / 4) + j); omega)
        (Nat.mod_lt _ (by omega)), show 4 * (r / 4) + r % 4 = r by omega]
      rfl
    · cases hh
  · rw [call_iff, Entry.dhint, Gas.dhint]
    have hres : okH s.executionEnv.calldata =
        (st6.good && (List.range' st6.index (55 - st6.index)).all
          (fun idx => yv s.executionEnv.calldata idx == 0)) := by
      unfold okH; rw [hspec, ← hgood]; split <;> simp_all
    rw [hres]
    refine (hrun.mono ?_).of_eq (by simp [hs0, flag]) (by simp)
    omega

end MlDsaOptGlam65.Proofs.DecodeH
