import MlDsaOpt44.Fn.Decode.HintLoop
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `dhint` end to end (WP8)

Entry, the four unrolled rows (`row_step` with each row's block lemmas), the
trailing scan and the exit; the result flag is `hintGood` of the reference
model, hence `okH` by `hintBitUnpack_eq`.
-/

namespace MlDsaOpt44.Proofs.DecodeH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsa44.Proofs.Decode (HS outerStep hs0 outerAll hintGood fillH setH okIdx WF WF_setH setH_get
  WF_hs0 hintBitUnpack_eq)

theorem dhint_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.dhint ret tail) (m : ByteArray) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hz : ZeroOn m HP (HP + 8192)) :
    ∃ m', (∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧ word m' (HP + 32 * t) = pack4 b) ∧
      (∀ h, hintOf s.executionEnv.calldata = some h →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (HP + 32 * t)) r = (h[r]![t]!).toNat) ∧
      FrameExcept m m' [(HP, HP + 8192)] ∧
      Call s Entry.dhint [] ret tail m [flag (okH s.executionEnv.calldata)] m' Gas.dhint := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.dhint, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  have hmem : 59648 ≤ 32 * s.activeWords.toNat := by simp only [memWords] at hsz; omega
  have B0 : RowBlocks s ret tail 0 1 7534 7561 7631 :=
    ⟨fun M G _ _ h1 h2 h3 => h0_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h0_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h0_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h0_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h0_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h0_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B1 : RowBlocks s ret tail 1 18446744073709551616 7631 7658 7736 :=
    ⟨fun M G _ _ h1 h2 h3 => h1_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h1_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h1_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h1_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h1_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h1_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B2 : RowBlocks s ret tail 2 340282366920938463463374607431768211456 7736 7763 7849 :=
    ⟨fun M G _ _ h1 h2 h3 => h2_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h2_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h2_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h2_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h2_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h2_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B3 : RowBlocks s ret tail 3 6277101735386680763835789423207666416102355444464034512896
      7849 7876 7970 :=
    ⟨fun M G _ _ h1 h2 h3 => h3_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h3_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h3_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h3_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h3_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h3_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have he := h_entry (ret := ret) (tail := tail) hs htl m
  obtain ⟨M1, hi1, hl1, hu1, r1⟩ := row_step B0 hcd (by norm_num) (by norm_num) hs0 (inv_zero hz)
    (by simp [hs0])
  obtain ⟨M2, hi2, hl2, hu2, r2⟩ := row_step B1 hcd (by norm_num) (by norm_num) _ hi1 hu1
  obtain ⟨M3, hi3, hl3, hu3, r3⟩ := row_step B2 hcd (by norm_num) (by norm_num) _ hi2 hu2
  obtain ⟨M4, hi4, hl4, hu4, r4⟩ := row_step B3 hcd (by norm_num) (by norm_num) _ hi3 hu3
  generalize hst1 : outerStep (yv s.executionEnv.calldata) hs0 0 = st1 at hi1 hl1 hu1 r1 hi2 hl2 hu2 r2 hi3 hl3 hu3 r3 hi4 hl4 hu4 r4
  generalize hst2 : outerStep (yv s.executionEnv.calldata) st1 1 = st2 at hi2 hl2 hu2 r2 hi3 hl3 hu3 r3 hi4 hl4 hu4 r4
  generalize hst3 : outerStep (yv s.executionEnv.calldata) st2 2 = st3 at hi3 hl3 hu3 r3 hi4 hl4 hu4 r4
  generalize hst4 : outerStep (yv s.executionEnv.calldata) st3 3 = st4 at hi4 hl4 hu4 r4
  have hfin := tscan (ret := ret) hs htl hcd M4 (a := st4.index) st4.good (80 - st4.index) (by omega)
  rw [show st4.index + (80 - st4.index) = 80 by omega] at hfin
  have hex := h_texit hs hr htl M4
    (flag (st4.good && (List.range' st4.index (80 - st4.index)).all
      (fun idx => yv s.executionEnv.calldata idx == 0)))
  have hrun := (he.trans (r1.trans (r2.trans (r3.trans (r4.trans (hfin.trans hex))))))
  -- the spec
  have hspec : hintOf s.executionEnv.calldata = if hintGood (yv s.executionEnv.calldata) then
      some (outerAll (yv s.executionEnv.calldata)).H else none :=
    hintBitUnpack_eq (s.executionEnv.calldata.extract H0 HDR)
  have hall : outerAll (yv s.executionEnv.calldata) = st4 := by
    rw [← hst4, ← hst3, ← hst2, ← hst1]; unfold outerAll; simp only [List.foldl_cons, List.foldl_nil]
  have hgood : hintGood (yv s.executionEnv.calldata) =
      (st4.good && (List.range' st4.index (80 - st4.index)).all
        (fun idx => yv s.executionEnv.calldata idx == 0)) := by
    unfold hintGood; rw [hall]
  obtain ⟨hwf, hw, hfr⟩ := hi4
  refine ⟨M4, fun t ht => ⟨bits st4.H t, fun r hr => bits_le hwf ht hr, hw t ht⟩, fun h hh => ?_, hfr, ?_⟩
  · rw [hspec] at hh
    split at hh
    · have e := Option.some.inj hh
      subst e
      intro t ht r hr
      rw [hall, hw t ht, lane_pack4' (fun k hk => by have := bits_le hwf ht hk; omega) hr]
      rfl
    · cases hh
  · rw [call_iff, Entry.dhint, Gas.dhint]
    have hres : okH s.executionEnv.calldata =
        (st4.good && (List.range' st4.index (80 - st4.index)).all
          (fun idx => yv s.executionEnv.calldata idx == 0)) := by
      unfold okH; rw [hspec, ← hgood]; split <;> simp_all
    rw [hres]
    refine (hrun.mono ?_).of_eq (by simp [hs0, flag]) (by simp)
    omega

end MlDsaOpt44.Proofs.DecodeH
