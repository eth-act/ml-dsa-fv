import MlDsaOpt87.Fn.Decode.HintLoop
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `dhint` end to end (ML-DSA-87, WP G2)

Entry, the 8 unrolled rows (`row_step` with each row's block lemmas), the trailing
scan and the exit; the result flag is `hintGood 8 75` of the model, hence `okH` by
`hintBitUnpack_eq`. Twin of `MlDsaOpt44/Fn/Decode/HintMain.lean`.
-/

namespace MlDsaOpt87.Proofs.DecodeH

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeH

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
  have B0 : RowBlocks s ret tail 0 1 67840 9263 9290 9361 :=
    ⟨fun M G _ _ h1 h2 h3 => h0_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h0_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h0_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h0_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h0_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h0_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B1 : RowBlocks s ret tail 1 18446744073709551616 67840 9361 9388 9467 :=
    ⟨fun M G _ _ h1 h2 h3 => h1_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h1_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h1_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h1_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h1_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h1_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B2 : RowBlocks s ret tail 2 340282366920938463463374607431768211456 67840 9467 9494 9581 :=
    ⟨fun M G _ _ h1 h2 h3 => h2_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h2_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h2_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h2_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h2_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h2_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B3 : RowBlocks s ret tail 3 6277101735386680763835789423207666416102355444464034512896 67840 9581 9608 9703 :=
    ⟨fun M G _ _ h1 h2 h3 => h3_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h3_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h3_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h3_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h3_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h3_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B4 : RowBlocks s ret tail 4 1 76032 9703 9730 9801 :=
    ⟨fun M G _ _ h1 h2 h3 => h4_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h4_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h4_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h4_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h4_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h4_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B5 : RowBlocks s ret tail 5 18446744073709551616 76032 9801 9828 9907 :=
    ⟨fun M G _ _ h1 h2 h3 => h5_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h5_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h5_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h5_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h5_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h5_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B6 : RowBlocks s ret tail 6 340282366920938463463374607431768211456 76032 9907 9934 10021 :=
    ⟨fun M G _ _ h1 h2 h3 => h6_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h6_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h6_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h6_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h6_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h6_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have B7 : RowBlocks s ret tail 7 6277101735386680763835789423207666416102355444464034512896 76032 10021 10048 10143 :=
    ⟨fun M G _ _ h1 h2 h3 => h7_hok hs htl M G (by simpa using h1) h2 h3,
     fun M G _ _ h1 h2 h3 h4 => h7_hbad hs htl M G h1 (by simpa using h2) h3 h4,
     fun M G _ _ h1 => h7_iexit hs htl M G h1,
     fun M G _ _ _ h1 h2 h3 h4 => h7_ifirst hs htl M G h1 h2 h3 h4 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => h7_iok hs htl M G h1 h2 h3 h4 h5 h6 h7 haw hmem,
     fun M G _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 => h7_ibad hs htl M G h1 h2 h3 h4 h5 h6 h7 h8 haw hmem⟩
  have he := h_entry (ret := ret) (tail := tail) hs htl m
  obtain ⟨M1, hi1, hl1, hu1, r1⟩ := row_step B0 (by norm_num) (by norm_num) (by norm_num [HP]) (hs0 8) (inv_zero hz)
    (by simp [hs0])
  obtain ⟨M2, hi2, hl2, hu2, r2⟩ := row_step B1 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi1 hu1
  obtain ⟨M3, hi3, hl3, hu3, r3⟩ := row_step B2 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi2 hu2
  obtain ⟨M4, hi4, hl4, hu4, r4⟩ := row_step B3 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi3 hu3
  obtain ⟨M5, hi5, hl5, hu5, r5⟩ := row_step B4 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi4 hu4
  obtain ⟨M6, hi6, hl6, hu6, r6⟩ := row_step B5 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi5 hu5
  obtain ⟨M7, hi7, hl7, hu7, r7⟩ := row_step B6 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi6 hu6
  obtain ⟨M8, hi8, hl8, hu8, r8⟩ := row_step B7 (by norm_num) (by norm_num) (by norm_num [HP]) _ hi7 hu7
  generalize hst1 : outerStep 75 (yv s.executionEnv.calldata) (hs0 8) 0 = st1 at hi1 hl1 hu1 r1 hi2 hl2 hu2 r2 hi3 hl3 hu3 r3 hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6 hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst2 : outerStep 75 (yv s.executionEnv.calldata) st1 1 = st2 at hi2 hl2 hu2 r2 hi3 hl3 hu3 r3 hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6 hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst3 : outerStep 75 (yv s.executionEnv.calldata) st2 2 = st3 at hi3 hl3 hu3 r3 hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6 hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst4 : outerStep 75 (yv s.executionEnv.calldata) st3 3 = st4 at hi4 hl4 hu4 r4 hi5 hl5 hu5 r5 hi6 hl6 hu6 r6 hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst5 : outerStep 75 (yv s.executionEnv.calldata) st4 4 = st5 at hi5 hl5 hu5 r5 hi6 hl6 hu6 r6 hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst6 : outerStep 75 (yv s.executionEnv.calldata) st5 5 = st6 at hi6 hl6 hu6 r6 hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst7 : outerStep 75 (yv s.executionEnv.calldata) st6 6 = st7 at hi7 hl7 hu7 r7 hi8 hl8 hu8 r8
  generalize hst8 : outerStep 75 (yv s.executionEnv.calldata) st7 7 = st8 at hi8 hl8 hu8 r8
  have hfin := tscan (ret := ret) hs htl M8 (a := st8.index) st8.good (75 - st8.index) (by omega)
  rw [show st8.index + (75 - st8.index) = 75 by omega] at hfin
  have hex := h_texit hs hr htl M8
    (flag (st8.good && (List.range' st8.index (75 - st8.index)).all
      (fun idx => yv s.executionEnv.calldata idx == 0)))
  have hrun := (he.trans (r1.trans ( r2.trans ( r3.trans ( r4.trans ( r5.trans ( r6.trans ( r7.trans ( r8.trans (hfin.trans hex))))))))))
  -- the spec
  have hspec : hintOf s.executionEnv.calldata = if hintGood 8 75 (yv s.executionEnv.calldata) then
      some (outerAll 8 75 (yv s.executionEnv.calldata)).H else none :=
    hintBitUnpack_eq P (s.executionEnv.calldata.extract H0 HDR)
  have hall : outerAll 8 75 (yv s.executionEnv.calldata) = st8 := by
    rw [← hst8, ← hst7, ← hst6, ← hst5, ← hst4, ← hst3, ← hst2, ← hst1]; unfold outerAll
    rw [show List.range' 0 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    simp only [List.foldl_cons, List.foldl_nil]
  have hgood : hintGood 8 75 (yv s.executionEnv.calldata) =
      (st8.good && (List.range' st8.index (75 - st8.index)).all
        (fun idx => yv s.executionEnv.calldata idx == 0)) := by
    unfold hintGood; rw [hall]
  obtain ⟨hwf, hw, hfr⟩ := hi8
  refine ⟨M8, fun g hg t ht => ⟨fun j => bits st8.H t (4 * g + j), fun r _ => bits_le hwf ht _, hw g hg t ht⟩,
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
        (st8.good && (List.range' st8.index (75 - st8.index)).all
          (fun idx => yv s.executionEnv.calldata idx == 0)) := by
      unfold okH; rw [hspec, ← hgood]; split <;> simp_all
    rw [hres]
    refine (hrun.mono ?_).of_eq (by simp [hs0, flag]) (by simp)
    omega

end MlDsaOpt87.Proofs.DecodeH
