import MlDsaOpt65.Fn.Sponge.MubBlocks
import MlDsaOpt65.Fn.Sponge.MubMath
import MlDsaOpt65.Fn.Sponge.Mub0
import MlDsaOpt65.Fn.Sponge.Spr
import MlDsaOpt65.Fn.Sponge.Cext
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
/-!
# `mub` (ML-DSA-65): composition of the blocks with `trabs`, `spr` and `cext`

`[K = 136 k, sh, ret]`, `P = |cd| − 0x144b = 66 + |M|`. The four exits:

* `K ≤ P`, `k < 5`: `trabs` absorbs calldata lanes `0x144b + K + 8x` (`x < 17`;
  lanes 17–19 masked to zero); if `P < K + 136` this is the last block and the
  code xors `0x1F` into byte `P − K` (lane `(P − K) / 8`) and `0x80` into byte 135
  (lane 16): together the lanes of block `k` of `pad 136 0x1F (tr ‖ 0 ‖ 0 ‖ M)`
  (`mub_value_full`, `mub_value_last`);
* `K ≤ P`, `k = 5`: nothing;
* `P < K ≤ P + 136`: `cext [8, sh, MU]`;
* `P + 136 < K`: nothing.

The longest path (absorb and pad) costs `91 + trabs 5 + 82 + spr + 87 = 3090 = Gas.mub`.
`trabs` is a stated contract proved elsewhere: `mub_call_aux` takes its exact
statement as the argument `htrabs`. μ's padded input appears unfolded
(`muPadded tr cd` of `Fn/Sponge.lean` is
`Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))`).
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra
open MlDsa44

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem mub_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (m : ByteArray) {sh k : Nat} (hsh : sh < 4) (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (htrabs : ∀ {s : State} (_hs : Ctx s) {ret : Nat} {tail : List UInt256}
      (_hr : RetOK Stack.trabs ret tail) (m : ByteArray) {off sh n4 lm kp : Nat}
      (_hoff : off < 2 ^ 64) (_hsh : sh < 4) (_hn4 : 1 ≤ n4) (_hlm : lm < 2 ^ 256)
      (_hlmL : ∀ k, k < 4 → lane lm k = 0 ∨ lane lm k = M64)
      (_hkp : kp + 128 * n4 ≤ KS + 800) (_hkp' : KS ≤ kp) (_hkp32 : kp % 32 = 0),
      ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
          if kp ≤ KS + 32 * x ∧ KS + 32 * x < kp + 128 * n4 then
            word m (KS + 32 * x) ^^^
              spread (trLane s.executionEnv.calldata off lm n4 ((KS + 32 * x - kp) / 32)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
        FrameExcept m m' [(kp, kp + 128 * n4)] ∧
        Call s Entry.trabs [wd kp, wd lm, wd n4, wd sh, wd off] ret tail m [] m' (Gas.trabs n4)) :
    ∃ m', (∀ tr : ByteArray, tr.size = 64 → k < 5 → 136 * k ≤ 66 + mlenOf s.executionEnv.calldata →
        ∀ x, x < 25 → word m' (KS + 32 * x) =
          if x < 17 then word m (KS + 32 * x) ^^^
            spread (le64 (Fips202.pad 136 0x1F
              (tr ++ (ByteArray.mk #[0, 0] ++ msgOf s.executionEnv.calldata))) (136 * k + 8 * x)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
      (66 + mlenOf s.executionEnv.calldata < 136 * k → 136 * k ≤ 66 + mlenOf s.executionEnv.calldata + 136 →
        ∀ x, x < 8 → word m' (MU + 32 * x) =
          cpl x (compress (word m (KS + 32 * x) / 2 ^ sh &&& spread M64))) ∧
      (66 + mlenOf s.executionEnv.calldata < 136 * k →
        ∀ x, x < 25 → word m' (KS + 32 * x) = word m (KS + 32 * x)) ∧
      ((k = 5 ∧ 136 * k ≤ 66 + mlenOf s.executionEnv.calldata) ∨
        66 + mlenOf s.executionEnv.calldata + 136 < 136 * k → m' = m) ∧
      FrameExcept m m' [(KS, KS + 800), (MU, MU + 256)] ∧
      Call s Entry.mub [wd (136 * k), wd sh] ret tail m [] m' Gas.mub := by
  have hcd' : 5261 ≤ s.executionEnv.calldata.size := hcd
  have hP : 66 + mlenOf s.executionEnv.calldata = s.executionEnv.calldata.size - 5195 := by
    have h : mlenOf s.executionEnv.calldata = s.executionEnv.calldata.size - 5261 := rfl
    rw [h]; omega
  clear hcd
  simp only [hP, KS, MU, Nat.zero_add]
  simp only [call_iff, Entry.mub, Gas.mub]
  by_cases hKP : 136 * k ≤ s.executionEnv.calldata.size - 5195
  · by_cases hk5' : k = 5
    · -- `k = 5`, `680 ≤ P`: nothing
      subst hk5'
      have r := mub_z hs hr m (sh := sh) hcd' hKP
      refine ⟨m, fun tr _ hk _ => absurd hk (by omega), fun h => absurd h (by omega),
        fun _ _ _ => rfl, fun _ => rfl, FrameExcept.refl _ _, (r.mono (by norm_num)).of_eq rfl rfl⟩
    · -- `trabs`
      have r0 := mub_t hs hr m (K := 136 * k) (sh := sh) (by omega) hcd' hKP
      obtain ⟨m9, h9post, h9frame, h9call⟩ := htrabs hs
        (hr.callee (B' := Stack.trabs) (ret' := 13839)
          (extra := [wd (s.executionEnv.calldata.size - 5195), wd (136 * k), wd sh, wd ret])
          (by simp only [Stack.mub, Stack.trabs, Stack.spr, Stack.cext, Stack.leaf, Nat.max_self,
            List.length_cons, List.length_nil]; omega)
          (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
        m (off := 5195 + 136 * k) (sh := sh) (n4 := 5)
        (lm := 115792089237316195417293883273301227089434195242432897623355228563449095127040) (kp := 0)
        (by omega) hsh (by norm_num) (by norm_num) mub0_lmL (by simp [KS]) (by simp [KS]) (by norm_num)
      have t9 := call_iff.mp h9call
      have h9 : ∀ y, y < 25 → word m9 (32 * y) = if y < 20 then
          word m (32 * y) ^^^ spread (trLane s.executionEnv.calldata (5195 + 136 * k)
            115792089237316195417293883273301227089434195242432897623355228563449095127040 5 y) * 2 ^ sh
          else word m (32 * y) := by
        intro y hy
        have h := h9post y hy
        simp only [KS, Nat.zero_add] at h
        rw [h]
        by_cases hy' : y < 20
        · rw [if_pos (by omega), if_pos hy', show (32 * y - 0) / 32 = y by omega]
        · rw [if_neg (by omega), if_neg hy']
      have f9 : FrameExcept m m9 [(0, 800), (89600, 89600 + 256)] := by
        refine h9frame.mono ?_
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact ⟨(0, 800), by simp, by simp only; omega, by simp only; omega⟩
      by_cases hfull : 136 * k + 136 ≤ s.executionEnv.calldata.size - 5195
      · -- a full block
        have r1 := mub_tf hs hr m9 (K := 136 * k) (sh := sh) (by omega) hcd' hfull
        refine ⟨m9, fun tr htr _ _ x hx => ?_, fun h => absurd h (by omega),
          fun h => absurd h (by omega), fun h => absurd h (by omega), f9, ?_⟩
        · exact mub_value_full htr hcd' (by omega) (by omega) hfull h9 hx
        · exact (((r0.trans t9).trans r1).mono (by simp only [Gas.trabs]; norm_num)).of_eq rfl rfl
      · -- the last block: padding
        have r1 := mub_tp hs hr m9 (K := 136 * k) (sh := sh) (by omega) hcd' hKP (by omega)
        have c1 := call_iff.mp (spr_call_any hs (hr.callee (B' := Stack.spr) (ret' := 13873)
          (extra := [wd (s.executionEnv.calldata.size - 5195 - 136 * k),
            wd (s.executionEnv.calldata.size - 5195), wd (136 * k), wd sh, wd ret])
          (by simp only [Stack.mub, Stack.trabs, Stack.spr, Stack.cext, Stack.leaf, Nat.max_self,
            List.length_cons, List.length_nil]; omega)
          (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) m9
          (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 5195 - 136 * k) * 8)))
        have r2 := mub_tp2 hs hr m9 (r := sprNet (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 5195 - 136 * k) * 8)))
          (q := s.executionEnv.calldata.size - 5195 - 136 * k) (p := s.executionEnv.calldata.size - 5195)
          (K := 136 * k) hsh (by omega)
        have htot := (((r0.trans t9).trans r1).trans c1).trans r2
        refine ⟨_, ?_, fun h => absurd h (by omega), fun h => absurd h (by omega),
          fun h => absurd h (by omega), ?_,
          (htot.mono (by simp only [Gas.trabs, Gas.spr]; norm_num)).of_eq rfl rfl⟩
        · intro tr htr _ _ x hx
          exact mub_value_last hsh htr hcd' (by omega) (by omega) hKP (by omega) h9 rfl rfl hx
        · refine ((f9.trans (FrameExcept.mstore _ _ _)).trans (FrameExcept.mstore _ _ _)).mono ?_
          intro r hr'
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr'
          rcases hr' with rfl | rfl | rfl | rfl
          · exact ⟨(0, 800), by simp, by simp only; omega, by simp only; omega⟩
          · exact ⟨(89600, 89600 + 256), by simp, by simp only; omega, by simp only; omega⟩
          · exact ⟨(0, 800), by simp, by simp only; omega, by simp only; omega⟩
          · exact ⟨(0, 800), by simp, by simp only; omega, by simp only; omega⟩
  · by_cases hle : 136 * k ≤ s.executionEnv.calldata.size - 5195 + 136
    · -- `P < K ≤ P + 136`: extract μ
      have r0 := mub_cx hs hr m (K := 136 * k) (sh := sh) (by omega) hcd' (by omega) hle
      obtain ⟨mc, hcpost, hcframe, hccall⟩ := cext_call_aux hs
        (hr.callee (B' := Stack.cext) (ret' := 13775)
          (extra := [wd (s.executionEnv.calldata.size - 5195), wd (136 * k), wd sh, wd ret])
          (by simp only [Stack.mub, Stack.trabs, Stack.spr, Stack.cext, Stack.leaf, Nat.max_self,
            List.length_cons, List.length_nil]; omega)
          (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
        m (dst := 89600) (sh := sh) (n := 8) hsh (by norm_num) (by norm_num) (by simp [KS])
        (by simp [TOP])
      have t1 := call_iff.mp hccall
      have r1 := mub_cx2 hs hr mc (p := s.executionEnv.calldata.size - 5195) (K := 136 * k) (sh := sh)
      refine ⟨mc, fun _ _ _ h => absurd h hKP, fun _ _ x hx => ?_,
        fun _ x _ => FrameExcept.word hcframe (by simp only [avoids_cons, avoids_nil, and_true]; omega),
        fun h => absurd h (by omega), ?_, ?_⟩
      · have h := hcpost x hx
        simp only [KS, Nat.zero_add] at h
        exact h
      · refine hcframe.mono ?_
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact ⟨(89600, 89600 + 256), by simp, by simp only; omega, by simp only; omega⟩
      · exact (((r0.trans t1).trans r1).mono (by simp only [Gas.cext]; norm_num)).of_eq rfl rfl
    · -- `P + 136 < K`: nothing
      have r := mub_out hs hr m (K := 136 * k) (sh := sh) (by omega) hcd' (by omega)
      refine ⟨m, fun _ _ _ h => absurd h hKP, fun _ h => absurd h hle,
        fun _ _ _ => rfl, fun _ => rfl, FrameExcept.refl _ _, (r.mono (by norm_num)).of_eq rfl rfl⟩

end MlDsaOpt65.Proofs.WP4
