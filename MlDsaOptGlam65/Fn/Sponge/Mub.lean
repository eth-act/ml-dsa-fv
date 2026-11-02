import MlDsaOpt65.Fn.Sponge.MubMath
import MlDsaOptGlam65.Fn.Sponge.Mub0
import MlDsaOptGlam65.Fn.Sponge.Spr
import MlDsaOptGlam65.Fn.Sponge.Cext
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Sponge/Mub.lean` by `scripts/proofgen_port.py --glam 65`; the statement is v4's, the proof an open item. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError false  -- glam: open items (`sorry`)
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

namespace MlDsaOptGlam65.Proofs.WP4

open MlDsaOpt65.Proofs MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs.WP4
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra
open MlDsa44

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
  sorry  -- glam: open item (package 4: glam 65's `mub` is changed, `K < 136` instead of `K < 680`)

end MlDsaOptGlam65.Proofs.WP4
