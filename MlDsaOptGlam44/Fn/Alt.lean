import MlDsaOptGlam44.Fn.Sponge
import MlDsaOptGlam44.Fn.Group
import MlDsaOptGlam44.Fn.Alt.Mub
import MlDsaOptGlam44.Fn.Alt.Pass3f4b
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
set_option warningAsError true
/-!
# Subroutines of the long-message schedule only: `mub`, `pass3f4b`

`mub [136 k, sh, ret]` (after the `k`-th `kf4` of the μ group, `1 ≤ k ≤ 5`,
`P = 66 + |M|`): for `k < 5` and `136 k ≤ P` slot `sh` absorbs block `k` of
μ's padded input (padding it when it is the last); for `P < 136 k ≤ P + 136`
μ's lanes 0 … 7 are extracted from slot `sh` to `MU`; otherwise nothing.
The same code as ML-DSA-65's (proved there, `MlDsaOpt65/Fn/Sponge/Mub*.lean`; ported
to `Fn/Alt/Mub*.lean`).

`pass3f4b [ret]`: the long-message schedule's fused pass: `ACC[t] := altWord t`
(columns 0, 1 aligned from `CW`, `HP`; rows 0 … 2 of columns 2, 3 in lanes
0 … 2 of `SB`, `SB + 8192`; the Kronecker pair `(A[3][3], A[3][2])` in lanes 2, 3
of `ABUF`). Proof in `Fn/Alt/Pass3f4b.lean`.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- μ's padded input `tr ‖ 0 ‖ 0 ‖ M ‖ pad` for a given `tr`. -/
def muPaddedG (tr cd : ByteArray) : ByteArray :=
  Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))

/-- **mub**. -/
theorem mub_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (m : ByteArray) {sh k : Nat} (hsh : sh < 4) (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ tr : ByteArray, tr.size = 64 → k < 5 → 136 * k ≤ 66 + mlenOf s.executionEnv.calldata →
        ∀ x, x < 25 → word m' (KS + 32 * x) =
          if x < 17 then word m (KS + 32 * x) ^^^
            spread (le64 (muPaddedG tr s.executionEnv.calldata) (136 * k + 8 * x)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
      (66 + mlenOf s.executionEnv.calldata < 136 * k → 136 * k ≤ 66 + mlenOf s.executionEnv.calldata + 136 →
        ∀ x, x < 8 → word m' (MU + 32 * x) =
          cpl x (compress (word m (KS + 32 * x) / 2 ^ sh &&& spread M64))) ∧
      (66 + mlenOf s.executionEnv.calldata < 136 * k →
        ∀ x, x < 25 → word m' (KS + 32 * x) = word m (KS + 32 * x)) ∧
      ((k = 5 ∧ 136 * k ≤ 66 + mlenOf s.executionEnv.calldata) ∨
        66 + mlenOf s.executionEnv.calldata + 136 < 136 * k → m' = m) ∧
      FrameExcept m m' [(KS, KS + 800), (MU, MU + 256)] ∧
      Call s Entry.mub [wd (136 * k), wd sh] ret tail m [] m' Gas.mub :=
  WP4.mub_call_aux hs hr m hsh hk1 hk5 hcd trabs_call

/-- The word `pass3f4b` stores at `ACC[t]`. -/
def altWord (m : ByteArray) (t : Nat) : Nat :=
  let z := word m (ZH + 32 * t)
  (word m (CW + 32 * t) * lane z 0 + word m (HP + 32 * t) * lane z 1 +
    (word m (SB + 32 * t) &&& (2 ^ 192 - 1)) * lane z 2 +
    (word m (SB + 8192 + 32 * t) &&& (2 ^ 192 - 1)) * lane z 3 +
    ((word m (ABUF + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
      (M64 * 2 ^ 192))) % 2 ^ 256

/-- **pass3f4b**: `[ret]`; `ACC[t] := altWord t`. -/
theorem pass3f4b_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4b ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) = altWord m t) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f4b [] ret tail m [] m' Gas.pass3f4b :=
  pass3f4b_call_aux hs hr m

end MlDsaOptGlam44.Proofs
