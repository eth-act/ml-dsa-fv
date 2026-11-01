import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/-!
# `mu0`: μ's single padded block into a SIMD slot (ML-DSA-65)

Open contract (statement only). The code is the ML-DSA-44 `mu0` with this artifact's
`HDR` (`|M| = CALLDATASIZE − HDR`, the message read from `HDR − 2`) and `TRL`
(`PUSH3 0x015d00 …` instead of `PUSH2 0xfd00 …`: the instruction count is unchanged, the
pcs shift). Call site: `mu0 [3]` in group 8 (slot 3 is the μ slot,
`MlDsaOpt/65/layout.txt`). The proof is the port of `MlDsaOpt44/Fn/Sponge/{Mu0,MuBlocks,
MuFinal,MuVal,MuMath}.lean` (`WP4.mu0_call_aux`) by `scripts/proofgen_port.py 65`
(`spr`, `trabs` calls through the 65 contracts of `Fn/Sponge.lean`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- μ's single padded SHAKE256 block for `|M| ≤ 69`: `tr ‖ 0 ‖ 0 ‖ M ‖ pad`. -/
def muBlock (tr : ByteArray) (cd : ByteArray) : ByteArray :=
  MlDsa44.Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))

/-- **mu0**: `[sh, ret]`; for `|M| ≤ 69` slot `sh` absorbs μ's single block (with `tr`
read from `TRL`), otherwise nothing. -/
theorem mu0_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (m : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (mlenOf s.executionEnv.calldata ≤ 69 → ∀ tr : ByteArray, tr.size = 64 →
        (∀ x, x < 8 → word m (TRL + 32 * x) = le64 tr (8 * x)) →
        ∀ x, x < 25 → word m' (KS + 32 * x) =
          if x < 17 then word m (KS + 32 * x) ^^^
            spread (le64 (muBlock tr s.executionEnv.calldata) (8 * x)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
      (69 < mlenOf s.executionEnv.calldata → m' = m) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.mu0 [wd sh] ret tail m [] m' Gas.mu0 := by
  sorry

end MlDsaOpt65.Proofs
