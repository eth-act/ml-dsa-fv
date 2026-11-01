import MlDsaOpt65.Fn.Mu0.Defs
import MlDsaOpt65.Fn.Mu0.Mu0
/-!
# `mu0`: μ's single padded block into a SIMD slot (ML-DSA-65)

The code is the ML-DSA-44 `mu0` with this artifact's `HDR` (`|M| = CALLDATASIZE − HDR`,
the message read from `HDR − 2`) and `TRL` (`PUSH3 0x015d00 …` instead of `PUSH2 0xfd00 …`:
the instruction count is unchanged, the pcs shift). Call site: `mu0 [3]` in group 8 (slot 3
is the μ slot, `MlDsaOpt/65/layout.txt`). `muBlock` is defined in `Fn/Mu0/Defs.lean`. The
proof is the port of `MlDsaOpt44/Fn/Sponge/{Mu0,MuBlocks,MuFinal,MuVal,MuMath}.lean`
(`WP4.mu0_call_aux`) to `Fn/Mu0/` by
`scripts/proofgen_port.py 65 --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195
--sub 64768=89344 … --sub 64992=89568 --sub 12633=13592 … --sub 12905=13871
--path Fn/Sponge/=Fn/Mu0/` (full command in each file's header; `-- port:` hand edits:
65 `spr`/`trabs` imports, `muBlock` import, unfolding `HDR`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

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
      Call s Entry.mu0 [wd sh] ret tail m [] m' Gas.mu0 :=
  WP4.mu0_call_aux hs hr m hsh hcd

end MlDsaOpt65.Proofs
