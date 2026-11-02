import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
set_option warningAsError true
/-!
# The public gas schedule (Glamsterdam ML-DSA-65)

v4's schedule (`MlDsaOpt65/Gas.lean`) over this artifact's segment budgets
(`Main/Base.lean`, re-measured where the code changed): `pExp` is the 42-call
ExpandA schedule's exact static cost (`Main/SegExp.lean`), `pMu` glam's μ (one
squeeze in the SIMD slot, `hash_mu` from the state image).

v4's notes:

A function of the calldata length only, composed from the segment budgets of
`Main/Base.lean` (themselves sums of subroutine budgets and static glue
costs). Data-dependent control flow is charged at its proved worst case:
RejNTTPoly fix-ups including the sixth squeeze in every group, SampleInBall's
byte loop, HintBitUnpack's loops; μ's block count depends on the message
length only.

`schedule (5261 + n)` is constant for `n ≤ 613` and grows by 33,819 per 136
message bytes after that. The measured adversarial worst case of
`docs/opt.md` (v4) is 4,610,258 for `n = 0`.

Glam: `schedule (5261 + n)` is constant for `n ≤ 69`, steps by 32,952 at `n = 70`
(μ moves from `MU` to `hash_mu`) and grows by 27,175 (`kf1 + absorb17 + 88`) per
further 136 message bytes.
-/

namespace MlDsaOptGlam65.Proofs.Gas

open MlDsaOpt65.Proofs

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- **The public gas schedule.** -/
def schedule (size : Nat) : Nat :=
  if size < 5261 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZ + pTbl + pNtt + pRho + pExp + pZd +
      pMu (size - 5261) + pSib + pCt + pW + pFin

end MlDsaOptGlam65.Proofs.Gas
