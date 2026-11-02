import MlDsaOpt65.Main.Base
set_option warningAsError true
/-!
# The public gas schedule (ML-DSA-65)

A function of the calldata length only, composed from the segment budgets of
`Main/Base.lean` (themselves sums of subroutine budgets and static glue
costs). Data-dependent control flow is charged at its proved worst case:
RejNTTPoly fix-ups including the sixth squeeze in every group, SampleInBall's
byte loop, HintBitUnpack's loops; μ's block count depends on the message
length only.

`schedule (5261 + n)` is constant for `n ≤ 613` and grows by 33,819 per 136
message bytes after that. The measured adversarial worst case of
`docs/opt.md` (v4) is 4,610,258 for `n = 0`.
-/

namespace MlDsaOpt65.Proofs.Gas

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- **The public gas schedule.** -/
def schedule (size : Nat) : Nat :=
  if size < 5261 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZ + pTbl + pNtt + pRho + pExp + pZd +
      pMu (size - 5261) + pSib + pCt + pW + pFin

end MlDsaOpt65.Proofs.Gas
