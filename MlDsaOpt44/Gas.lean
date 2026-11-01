import MlDsaOpt44.Main.Base
/-!
# The public gas schedule

A function of the calldata length only, composed from the segment budgets of
`Main/Segments.lean` (themselves sums of subroutine budgets and static glue
costs). Data-dependent control flow is charged at its proved worst case:
RejNTTPoly fix-ups including the sixth squeeze in every group, SampleInBall's
byte loop, HintBitUnpack's loops; μ's block count depends on the message
length only.

`schedule (3732 + n)` is 2,931,924 for `n ≤ 69`, 3,033,147 for `70 ≤ n ≤
205`, and grows by 33,819 per 136 message bytes (`scripts/proofgen_gas.py
--schedule`). The measured adversarial worst case of `docs/opt.md` is
2,864,301 for `n = 0`; the difference is the conservative fix-up and
SampleInBall loop counts.
-/

namespace MlDsaOpt44.Proofs.Gas

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- **The public gas schedule.** -/
def schedule (size : Nat) : Nat :=
  if size < 3732 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZh + pTbl + pNtt + pRho + pG0 + pG1 + pG234 +
      pMu (size - 3732) + pSib + pCt + pW + pFin

end MlDsaOpt44.Proofs.Gas
