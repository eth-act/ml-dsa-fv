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

`schedule (5261 + n)` is 5,199,370 for `n ≤ 69`, 5,300,593 for `70 ≤ n ≤
205`, and grows by 33,819 per 136 message bytes
(`python3 scripts/proofgen_gas_param.py 65 --schedule`). The measured
adversarial worst case of `docs/opt.md` is 5,073,355 for `n = 0`.
-/

namespace MlDsaOpt65.Proofs.Gas

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- **The public gas schedule.** -/
def schedule (size : Nat) : Nat :=
  if size < 5261 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZh + pTbl + pNtt + pRho +
      pG0 + pG1 + pG2 + pG3 + pG4 + pG5 + pG6 + pG7 + pG8 +
      pMu (size - 5261) + pSib + pCt + pW + pFin

example : schedule 5261 = 5199370 := by decide +kernel
example : schedule (5261 + 69) = 5199370 := by decide +kernel
example : schedule (5261 + 70) = 5300593 := by decide +kernel
example : schedule (5261 + 1000) = 5503507 := by decide +kernel

end MlDsaOpt65.Proofs.Gas
