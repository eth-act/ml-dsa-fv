import MlDsaOptGlam87.Main.Base
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
set_option warningAsError true
/-!
# The public gas schedule (Glamsterdam ML-DSA-87)

v4's schedule (`MlDsaOpt87/Gas.lean`) over this artifact's segment budgets
(`Main/Base.lean`, re-measured where the code changed).

v4's notes:

A function of the calldata length only, composed from the segment budgets of
`Main/Base.lean` (themselves sums of subroutine budgets and static glue
costs). Data-dependent control flow is charged at its proved worst case:
RejNTTPoly fix-ups including the sixth squeeze in every group, SampleInBall's
byte loop (with the second `H(c̃)` block), HintBitUnpack's loops; μ's block
count depends on the message length only (always the `kf1` sponge).

`schedule (7219 + n) = 7,443,165 + ⌊(66 + n) / 136⌋ · 33,819` (`schedule_msg`):
7,443,165 for `n ≤ 69`, 7,476,984 for `70 ≤ n ≤ 205`, and 33,819 more per
further 136 message bytes. The ExpandA segment is charged at its longest
static path. The measured adversarial worst case of `docs/opt.md` (v4) is
7,261,604 for `n = 0`.
-/

namespace MlDsaOptGlam87.Proofs.Gas

open MlDsaOpt87.Proofs

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- **The public gas schedule.** The fixed segments (in program order, the μ
segment last) plus μ's message-dependent part. -/
def schedule (size : Nat) : Nat :=
  if size < 7219 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZ + pTbl + pNtt + pRho + pExp + pZd +
      pSib + pCt + pW + pFin + pMu (size - 7219)

-- glam: v4's closed form `schedule_msg` is restated once `pExp`, `pW` are final

end MlDsaOptGlam87.Proofs.Gas
