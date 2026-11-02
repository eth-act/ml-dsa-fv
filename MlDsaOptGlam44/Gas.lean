import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/-!
# The public gas schedule (Glamsterdam ML-DSA-44)

A function of the calldata length only, composed from the segment budgets of
`Main/Base.lean` as in v4 (`MlDsaOpt44/Gas.lean`), with the long-message switch:
for `|M| < 342` the packed schedule's segments (`pSw` … `pSib`), from there on
`pAlt`.

**Provisional:** `pAlt` is an upper bound stated before the long-message path
is proved (open item `seg_alt`): twice the packed schedule's budget for the
same stretch. That path makes at most 20 `kf4`, 16 `blk`, 4 `blkh` and 4
`gfix` calls (the packed stretch's budget has 13, 11, 2 and 3), and its μ part
is bounded by `pMu`. It will be replaced by the path's exact static budget.
-/

namespace MlDsaOptGlam44.Proofs.Gas

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Gas

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- `2436 … 6030` on the packed schedule (`|M| < 342`). -/
def pPacked (mlen : Nat) : Nat := pSw + pG2 + pWin + pJoin + pZd + pMu mlen + pSib

/-- `2436 … 6030` on the long-message schedule (`|M| ≥ 342`); provisional, see
the module doc. -/
def pAlt (mlen : Nat) : Nat := 2 * pPacked mlen

/-- **The public gas schedule.** -/
def schedule (size : Nat) : Nat :=
  if size < 3732 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZ + pTbl + pNtt + pRho + pG0 + pG1 +
      (if size - 3732 < 342 then pPacked (size - 3732) else pAlt (size - 3732)) + pCt + pW + pFin

end MlDsaOptGlam44.Proofs.Gas
