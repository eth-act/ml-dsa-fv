import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/-!
# The public gas schedule (Glamsterdam ML-DSA-44)

A function of the calldata length only, composed from the segment budgets of
`Main/Base.lean` as in v4 (`MlDsaOpt44/Gas.lean`), with the long-message switch:
for `|M| < 342` the packed schedule's segments (`pSw` … `pSib`), from there on
`pAlt`, the exact static budget of the long-message schedule (`Main/SegAlt.lean`).
-/

namespace MlDsaOptGlam44.Proofs.Gas

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Gas

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- `2436 … 6030` on the packed schedule (`|M| < 342`). -/
def pPacked (mlen : Nat) : Nat := pSw + pG2 + pWin + pJoin + pZd + pMu mlen + pSib

/-- `2436 … 5081` on the long-message schedule: the jump to `alt` (24), the two
`tr`-rider groups (`Main/Alt/GrpA.lean`, `GrpB.lean`), the μ group with its
`mulong` region (`GrpK.lean`) and `pass3f4b`; 2825 gas of glue. -/
def pAltX : Nat :=
  2825 + 3 * ginit + mub0 + 9 * trabs 5 + trabs 3 + 15 * kf4 + 12 * blk + 3 * blkh + cext 8 +
    2 * cext 17 + 5 * mub + 2 * gfix 3 + gfix 2 + pass3f4b

/-- `5183 … 6020` on the long-message schedule (`FLAG = 0`), the exact path:
`|M| ≤ 613`: the dispatch and the copy of `MU` to `FIN` (212). Otherwise the
dispatch (41), `hash_mu`'s setup without the `MCOPY` (637: `FLAG` test 23,
`cext` call 23, replication 522, block 5's call 37, loop head 32) with
`cext 25` and `absorb17`, one loop visit (`kf1 + absorb17 + 88`) per further
full block of `tr ‖ 0 ‖ 0 ‖ M` (`(|M| − 614) / 136` visits), and the exit
(check 23, padding 100, `kf1`, copy to `FIN` 102). -/
def pMuA (mlen : Nat) : Nat :=
  if mlen ≤ 613 then 212
  else 41 + 637 + cext 25 + absorb17 + (mlen - 614) / 136 * (kf1 + absorb17 + 88) + (kf1 + 225)

/-- `2436 … 6030` on the long-message schedule (`|M| ≥ 342`, `Main/SegAlt.lean`):
ExpandA, then the side buffers and hints, μ and SampleInBall with `FLAG = 0`. -/
def pAlt (mlen : Nat) : Nat := pAltX + pZd + pMuA mlen + pSib

/-- **The public gas schedule.** -/
def schedule (size : Nat) : Nat :=
  if size < 3732 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZ + pTbl + pNtt + pRho + pG0 + pG1 +
      (if size - 3732 < 342 then pPacked (size - 3732) else pAlt (size - 3732)) + pCt + pW + pFin

end MlDsaOptGlam44.Proofs.Gas
