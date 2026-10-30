import MlDsa44.Proofs.Fn.Row
import MlDsa44.Proofs.Fn.Hint
import MlDsa44.Proofs.Fn.Zetas
/-!
# The public gas schedule

Composed from the per-subroutine budgets `Gas.*` defined next to each call
contract in `MlDsa44.Proofs.Fn.*`. The schedule depends only on the calldata
length: the verification path's control flow is data-independent except for
bounded per-coefficient branches, which the budgets bound by their maxima.
-/

namespace MlDsa44.Proofs.Gas

/-- EVM memory cost of `words` active words (Yellow Paper `C_mem`). -/
def memCost (words : Nat) : Nat := 3 * words + words * words / 512

/-- Everything on the valid-length path except the message-dependent parts. -/
def mainFixed : Nat :=
  5000 + initZetas + shake 136 1312 1 + decodeZ + decodeHint + shake 136 32 2 +
    sampleInBall + ntt + 4 * (computeRow + encodeRow) + shake 136 832 1

/-- Calldata shorter than `pk ‖ σ`: return the zero word. -/
def short : Nat := 300

/-- **The public gas schedule**, a function of the calldata length only:
fixed verification work, the `μ` absorption of `tr ‖ 0 ‖ 0 ‖ M`, the
message copy, and memory expansion up to `MSGIN + |M| + 288`. -/
def schedule (size : Nat) : Nat :=
  if size < 3732 then short else
    let n := size - 3732
    mainFixed + shake 136 (66 + n) 1 + 3 * ((n + 31) / 32) +
      memCost ((MSGIN + n + 288 + 31) / 32)

end MlDsa44.Proofs.Gas
