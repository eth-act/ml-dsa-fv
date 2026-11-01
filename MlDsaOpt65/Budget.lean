/-!
# Gas budgets of the subroutine contracts (ML-DSA-65)

Same conventions as `MlDsaOpt44/Budget.lean`: every budget is the exact
worst-case cost of its contract, from the entry `JUMPDEST` up to and including
the returning `JUMP`; memory never grows after the entry store.

Numbers: `python3 scripts/proofgen_gas_param.py 65 --analyse` (constant-cost
subroutines measured in the Python EVM, data-dependent ones as longest static
paths with the loop trip counts documented below). Kernels shared with
ML-DSA-44 (`kf4`, `kf1`, `blk`, `ntt`, `intt`, `pass3`, `tbuild`, `dz`, `spr`,
`absorb17`, `trabs`, `cext`, `fix`, `gfix`) have the ML-DSA-44 budgets.
-/

namespace MlDsaOpt65.Proofs.Gas

/-! ## Constant-cost subroutines -/

def kf4 : Nat := 40238
def kf1 : Nat := 35880
def blk : Nat := 7836
def ntt : Nat := 99705
def intt : Nat := 119593
def pass3 : Nat := 17780
def tbuild : Nat := 28511
def csum : Nat := 81381
def usehint : Nat := 56857
def dz : Nat := 46156
def spr : Nat := 120
def ginit : Nat := 792
def absorb17 : Nat := 1160
/-- `pack` with `nr` rows (rows `≥ nr` take a cheaper skip branch); ML-DSA-65
calls it with 4 and 2 rows. -/
def pack (nr : Nat) : Nat := if nr ≤ 2 then 8227 else 9251
/-- `trabs` with `n4` groups of four lanes: 826 per group (one of them masked). -/
def trabs (n4 : Nat) : Nat := 55 + 826 * n4
/-- `cext` extracting `n` lanes. -/
def cext (n : Nat) : Nat := 19 + 205 * n

/-! ## Data-dependent subroutines (worst cases) -/

/-- `mu0`: the absorbing path (`|M| ≤ 69`); the skipping path is cheaper. -/
def mu0 : Nat := 4359

/-- `fix` without a sixth squeeze (as ML-DSA-44): first-flag scan 1810, at most
44 group-loop visits of at most 784, continue path 59, exit 51. -/
def fixNo : Nat := 1810 + 44 * 784 + 59 + 51

/-- `fix` performing the sixth squeeze (48350 instead of the continue path). -/
def fixSq : Nat := 1810 + 44 * 784 + 48350 + 51

/-- `gfix` own instructions with all four slots taking the `fix` call path. -/
def gfix0 : Nat := 630

/-- `gfix` with at most `n` active slots (at most one sixth squeeze). -/
def gfix (n : Nat) : Nat := gfix0 + n * fixNo + (fixSq - fixNo)

/-- `group`: glue 470, `ginit`, five `kf4` + `blk`, `gfix 4`, `pass3`. -/
def group : Nat := 470 + ginit + 5 * (kf4 + blk) + gfix 4 + pass3

/-- `sib`: entry 13; 265 loop visits (positions `8 … 271` and the exit visit),
at most `τ = 49` accepted ones (454 each), the others rejected (125 each). -/
def sib : Nat := 13 + 216 * 125 + 49 * 454

/-- `dhint`: fixed part 458 plus at most `ω + k + 1 = 62` loop visits of at
most 161 each (55 hint indices, 6 row exits, the trailing scan exit). -/
def dhint : Nat := 458 + 62 * 161

end MlDsaOpt65.Proofs.Gas
