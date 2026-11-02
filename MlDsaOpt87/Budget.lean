/-!
# Gas budgets of the subroutine contracts (ML-DSA-87, v4)

Same conventions as `MlDsaOpt44/Budget.lean`: every budget is the exact
worst-case cost of its contract, from the entry `JUMPDEST` up to and including
the returning `JUMP`; memory never grows after the entry store. Constant-cost
subroutines measured in the Python EVM, data-dependent ones as longest static
paths. Kernels shared with ML-DSA-44 have the ML-DSA-44 budgets.
`Gas.sib` is a placeholder until the `sib` proof fixes its path count.
-/

namespace MlDsaOpt87.Proofs.Gas

/-! ## Constant-cost subroutines -/

def ginit : Nat := 677
def kf4 : Nat := 40238
def kf1 : Nat := 32571
def blk : Nat := 7842
def blkh : Nat := 4592
def blkt : Nat := 3512
def ntt : Nat := 92404
def tbuild : Nat := 28511
def dz : Nat := 43516
def spr : Nat := 120
def absorb17 : Nat := 1160
/-- `pack` with `nr` rows (rows `≥ nr` take a cheaper skip branch). -/
def pack (nr : Nat) : Nat := if nr ≤ 2 then 8227 else 9251
/-- `trabs` with `n4` groups of four lanes. -/
def trabs (n4 : Nat) : Nat := 65 + 529 * n4
/-- `cext` extracting `n` lanes. -/
def cext (n : Nat) : Nat := 19 + 205 * n

/-! ## Data-dependent subroutines (worst cases) -/

/-- `fix` without a sixth squeeze (as ML-DSA-44). -/
def fixNo : Nat := 40 + 32 * 55 + 4 + 42 * 580 + 65 + 53

/-- `fix` performing the sixth squeeze (as ML-DSA-44). -/
def fixSq : Nat := 40 + 32 * 55 + 4 + 42 * 580 + 48362 + 53

/-- `gfix` own instructions with all four slots taking the `fix` call path. -/
def gfix0 : Nat := 806

/-- `gfix` with at most `n` active slots: one `blkt`, at most one sixth squeeze. -/
def gfix (n : Nat) : Nat := gfix0 + blkt + n * fixNo + (fixSq - fixNo)

/-- `group`: glue 404, `ginit`, five `kf4`, four `blk` and one `blkh`, `gfix 4`. -/
def group : Nat := 404 + ginit + 5 * kf4 + 4 * blk + blkh + gfix 4

def intt : Nat := 116521
def usehint : Nat := 41497
def pass3f4 : Nat := 55187
def pass3f6 : Nat := 32147
def pass3f10 : Nat := 46232
def pass3f14 : Nat := 60061
def csum : Nat := 88848

/-- `sib`: placeholder (v3 count). -/
def sib : Nat := (853 + kf1) + 205 * 158 + 60 * 487 + (135 + kf1)

/-- `dhint`: fixed part 604 plus at most `ω + k + 1 = 84` loop visits of at
most 161 each (75 hint indices, 8 row exits, the trailing scan exit). -/
def dhint : Nat := 604 + 84 * 161

end MlDsaOpt87.Proofs.Gas
