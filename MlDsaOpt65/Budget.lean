/-!
# Gas budgets of the subroutine contracts (ML-DSA-65, v4)

Same conventions as `MlDsaOpt44/Budget.lean`: every budget is the exact
worst-case cost of its contract, from the entry `JUMPDEST` up to and including
the returning `JUMP`; memory never grows after the entry store. Constant-cost
subroutines measured in the Python EVM, data-dependent ones as longest static
paths. Kernels shared with ML-DSA-44 have the ML-DSA-44 budgets.
-/

namespace MlDsaOpt65.Proofs.Gas

/-! ## Constant-cost subroutines -/

def ginit : Nat := 792
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

/-- The inverse NTT with UseHint fused into its last pass. -/
def intt : Nat := 147497
def pass3f4 : Nat := 55187
def pass3f8 : Nat := 88999
def csum : Nat := 76176

/-- `mub0`: the longer of its two exits. -/
def mub0 : Nat := 3466
/-- `mub`: the longest of its paths (absorb a block, pad it, or extract μ). -/
def mub : Nat := 3090

/-- `sib` (`Fn/Ball/V4Loop.lean`): entry 13; the 264 stream bytes as rejected
(each lane: byte 0 with the loop head 66, bytes 1 … 6 40 each, byte 7 with the
lane epilogue 62, so 33 × 368); 353 more per accepted byte (49); the failure
exit 43. -/
def sib : Nat := 13 + 33 * 368 + 49 * 353 + 43

/-- `dhint`: fixed part 458 plus at most `ω + k + 1 = 62` loop visits of at
most 161 each (55 hint indices, 6 row exits, the trailing scan exit). -/
def dhint : Nat := 458 + 62 * 161

end MlDsaOpt65.Proofs.Gas
