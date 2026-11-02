set_option warningAsError true
/-!
# Gas budgets of the Glamsterdam ML-DSA-65 bytecode

The budgets of `MlDsaOpt65/Budget.lean` for `MlDsaOpt/65/glam/opt.hex`
(Amsterdam gas: Osaka plus 3 per DUPN / SWAPN / EXCHANGE). Unchanged
subroutines keep their v4 cost; the changed ones (`kf4`, `kf1`, `blk`, `ntt`,
`intt`, `csum`, `dz`, and the 42-call schedule's `pass3f7`, `pass3f8`, `kmove`,
`lmerge`) were measured with `opt_evm.run(..., fork="glamsterdam")` or as static
path sums (`blockCostEval`) and are re-checked by their block lemmas. The
squeeze path inside `fixSq` (two 800-byte `MCOPY`s and glue, 282, then `kf4` and
`blk`) follows them. v4 has no `pass3f7`, `kmove`, `lmerge`; its `pass3f4` is gone.

v4's notes:

Same conventions as `MlDsaOpt44/Budget.lean`: every budget is the exact
worst-case cost of its contract, from the entry `JUMPDEST` up to and including
the returning `JUMP`; memory never grows after the entry store. Constant-cost
subroutines measured in the Python EVM, data-dependent ones as longest static
paths. Kernels shared with ML-DSA-44 have the ML-DSA-44 budgets.
-/

namespace MlDsaOptGlam65.Proofs.Gas

/-! ## Constant-cost subroutines -/

def ginit : Nat := 792
def kf4 : Nat := 33562
def kf1 : Nat := 25927
def blk : Nat := 7278
def blkh : Nat := 4174
def blkt : Nat := 3159
def ntt : Nat := 82378
def tbuild : Nat := 28511
def dz : Nat := 39578
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

/-- `fix` performing the sixth squeeze: the squeeze path (two 800-byte `MCOPY`s and
glue 282, `kf4`, `blk`) instead of the continue path. -/
def fixSq : Nat := 40 + 32 * 55 + 4 + 42 * 580 + (282 + kf4 + blk) + 53

/-- `gfix` own instructions with all four slots taking the `fix` call path. -/
def gfix0 : Nat := 806

/-- `gfix` with at most `n` active slots: one `blkt`, at most one sixth squeeze. -/
def gfix (n : Nat) : Nat := gfix0 + blkt + n * fixNo + (fixSq - fixNo)

/-- `group`: glue 404, `ginit`, five `kf4`, four `blk` and one `blkh`, `gfix 4`. -/
def group : Nat := 404 + ginit + 5 * kf4 + 4 * blk + blkh + gfix 4

/-- The inverse NTT with UseHint fused into its last pass. -/
def intt : Nat := 137539
/-- The fused pass of row group 0 (13 + 128 × 577 + 16). -/
def pass3f7 : Nat := 73885
/-- The fused pass of row group 1 (13 + 128 × 303 + 16). -/
def pass3f8 : Nat := 38813
def csum : Nat := 69184
def kmove : Nat := 1654
/-- `lmerge` over `14 k` words. -/
def lmerge (k : Nat) : Nat := 21 + 863 * k

/-- `mub0`: the longer of its two exits. -/
def mub0 : Nat := 3466

/-- `sib` (`Fn/Ball/V4Loop.lean`): entry 13; the 264 stream bytes as rejected
(each lane: byte 0 with the loop head 66, bytes 1 … 6 40 each, byte 7 with the
lane epilogue 62, so 33 × 368); 353 more per accepted byte (49); the failure
exit 43. -/
def sib : Nat := 13 + 33 * 368 + 49 * 353 + 43

/-- `dhint`: fixed part 458 plus at most `ω + k + 1 = 62` loop visits of at
most 161 each (55 hint indices, 6 row exits, the trailing scan exit). -/
def dhint : Nat := 458 + 62 * 161

end MlDsaOptGlam65.Proofs.Gas
