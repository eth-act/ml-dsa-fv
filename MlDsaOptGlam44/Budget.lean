set_option warningAsError true
/-!
# Gas budgets of the Glamsterdam ML-DSA-44 bytecode

The budgets of `MlDsaOpt44/Budget.lean` for `MlDsaOpt/44/glam/opt.hex`
(Amsterdam gas: Osaka plus 3 per DUPN / SWAPN / EXCHANGE). Unchanged
subroutines keep their v4 cost; the changed ones (`kf4`, `kf1`, `blk`, `ntt`,
`intt`, `csum`, `dz`) were measured with `opt_evm.run(..., fork="glamsterdam")`
and are re-checked by their block lemmas. The squeeze path inside `fixSq`
(two 800-byte `MCOPY`s and glue, 282, then `kf4` and `blk`) follows them.

v4's notes:

Every budget is the exact worst-case cost of its contract: from the entry
`JUMPDEST` up to and including the returning `JUMP` (segments: from their
first instruction up to, not including, the instruction at their end pc).
Memory never grows after the entry store, so costs are static opcode sums.

Constant-cost subroutines were measured with `scripts/proofgen_gas.py`
(Python EVM, `scripts/opt_evm.py`) and are re-checked by the block lemmas:
`opt44_reach` fails unless the stated cost is the exact static sum of the
path. Data-dependent ones (`fix`, `gfix`, `sib`, `dhint`, `mub0`) are the
longest static paths (`scripts/proofgen_gas.py --analyse`), with loop trip
counts bounded as documented below.
-/

namespace MlDsaOptGlam44.Proofs.Gas

/-! ## Constant-cost subroutines -/

def kf4 : Nat := 33562
def kf1 : Nat := 25927
def blk : Nat := 7278
def blkh : Nat := 4174
def blkt : Nat := 3159
def ntt : Nat := 82378
/-- The inverse NTT with UseHint fused into its last pass. -/
def intt : Nat := 145475
def pass3f4 : Nat := 59037
def tbuild : Nat := 28511
def csum : Nat := 59504
def pack : Nat := 11107
def dz : Nat := 39578
def spr : Nat := 120
def ginit : Nat := 754
def absorb17 : Nat := 1160
def kmove : Nat := 1654
/-- `trabs` with `n4` groups of four lanes. -/
def trabs (n4 : Nat) : Nat := 65 + 529 * n4
/-- `cext` extracting `n` lanes. -/
def cext (n : Nat) : Nat := 19 + 205 * n
/-- `lmerge` over `11 n` words. -/
def lmerge (n : Nat) : Nat := 21 + 683 * n

/-! ## Data-dependent subroutines (worst cases) -/

/-- `mub0`: the longer of its two exits (padded single block, or the
continuation). -/
def mub0 : Nat := 3466

/-- `mub` (long-message schedule): the longest of its paths (absorb and pad:
glue, `trabs 5`, `spr`). -/
def mub : Nat := 3090

/-- `pass3f4b`, the long-message schedule's fused pass (static). -/
def pass3f4b : Nat := 59042

/-- `fix` without a sixth squeeze: entry 40, the first-flag scan (at most 32
visits of 55), its exit 4, at most 42 group-loop visits of at most 580, the
exhaustion check with the continue path (65) and the exit (at most 53). -/
def fixNo : Nat := 40 + 32 * 55 + 4 + 42 * 580 + 65 + 53

/-- `fix` performing the sixth squeeze: as `fixNo` with the squeeze path
(two 800-byte `MCOPY`s and glue 282, `kf4`, `blk`) instead of the continue path. -/
def fixSq : Nat := 40 + 32 * 55 + 4 + 42 * 580 + (282 + kf4 + blk) + 53

/-- `gfix` own instructions with all four slots taking the `fix` call path. -/
def gfix0 : Nat := 806

/-- `gfix` with at most `n` active slots: one `blkt` before the first fix-up,
and at most one `fix` call squeezes the sixth block (`HAVE6` is set by the
first squeeze). -/
def gfix (n : Nat) : Nat := gfix0 + blkt + n * fixNo + (fixSq - fixNo)

/-- `group`: glue 404, `ginit`, five `kf4`, four `blk` and one `blkh`, `gfix 4`. -/
def group : Nat := 404 + ginit + 5 * kf4 + 4 * blk + blkh + gfix 4

/-- `sib` (`Fn/Ball/V4Loop.lean`): entry 22; the 264 stream bytes as rejected
(each lane: byte 0 with the loop head 69, bytes 1 … 6 40 each, byte 7 with the
lane epilogue 62, so 33 × 371); 353 more per accepted byte (39); the failure
exit 72; the second block's squeeze 196 + `kf4` + `cext 17`. -/
def sib : Nat := 22 + 33 * 371 + 39 * 353 + 72 + 196 + kf4 + cext 17

/-- `dhint`: fixed part 312 plus at most 85 loop visits of at most 161 each
(80 hint indices, the trailing-zero scan, and the 5 loop exits). -/
def dhint : Nat := 312 + 85 * 161

end MlDsaOptGlam44.Proofs.Gas
