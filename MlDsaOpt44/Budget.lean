/-!
# Gas budgets of the subroutine contracts and main-flow segments

Every budget is the exact worst-case cost of its contract: from the entry
`JUMPDEST` up to and including the returning `JUMP` (segments: from their
first instruction up to, not including, the instruction at their end pc).
Memory never grows after the entry store, so costs are static opcode sums.

Constant-cost subroutines were measured with `scripts/proofgen_gas.py`
(Python EVM, `scripts/opt_evm.py`) and are re-checked by the block lemmas:
`opt44_reach` fails unless the stated cost is the exact static sum of the
path. Data-dependent ones (`fix`, `gfix`, `sib`, `dhint`, `mu0`) are the
longest static paths (`scripts/proofgen_gas.py --analyse`), with loop trip
counts bounded as documented below.
-/

namespace MlDsaOpt44.Proofs.Gas

/-! ## Constant-cost subroutines -/

def kf4 : Nat := 40238
def kf1 : Nat := 35880
def blk : Nat := 7836
def ntt : Nat := 99705
def intt : Nat := 119593
def pass3 : Nat := 17780
def pass3m : Nat := 19318
def pass3k4 : Nat := 25613
def tbuild : Nat := 28511
def csum : Nat := 69861
def usehint : Nat := 64793
def pack : Nat := 11107
def dz : Nat := 46156
def spr : Nat := 120
def ginit : Nat := 754
def absorb17 : Nat := 1160
/-- `trabs` with `n4` groups of four lanes: 826 per group (one of them masked). -/
def trabs (n4 : Nat) : Nat := 55 + 826 * n4
/-- `cext` extracting `n` lanes. -/
def cext (n : Nat) : Nat := 19 + 205 * n

/-! ## Data-dependent subroutines (worst cases) -/

/-- `mu0`: the absorbing path (`|M| ≤ 69`), 8 `spr` calls, one `trabs 3`,
two more `spr` calls; the skipping path is cheaper. -/
def mu0 : Nat := 4359

/-- `fix` without a sixth squeeze: the first-flag scan (≤ 32 groups, 1810 in
total with entry and setup), at most 44 group-loop visits of at most 784
each (42 groups plus 2 exhaustion visits), the exhaustion check with the
continue path (59) and the exit (51). -/
def fixNo : Nat := 1810 + 44 * 784 + 59 + 51

/-- `fix` performing the sixth squeeze: as `fixNo` with the squeeze path
(two 800-byte `MCOPY`s, `kf4`, `blk`; 48350) instead of the continue path. -/
def fixSq : Nat := 1810 + 44 * 784 + 48350 + 51

/-- `gfix` own instructions with all four slots taking the `fix` call path. -/
def gfix0 : Nat := 630

/-- `gfix` with at most `n` active slots: at most one `fix` call squeezes the
sixth block (`HAVE6` is set by the first squeeze). -/
def gfix (n : Nat) : Nat := gfix0 + n * fixNo + (fixSq - fixNo)

/-- `group`: glue 470, `ginit`, five `kf4` + `blk`, `gfix 4`, `pass3`. -/
def group : Nat := 470 + ginit + 5 * (kf4 + blk) + gfix 4 + pass3

/-- `sib`: entry 13; positions `8 … 271`: at most 226 rejected bytes (125
each) and 39 accepted ones (454 each), counting the exit visits. -/
def sib : Nat := 13 + 226 * 125 + 39 * 454

/-- `dhint`: fixed part 312 plus at most 85 loop visits of at most 161 each
(80 hint indices, the trailing-zero scan, and the 5 loop exits). -/
def dhint : Nat := 312 + 85 * 161

end MlDsaOpt44.Proofs.Gas
