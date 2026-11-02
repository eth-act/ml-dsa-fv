import MlDsaOpt87.Layout
import MlDsaOptGlam44.Layout
import MlDsaOptGlam87.Infra
set_option warningAsError true
/-!
# Entry points and stack budgets of the Glamsterdam ML-DSA-87 bytecode

`MlDsaOpt/87/glam/opt.hex` has the memory map, calling convention and
representations of the v4 bytes (`MlDsaOpt/87/layout.txt` and
`MlDsaOpt/87/glam/layout.txt` list the same memory map; memory is sized to
`0x16a20`, `memWords = 2897`), so every
definition of `MlDsaOpt87.Layout` is shared: the ported proofs `open
MlDsaOpt87.Proofs`. Only what depends on the code is redefined here, inside
`MlDsaOptGlam87.Proofs`, where it shadows the v4 constant:

* `Entry`: the subroutine entry pcs (`MlDsaOpt/87/glam/opt.asm` labels);
* `Stack`: the stack budgets, with the 74-slot leaf of the stack-resident Keccak
  kernels (as `MlDsaOptGlam44.Proofs.Stack`);
* the tables in memory, re-exported from glam 44 (the same code and table): no
  iota tables (`RC4Table` / `RC1Table` are `True`), and `TblAt` is the 4 + 4 NTT's
  240-record table (`nttRecG`).
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOptCommon

/-! The iota tables (`RC4Table` / `RC1Table`, trivial: iota is an immediate) and the
4 + 4 NTT's table (`TblAt`, 240 records `nttRecG`) are glam 44's: the code and the
table are the same, so glam 44's lemmas about them apply verbatim. -/
export MlDsaOptGlam44.Proofs (RC4Table RC1Table TblAt nttRecG)

/-! The constants and spec-level data that `MlDsaOpt87.Layout` defines for this
parameter set (where they differ from ML-DSA-44's), re-exported so that they win over
`MlDsaOpt44.Proofs`' when a file of this namespace opens both. -/
export MlDsaOpt87.Proofs (P ZH2 BASES IDX ACC HP FIN RHO1 CB TRL MU BK SP TOP KZ HDR CTOFF Z0 H0 pkOf sigOf msgOf rhoOf ctOf mlenOf rawZ zLane zLo zHi spOff t1v zPolys hintOf cOf aOf t1Of trOf muOf cStream okZ okH okC okA hintD cD aD zHat azRow wRow w1Of finBytes optAccepts)

/-! ## Subroutine entry points (`MlDsaOpt/87/glam/opt.asm` labels) -/

namespace Entry
def absorb17 : Nat := 6506
def sib : Nat := 7102
def dhint : Nat := 8196
def dz : Nat := 9119
def blk : Nat := 10846
/-- `blk` on lanes 0 … 11 only (candidates 0 … 31 of the block). -/
def blkh : Nat := 10852
/-- The rest of block 4 (lanes 12 … 20), made by `gfix` on demand. -/
def blkt : Nat := 17211
def pass3f4 : Nat := 17390
def pass3f6 : Nat := 17582
def pass3f10 : Nat := 17704
def pass3f14 : Nat := 17892
def gfix : Nat := 18160
def ginit : Nat := 18570
def trabs : Nat := 18925
def cext : Nat := 19374
def spr : Nat := 19648
def fix : Nat := 19863
def group : Nat := 20382
def tbuild : Nat := 20613
def csum : Nat := 21421
def pack : Nat := 22435
def ntt : Nat := 22818
/-- The inverse NTT with UseHint fused into its last pass (glam; v4 87 calls `usehint`). -/
def intt : Nat := 25404
def kf1 : Nat := 29816
def kf4 : Nat := 41770
end Entry

/-! ## Stack budgets

As v4 (a leaf, plus 64 per level of calls beneath it), with 74 slots for a
leaf instead of 64: the stack-resident Keccak kernels use 74 (`kf4_spec`). -/

namespace Stack
def leaf : Nat := 74
def kf4 : Nat := leaf
def kf1 : Nat := leaf
def blk : Nat := leaf
def ntt : Nat := leaf
def intt : Nat := leaf
def tbuild : Nat := leaf
def csum : Nat := leaf
def pack : Nat := leaf
def dz : Nat := leaf
def dhint : Nat := leaf
/-- `sib` squeezes `H(c̃)` with `kf1` (ML-DSA-87 has no free SIMD slot for it). -/
def sib : Nat := kf1 + 64
def spr : Nat := leaf
def ginit : Nat := leaf
def absorb17 : Nat := leaf
def trabs : Nat := leaf
def cext : Nat := leaf
def fix : Nat := max kf4 blk + 64
def pass3f : Nat := leaf
def gfix : Nat := max blk fix + 64
def group : Nat := max ginit (max kf4 (max blk gfix)) + 64
end Stack

end MlDsaOptGlam87.Proofs
