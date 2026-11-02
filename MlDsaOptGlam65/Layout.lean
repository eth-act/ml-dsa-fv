import MlDsaOpt65.Layout
import MlDsaOptGlam44.Layout
import MlDsaOptGlam65.Infra
set_option warningAsError true
/-!
# Entry points and stack budgets of the Glamsterdam ML-DSA-65 bytecode

`MlDsaOpt/65/glam/opt.hex` has the memory map, calling convention and
representations of the v4 bytes (`MlDsaOpt/65/layout.txt` and
`MlDsaOpt/65/glam/layout.txt` list the same memory map up to `KZ`), so every
definition of `MlDsaOpt65.Layout` is shared: the ported proofs `open
MlDsaOpt65.Proofs`. Only what depends on the code is redefined here, inside
`MlDsaOptGlam65.Proofs`, where it shadows the v4 constant:

* `SB`: the two 8 KB side buffers of the 42-call schedule's accumulation
  (`Layout.PACK65`, glam only), above `KZ`; memory is sized to `top = 0x1a700`
  (`memWords = 3384`);
* `Entry`: the subroutine entry pcs (`MlDsaOpt/65/glam/opt.asm` labels);
* `Stack`: the stack budgets, with the 74-slot leaf of the stack-resident Keccak
  kernels (as `MlDsaOptGlam44.Proofs.Stack`);
* the tables in memory, re-exported from glam 44 (the same code and table): no
  iota tables (`RC4Table` / `RC1Table` are `True`), and `TblAt` is the 4 + 4 NTT's
  240-record table (`nttRecG`).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOptCommon

/-! The iota tables (`RC4Table` / `RC1Table`, trivial: iota is an immediate) and the
4 + 4 NTT's table (`TblAt`, 240 records `nttRecG`) are glam 44's: the code and the
table are the same, so glam 44's lemmas about them apply verbatim. -/
export MlDsaOptGlam44.Proofs (RC4Table RC1Table TblAt nttRecG)

/-- Two 8 KB side buffers of the 42-call schedule's accumulation (`SB`, `SB + 8192`). -/
def SB : Nat := 0x16700

/-- The kf4 state image saved after the 42-call schedule's last call (inside `FIN`,
written before `FIN` is): slot 2 holds μ's sponge after block 0; `hash_mu`
restores it into `KS` for messages longer than one block. -/
def MUIMG : Nat := 0x15040

/-! The constants and spec-level data that `MlDsaOpt65.Layout` defines for this
parameter set (where they differ from ML-DSA-44's), re-exported so that they win over
`MlDsaOpt44.Proofs`' when a file of this namespace opens both. -/
export MlDsaOpt65.Proofs (P ZH2 BASES IDX ACC HP FIN RHO1 CB TRL MU BK SP TOP KZ HDR CTOFF Z0 H0 pkOf sigOf msgOf rhoOf ctOf mlenOf rawZ zLane zLo zHi spOff t1v zPolys hintOf cOf aOf t1Of trOf muOf cStream okZ okH okC okA hintD cD aD zHat azRow wRow w1Of finBytes optAccepts)

/-! ## Subroutine entry points (`MlDsaOpt/65/glam/opt.asm` labels) -/

namespace Entry
def absorb17 : Nat := 6737
def sib : Nat := 7333
def dhint : Nat := 7773
def dz : Nat := 8460
def blk : Nat := 10187
/-- `blk` on lanes 0 … 11 only (candidates 0 … 31 of the block). -/
def blkh : Nat := 10193
/-- The rest of block 4 (lanes 12 … 20), made by `gfix` on demand. -/
def blkt : Nat := 16552
/-- The fused pass of row group 0 (42-call schedule). -/
def pass3f7 : Nat := 16731
/-- The fused pass of row group 1 (42-call schedule). -/
def pass3f8 : Nat := 17053
def gfix : Nat := 17249
def ginit : Nat := 17659
def kmove : Nat := 18099
def lmerge : Nat := 18226
def trabs : Nat := 18543
def cext : Nat := 18992
def spr : Nat := 19266
def mub0 : Nat := 19481
def fix : Nat := 20056
def group : Nat := 20575
def tbuild : Nat := 20806
def csum : Nat := 21614
def pack : Nat := 22507
def ntt : Nat := 22890
def intt : Nat := 25476
def kf1 : Nat := 29888
def kf4 : Nat := 41842
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
def sib : Nat := leaf
def spr : Nat := leaf
def ginit : Nat := leaf
def absorb17 : Nat := leaf
def trabs : Nat := leaf
def cext : Nat := leaf
def kmove : Nat := leaf
def lmerge : Nat := leaf
def fix : Nat := max kf4 blk + 64
def pass3f : Nat := leaf
def mub0 : Nat := max trabs spr + 64
def gfix : Nat := max blk fix + 64
def group : Nat := max ginit (max kf4 (max blk gfix)) + 64
end Stack

end MlDsaOptGlam65.Proofs
