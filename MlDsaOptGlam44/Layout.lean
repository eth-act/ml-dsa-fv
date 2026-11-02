import MlDsaOpt44.Layout
import MlDsaOptGlam44.Infra
set_option warningAsError true
/-!
# Entry points and stack budgets of the Glamsterdam ML-DSA-44 bytecode

`MlDsaOpt/44/glam/opt.hex` has the memory map, calling convention and
representations of the v4 bytes (`MlDsaOpt/44/layout.txt` and
`MlDsaOpt/44/glam/layout.txt` list the same memory map), so every definition of
`MlDsaOpt44.Layout` is shared: the ported proofs `open MlDsaOpt44.Proofs`.
Only what depends on the code is redefined here, inside
`MlDsaOptGlam44.Proofs`, where it shadows the v4 constant:

* `Entry`: the subroutine entry pcs (`MlDsaOpt/44/glam/opt.asm` labels);
* `Stack`: the stack budgets. The stack-resident kernels (`kf4`, `kf1`) keep
  their 25 lanes and temporaries on the stack (74 slots, `kf4_spec`);
* the tables in memory: there are no iota tables (iota is a `PUSH`
  immediate), so `RC4Table` / `RC1Table` are `True` here, kept so that v4's
  invariants port unchanged; `TblAt` is the 4 + 4 NTT's table
  (`scripts/opt_ntt_glam.py`, `Kernel4x4.records`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOptCommon
open MlDsaOpt44.Proofs (zm TBL)

/-- The iota table of v4's `kf4`. This artifact has none (iota is an
immediate), so the hypothesis is trivial; it keeps v4's invariant shapes. -/
def RC4Table (_ : ByteArray) : Prop := True
/-- The iota table of v4's `kf1`; trivial here, as `RC4Table`. -/
def RC1Table (_ : ByteArray) : Prop := True

/-- Record `i` of the 4 + 4 NTT's table: block `b = i / 15` holds the 15
Montgomery zetas of layers 5 … 8 for the 16 words `16 b … 16 b + 15`; with
`w = 8 / len` (1, 2, 4, 8 for `len` = 8, 4, 2, 1) and group `g < w`, record
`w − 1 + g` of the block is `zm (16 w + b w + g)`. -/
def nttRecG (i : Nat) : Nat :=
  let b := i / 15
  let r := i % 15
  let w := if r < 1 then 1 else if r < 3 then 2 else if r < 7 then 4 else 8
  zm (16 * w + b * w + (r + 1 - w))

/-- The long-message switch's flag word (`MISC + 0x160`): ExpandA stores `1` there
when it runs the packed schedule (`|M| < 342`); it stays `0` on the long-message
schedule. `hash_mu` and `sample_in_ball` branch on it. -/
def FLAG : Nat := 0x0f60

/-- The 4 + 4 NTT's table (240 words at `TBL`). -/
def TblAt (m : ByteArray) : Prop := ∀ i, i < 240 → word m (TBL + 32 * i) = nttRecG i

/-! ## Subroutine entry points (`MlDsaOpt/44/glam/opt.asm` labels) -/

namespace Entry
def absorb17 : Nat := 7000
def sib : Nat := 7596
def dhint : Nat := 8291
def dz : Nat := 8770
def blk : Nat := 10481
/-- `blk` on lanes 0 … 11 only (candidates 0 … 31 of the block). -/
def blkh : Nat := 10487
/-- The rest of block 4 (lanes 12 … 20), made by `gfix` on demand. -/
def blkt : Nat := 16846
def pass3f4 : Nat := 17025
/-- The fused pass of the long-message schedule (`|M| ≥ 342`). -/
def pass3f4b : Nat := 17297
def gfix : Nat := 17591
def ginit : Nat := 18001
def kmove : Nat := 18414
def lmerge : Nat := 18541
def trabs : Nat := 18792
def cext : Nat := 19241
def spr : Nat := 19515
def mub0 : Nat := 19730
/-- `mub` (the long-message schedule's μ blocks 1 … 5, `mulong`). -/
def mub : Nat := 20094
def fix : Nat := 20297
def group : Nat := 20814
def tbuild : Nat := 21045
def csum : Nat := 21853
def pack : Nat := 22636
def ntt : Nat := 23725
def intt : Nat := 26311
def kf1 : Nat := 30933
def kf4 : Nat := 42887
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
def pass3f4 : Nat := leaf
def tbuild : Nat := leaf
def csum : Nat := leaf
def pack : Nat := leaf
def dz : Nat := leaf
def dhint : Nat := leaf
def spr : Nat := leaf
def ginit : Nat := leaf
def absorb17 : Nat := leaf
def trabs : Nat := leaf
def cext : Nat := leaf
def kmove : Nat := leaf
def lmerge : Nat := leaf
def sib : Nat := max kf4 cext + 64
def mub0 : Nat := max trabs spr + 64
def mub : Nat := max trabs (max spr cext) + 64
def pass3f4b : Nat := leaf
def fix : Nat := max kf4 blk + 64
def gfix : Nat := max blk fix + 64
def group : Nat := max ginit (max kf4 (max blk gfix)) + 64
end Stack

end MlDsaOptGlam44.Proofs
