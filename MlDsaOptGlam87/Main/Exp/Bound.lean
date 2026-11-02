import MlDsaOptGlam87.Main.Exp.Acc
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/Exp/Bound.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Boundary invariants inside ExpandA (ML-DSA-87, v4)

`seg_exp` (`3371 … 4510`) is composed from sub-segments:

| pc | stack | invariant |
|---|---|---|
| 3371 | `[okZ]` | `Inv4` |
| 3612 | `[pureFlag cd okZ]` | `Exp.MixIn` (after group 9's copy to `HP + 0x2000`) |
| 5394 | `[… ∧ okCol cd 1 c 3, c = 3 … 6]` | `Exp.InvG14` (after group 13's copy to `HP + 0x2000`) |
| 4510 | `[okZ ∧ okA]` | `InvW` (group 14, `pass3f14`) |

Groups 10–13 run rows 4–6 of columns 3–6 in slots 0–2 with the `tr` rider in
slot 3; group 10 ends in `pass3f10` (`Acc1`), groups 11–13 copy `ABUF` to `CW`,
`HP`, `HP + 0x2000`, group 13 extracts `tr` to `TRL`.
-/

namespace MlDsaOptGlam87.Proofs.Exp

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs MlDsaOpt87.Proofs

/-- Before group 10 (pc 3612): rows 0–3 complete in `ACC`, rows 4–7 of columns
0–2 in `CW`, `HP`, `HP + 0x2000`. -/
structure MixIn (cd m : ByteArray) : Prop where
  inv : InvE cd m
  acc0 : Acc0 m cd 7
  c0 : ColAt m cd CW 1 0
  c1 : ColAt m cd HP 1 1
  c2 : ColAt m cd (HP + 8192) 1 2

/-- Before group 14 (pc 5394): `ACC + 0x2000` after `pass3f10` (`Acc1`), rows
4–6 of columns 4, 5, 6 in lanes 0–2 of `CW`, `HP`, `HP + 0x2000`, `tr` in `TRL`. -/
structure InvG14 (cd m : ByteArray) : Prop where
  inv : InvE cd m
  acc0 : Acc0 m cd 7
  acc1 : Acc1 m cd
  b11 : Col3At m cd CW 4
  b12 : Col3At m cd HP 5
  b13 : Col3At m cd (HP + 8192) 6
  trl : TrlAt m cd

/-- The flag of the mixed groups 10–13. -/
def mixFlag (cd : ByteArray) (b : Bool) : Bool :=
  (((b && okCol cd 1 3 3) && okCol cd 1 4 3) && okCol cd 1 5 3) && okCol cd 1 6 3

end MlDsaOptGlam87.Proofs.Exp
