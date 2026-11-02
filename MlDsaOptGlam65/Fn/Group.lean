import MlDsaOpt65.Fn.Group.Defs
import MlDsaOptGlam65.Fn.Ginit.Call
import MlDsaOptGlam65.Fn.Fix
import MlDsaOptGlam65.Fn.Keccak
import MlDsaOptGlam65.Fn.Blk
import MlDsaOptGlam65.Fn.GroupV4.Main
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Group.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# ExpandA groups and the fused accumulation (ML-DSA-65, v4)

`group [amask, col, rb, ret] ↦ [ok]` is one pure ExpandA SIMD group: column
`col`, slot `r` the row `4 rb + r` when bit `r` of `amask` is set: `ginit`, five
`kf4` with `blk` (`blkh` for the last block), `gfix amask`. v4: the group's
fixed-up candidates are left in `ABUF[0, 256)`; the main flow copies them to a
side buffer, and the fused passes `pass3f*` (generator `gen_pass3f`,
`plan_accumulation`) store or add every product of a batch into one
accumulator table, reading and writing each word once.

`ginit` (`Fn/Ginit/Call.lean`); `ginitWord`, `Rho1At`, `gOk`, `groupFrame`,
`zl` are in `Fn/Group/Defs.lean`.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **group**: `[amask, col, rb, ret] ↦ [ok]`; `ok` iff the active slots' rows
of column `col` exist, and then lane `r` of `ABUF[t]` is `A[4 rb + r][col][t]`
for the active slots `r` (other lanes hold values below `2^23`). -/
theorem group_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (hamask : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (gOk s.executionEnv.calldata amask col rb = true →
        ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ABUF + 32 * t) =
          pack4 (fun r => if amask.testBit r then
            ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat else junk r t)) ∧
      FrameExcept m m' (groupFrame rb) ∧
      Call s Entry.group [wd amask, wd col, wd rb] ret tail m
        [flag (gOk s.executionEnv.calldata amask col rb)] m' Gas.group :=
  group_call_aux hs hr m hrc hrho hamask hcol hrb hcd

/-- A fused pass's frame and call, given the word it stores at `acc[t]`. -/
def FusedPass (s : State) (entry ret : Nat) (tail : List UInt256) (m : ByteArray) (acc gas : Nat)
    (W : ByteArray → Nat → Nat) : Prop :=
  ∃ m', (∀ t, t < 256 → word m' (acc + 32 * t) = W m t) ∧
    FrameExcept m m' [(acc, acc + 8192)] ∧ Call s entry [] ret tail m [] m' gas

/-- `x · ẑ_j` of buffer word `t` (lane-wise product, one `MUL`). -/
def bz (m : ByteArray) (b j t : Nat) : Nat := word m (b + 32 * t) * zl m j t

/-- As `bz` with the buffer word masked by `msk` and shifted left by `64 d`. -/
def bzl (m : ByteArray) (b msk d j t : Nat) : Nat :=
  (word m (b + 32 * t) &&& msk) * 2 ^ (64 * d) % 2 ^ 256 * zl m j t

/-- As `bz` with the buffer word masked by `msk` and shifted right by `64 d`. -/
def bzr (m : ByteArray) (b msk d j t : Nat) : Nat :=
  (word m (b + 32 * t) &&& msk) / 2 ^ (64 * d) * zl m j t

-- glam: v4's `pass3f4` / `pass3f8` contracts are replaced by `Fn/Pack65.lean`

end MlDsaOptGlam65.Proofs
