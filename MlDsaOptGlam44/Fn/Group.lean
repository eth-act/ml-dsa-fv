import MlDsaOptGlam44.Fn.Fix
import MlDsaOptGlam44.Fn.Sponge
import MlDsaOptGlam44.Fn.Keccak
import MlDsaOpt44.Fn.Group.Defs
import MlDsaOptGlam44.Fn.Group.Pass3f4
import MlDsaOptGlam44.Fn.Group.Main
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Group.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# ExpandA groups and the fused accumulation: `group`, `pass3f4` (WP6)

`group [amask, col, rb, ret] ↦ [ok]` is one pure ExpandA SIMD group (column
`col`, rows `0 … 3`): `ginit`, five `kf4` with `blk` (`blkh` for the last
block), `gfix`. ML-DSA-44 calls it with `rb = 0`, `amask = 15`, `col ∈ {0, 1}`;
the group's fixed-up candidates are left in `ABUF[0, 256)` (v4: the caller
copies them to a side buffer and accumulates later).

`pass3f4 [ret]` is ML-DSA-44's single fused accumulation pass: for every
`t < 256` it stores into `ACC[t]` (no read) the sum of the lane-wise products
of the five buffers with the ẑ lanes (`acc4Word`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- Regions a SIMD group may write. -/
def groupFrame : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800)]

/-- **group**: `[15, col, 0, ret] ↦ [ok]`; `ok` iff `A[r][col]` exists for all
rows, and then `ABUF[t] = (A[0][col][t], …, A[3][col][t])`. -/
theorem group_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {col : Nat} (hcol : col < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome) = true →
        ∀ t, t < 256 → word m' (ABUF + 32 * t) =
          pack4 (fun r => ((aD s.executionEnv.calldata r col)[t]!).toNat)) ∧
      FrameExcept m m' groupFrame ∧
      Call s Entry.group [wd 15, wd col, wd 0] ret tail m
        [flag ((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome)] m'
        Gas.group :=
  group_call_aux hs hr m hrc hrho hcol hcd

/-- The word `pass3f4` stores at `ACC[t]`: columns 0 and 1 (`CW`, `HP`,
aligned), column 2 rows 0 … 2 (`SB`, slots 1 … 3), row 3 columns 2, 3 (the
Kronecker product of `SB + 8192`'s slots 2, 3 with `ẑ_2, ẑ_3`, lane 3) and
column 3 rows 0 … 2 (`ABUF`, slots 1 … 3). -/
def acc4Word (m : ByteArray) (t : Nat) : Nat :=
  let z := word m (ZH + 32 * t)
  (word m (CW + 32 * t) * lane z 0 + word m (HP + 32 * t) * lane z 1 +
    word m (SB + 32 * t) / 2 ^ 64 * lane z 2 +
    ((word m (SB + 8192 + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
      (M64 * 2 ^ 192)) +
    word m (ABUF + 32 * t) / 2 ^ 64 * lane z 3) % 2 ^ 256

/-- **pass3f4**: `[ret]`; `ACC[t] := acc4Word t`. -/
theorem pass3f4_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) = acc4Word m t) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f4 [] ret tail m [] m' Gas.pass3f4 :=
  pass3f4_call_aux hs hr m

end MlDsaOptGlam44.Proofs
