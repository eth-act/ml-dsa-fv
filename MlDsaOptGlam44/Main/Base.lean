import MlDsaOptGlam44.Main.Frame
import MlDsaOpt44.Math
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/Base.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Main-flow segments: budgets and shared definitions

The main flow is cut into segments between the boundaries of `Main/Inv.lean`;
each segment is one theorem in `Main/Seg*.lean`. Straight-line glue is
proved with `glam44_rreach`; calls use the subroutine contracts of
`MlDsaOptGlam44/Fn`. The pcs are those of `MlDsaOpt/44/glam/opt.asm`. Every
segment budget is the static cost of its glue plus the budgets of its calls.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

namespace Gas

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Gas

/-- `0 … 15`: size check and the sizing store (static cost; memory expansion
to `memWords` is added by the trace). -/
def pInit : Nat := 29
/-- `15 … 99`: `dz`, the norm-flag check. -/
def pZ : Nat := 41 + dz
/-- `99 … 2018`: the 240 records of the 4 + 4 NTT's table. -/
def pTbl : Nat := 2160
/-- `2018 … 2028`: `ntt(ZH)`. -/
def pNtt : Nat := 17 + ntt
/-- `2028 … 2389`: `RHO1` (8 `spr` calls). -/
def pRho : Nat := 527 + 8 * spr
/-- `2389 … 2412`, `2412 … 2436`: the two pure ExpandA groups, each followed by
the `MCOPY` of `ABUF` to its side buffer (771). -/
def pG0 : Nat := 805 + group
def pG1 : Nat := 806 + group
/-- `2452 … 2850` (packed schedule): the mixed group (tr blocks 0 … 4 in slot 0, column 2 rows
0 … 2) and its copy to `SB`. -/
def pG2 : Nat := 1153 + ginit + 5 * trabs 5 + 5 * kf4 + 4 * blk + blkh + gfix 3
/-- `2436 … 2452`: the long-message switch on the packed side (the test and
`FLAG := 1`). -/
def pSw : Nat := 33
/-- `3948 … 5081`: the packed schedule's jump to the shared code. -/
def pJoin : Nat := 12
/-- `2850 … 3948` (packed schedule): the window (eight `kf4` calls: tr blocks 5 … 9, c̃,
μ's block 0, row 3 columns 2 and 3, column 3 rows 0 … 2), its two fix-ups and
the fused accumulation. -/
def pWin : Nat :=
  2785 + 3 * ginit + 4 * trabs 5 + trabs 3 + 8 * kf4 + 7 * blk + blkh + mub0 + 2 * cext 8 + cext 17 +
    3 * kmove + lmerge 8 + lmerge 1 + gfix 2 + gfix 3 + pass3f4
/-- `5081 … 5183`: zero the side buffers in `CW` and `HP`, `dhint`, `AND`. -/
def pZd : Nat := 1668 + dhint
/-- `5183 … 6020` (packed schedule): μ, from the SIMD slot (`|M| ≤ 69`) or by
`kf1` from the slot's saved state (`hash_mu`): dispatch 41 (v4's 24 plus 17 for
the `FLAG`-dependent bound), setup 723 (v4's 667 plus 22 for `hash_mu`'s `FLAG`
test and 2 × 17 for the bound) with `cext 25` and the absorption of block 1, one
loop visit (kf1 + absorb17 + 88) per further 136 bytes of `tr ‖ 0 ‖ 0 ‖ M` plus
one, the final permutation (kf1 + 202). -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 69 then 212
  else 41 + 723 + cext 25 + absorb17 + ((mlen - 70) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `6020 … 6030`: `sib`, `AND` (packed schedule). -/
def pSib : Nat := 19 + sib
/-- `6030 … 6057`: `tbuild`, `csum`. -/
def pCt : Nat := 42 + tbuild + csum
/-- `6057 … 6084`: `intt` (with UseHint), `pack`. -/
def pW : Nat := 42 + intt + pack
/-- `6084 …`: the final hash (six absorbing `kf1` calls and the last one),
the c̃ comparison, `mstore(0, ok)`, `return(0, 32)`. -/
def pFin : Nat := 220 + 6 * (kf1 + 495) + (kf1 + 327)

end Gas

/-- The state after the sizing store: `memWords` active words. -/
def sized (s : State) : State := { s with activeWords := UInt256.ofNat memWords }

theorem sized_activeWords (s : State) : (sized s).activeWords.toNat = memWords := by
  unfold sized memWords
  exact toNat_ofNat_of_lt (by norm_num)

theorem sized_ctx {s : State} (h0 : Ctx0 s) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    Ctx (sized s) where
  code := h0.code
  fork := h0.fork
  notPrecompile := h0.notPrecompile
  running := h0.running
  sized := by rw [sized_activeWords]
  small := by rw [sized_activeWords]; unfold memWords; norm_num
  calldataFits := hfit

/-- A return address in the main flow (stack tail of at most 8 words). -/
theorem retOK_main {B ret : Nat} {tail : List UInt256} (hB : B ≤ 1000) (htl : tail.length ≤ 8)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) : RetOK B ret tail :=
  ⟨hj, hret, by omega⟩

/-- The halted state after `mstore(0, v); return(0, 32)`. -/
def finalState (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) (v : Nat) : State :=
  { callState s pc stk (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) 0) with
    halt := .Returned
    hReturn := MachineState.readPadded
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) 0) 0 32 }


end MlDsaOptGlam44.Proofs
