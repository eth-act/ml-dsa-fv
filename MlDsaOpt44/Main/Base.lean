import MlDsaOpt44.Main.Frame
import MlDsaOpt44.Math
set_option warningAsError true
/-!
# Main-flow segments: budgets and shared definitions

The main flow is cut into segments between the boundaries of `Main/Inv.lean`;
each segment is one theorem in `Main/Seg*.lean`. Straight-line glue is
proved with `opt44_reach`; calls use the subroutine contracts of
`MlDsaOpt44/Fn`. Every segment budget is the static cost of its glue plus the
budgets of its calls (`scripts/proofgen_gas.py --phases`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

namespace Gas

/-- `0 … 992`: size check, the sizing store and the `RC4` / `RC1` tables
(static cost; memory expansion to `memWords` is added by the trace). -/
def pInit : Nat := 658
/-- `992 … 1076`: `dz`, the norm-flag check. -/
def pZ : Nat := 41 + dz
/-- `1076 … 3059`: the 248 NTT zeta records. -/
def pTbl : Nat := 2232
/-- `3059 … 3069`: `ntt(ZH)`. -/
def pNtt : Nat := 17 + ntt
/-- `3069 … 3430`: `RHO1` (8 `spr` calls). -/
def pRho : Nat := 527 + 8 * spr
/-- `3430 … 3453`, `3453 … 3477`: the two pure ExpandA groups, each followed by
the `MCOPY` of `ABUF` to its side buffer (771). -/
def pG0 : Nat := 805 + group
def pG1 : Nat := 806 + group
/-- `3477 … 3875`: the mixed group (tr blocks 0 … 4 in slot 0, column 2 rows
0 … 2) and its copy to `SB`. -/
def pG2 : Nat := 1153 + ginit + 5 * trabs 5 + 5 * kf4 + 4 * blk + blkh + gfix 3
/-- `3875 … 4973`: the packed window (eight `kf4` calls: tr blocks 5 … 9, c̃,
μ's block 0, row 3 columns 2 and 3, column 3 rows 0 … 2), its two fix-ups and
the fused accumulation. -/
def pWin : Nat :=
  2785 + 3 * ginit + 4 * trabs 5 + trabs 3 + 8 * kf4 + 7 * blk + blkh + mub0 + 2 * cext 8 + cext 17 +
    3 * kmove + lmerge 8 + lmerge 1 + gfix 2 + gfix 3 + pass3f4
/-- `4973 … 5075`: zero the side buffers in `CW` and `HP`, `dhint`, `AND`. -/
def pZd : Nat := 1668 + dhint
/-- `5075 … 5876`: μ, from the SIMD slot (`|M| ≤ 69`) or by `kf1` from the
slot's saved state (`hash_mu`): dispatch 24, setup 667 with `cext 25` and the
absorption of block 1, one loop visit (kf1 + absorb17 + 88) per further 136
bytes of `tr ‖ 0 ‖ 0 ‖ M` plus one, the final permutation (kf1 + 202). -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 69 then 195
  else 24 + 667 + cext 25 + absorb17 + ((mlen - 70) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `5876 … 5886`: `sib`, `AND`. -/
def pSib : Nat := 19 + sib
/-- `5886 … 5913`: `tbuild`, `csum`. -/
def pCt : Nat := 42 + tbuild + csum
/-- `5913 … 5940`: `intt` (with UseHint), `pack`. -/
def pW : Nat := 42 + intt + pack
/-- `5940 …`: the final hash (six absorbing `kf1` calls and the last one),
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


end MlDsaOpt44.Proofs
