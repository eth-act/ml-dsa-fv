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
/-- `992 … 1085`: `dz`, flag check, `dhint`, `AND`. -/
def pZh : Nat := 59 + dz + dhint
/-- `1085 … 3068`: the 248 NTT zeta records. -/
def pTbl : Nat := 2232
/-- `3068 … 3078`: `ntt(ZH)`. -/
def pNtt : Nat := 17 + ntt
/-- `3078 … 3439`: `RHO1` (8 `spr` calls). -/
def pRho : Nat := 527 + 8 * spr
/-- `3439 … 3452`, `3452 … 3466`: the two pure ExpandA groups. -/
def pG0 : Nat := 25 + group
def pG1 : Nat := 26 + group
/-- `3466 … 4648`: the three mixed groups (tr, c̃ and μ riders), with glue
1209: three `ginit`, fifteen `kf4` + `blk`, ten `trabs`, four `cext`, `mu0`,
`gfix` on 3, 3 and 2 slots, two `pass3m`, `pass3k4`. -/
def pG234 : Nat :=
  1209 + 3 * ginit + 15 * (kf4 + blk) + 9 * trabs 5 + trabs 3 + 2 * cext 17 + 2 * cext 8 + mu0 +
    2 * gfix 3 + gfix 2 + 2 * pass3m + pass3k4
/-- `4648 … 5926`: μ, from the SIMD slot (`|M| ≤ 69`) or by `kf1` (`hash_mu`):
setup 983, one loop visit (kf1 + absorb17 + 88) per 136 bytes of
`tr ‖ 0 ‖ 0 ‖ M` plus one, the final permutation (kf1 + 202). -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 69 then 196
  else 25 + 983 + ((66 + mlen) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `5926 … 5936`: `sib`, `AND`. -/
def pSib : Nat := 19 + sib
/-- `5936 … 5963`: `tbuild`, `csum`. -/
def pCt : Nat := 42 + tbuild + csum
/-- `5963 … 6001`: `intt`, `usehint`, `pack`. -/
def pW : Nat := 60 + intt + usehint + pack
/-- `6001 …`: the final hash (six absorbing `kf1` calls and the last one),
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
