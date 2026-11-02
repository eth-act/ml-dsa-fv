import MlDsaOptGlam87.Main.Frame
import MlDsaOptGlam87.Budget
import MlDsaOptGlam87.Layout
/- Ported from `MlDsaOpt87/Main/Base.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Main-flow segments: budgets and shared definitions (ML-DSA-87)

The main flow is cut into segments between the boundaries of `Main/Inv.lean`;
each segment is one theorem in `Main/Seg*.lean`. Every segment budget is the
static cost of its glue plus the budgets of its calls: the `p_*` numbers of
`python3 scripts/proofgen_gas_param.py 87 --schedule`, decomposed by the call
sites in `MlDsaOpt/87/opt.asm` (glue = longest static path minus the callee
budgets).
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

namespace Gas

open MlDsaOpt87.Proofs MlDsaOpt87.Proofs.Gas

/-- `0 … 15`: size check and the sizing store (static cost; memory expansion
to `memWords` is added by the trace).  -- glam: no iota tables -/
def pInit : Nat := 29
/-- `992 … 1117`: `dz` twice (the second flag word masked to lanes 0–2), the
norm-flag check (v4: no `dhint`, no `sib` here). -/
def pZ : Nat := 71 + 2 * dz
/-- `1117 … 3100`: the 248 NTT zeta records. -/
def pTbl : Nat := 2160  -- glam: the 240 records of the 4 + 4 NTT's table
/-- `3100 … 3122`: `ntt(ZH)`, `ntt(ZH2)`, the return `JUMPDEST`. -/
def pNtt : Nat := 36 + 2 * ntt
/-- `3122 … 3371`: `RHO1` (4 `spr` calls). -/
def pRho : Nat := 275 + 4 * spr
/-- `3371 … 4510`: ExpandA, all fifteen groups (copies of `ABUF` to the side
buffers `CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000`; the fused passes `pass3f4`,
`pass3f6`, `pass3f10`, `pass3f14`; the `tr` rider of groups 10–13, `TRL`).
Longest static path (`scripts/proofgen_gas_param.py`). -/
def pExp : Nat := 5435839  -- glam: pureCost 3617135 + gG1013 1406472 + gG14 412232
/-- `4510 … 5665`: zero the side buffers in `CW`, `HP`, `HP + 0x2000`, `dhint`, `AND`. -/
def pZd : Nat := 2448 + dhint
/-- `5665 … 6663`: μ = `H(tr ‖ 0 ‖ 0 ‖ M)` by `kf1` (`hash_mu`): setup 982, one
loop visit (`kf1` + `absorb17` + 88) per 136 bytes of `tr ‖ 0 ‖ 0 ‖ M` plus one
(the exit visit), the padding and final permutation (`kf1` + 202); μ to `FIN`. -/
def pMu (mlen : Nat) : Nat :=
  982 + ((66 + mlen) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `6663 … 6672`: `sib` (its own `kf1` sponge for `H(c̃)`), `AND`. -/
def pSib : Nat := 18 + sib
/-- `6672 … 6727`: `tbuild`, `csum` per row group. -/
def pCt : Nat := 84 + 2 * (tbuild + csum)
/-- `5686 … 5742`: `intt` (UseHint fused), `pack 4` per row group. -/
def pW : Nat := 84 + 2 * (intt + pack 4)  -- glam: no `usehint` call
/-- `6805 …`: the final hash (eight absorbing `kf1` visits of the 17-lane
loop over the 136 `FIN` lanes, then the padding block), the 64-byte c̃
comparison, `mstore(0, ok)`, `return(0, 32)`. -/
def pFin : Nat := 220 + 8 * (kf1 + 495) + (kf1 + 479)

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

end MlDsaOptGlam87.Proofs
