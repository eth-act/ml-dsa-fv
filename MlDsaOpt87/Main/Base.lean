import MlDsaOpt87.Main.Frame
import MlDsaOpt87.Budget
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

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

namespace Gas

/-- `0 … 992`: size check, the sizing store and the `RC4` / `RC1` tables
(static cost; memory expansion to `memWords` is added by the trace). -/
def pInit : Nat := 658
/-- `992 … 1126`: `dz` twice (the second flag word masked to lanes 0–2), the
norm-flag check, `dhint`, `AND`. -/
def pZh : Nat := 89 + 2 * dz + dhint
/-- `1126 … 1135`: `sib` (its own `kf1` sponge for `H(c̃)`), `AND`. -/
def pSib : Nat := 18 + sib
/-- `1135 … 3118`: the 248 NTT zeta records. -/
def pTbl : Nat := 2232
/-- `3118 … 3140`: `ntt(ZH)`, `ntt(ZH2)`. -/
def pNtt : Nat := 36 + 2 * ntt
/-- `3140 … 3389`: `RHO1` (4 `spr` calls). -/
def pRho : Nat := 275 + 4 * spr
/-- `3389 … 3530`: the ten pure ExpandA groups `[15, col, rb]` (glue 25–27). -/
def pG0 : Nat := 25 + group
def pG1 : Nat := 26 + group
def pG2 : Nat := 26 + group
def pG3 : Nat := 26 + group
def pG4 : Nat := 26 + group
def pG5 : Nat := 26 + group
def pG6 : Nat := 26 + group
def pG7 : Nat := 26 + group
def pG8 : Nat := 27 + group
def pG9 : Nat := 27 + group
/-- `3530 … 3963`, `3963 … 4430`, `4430 … 4898`: the mixed groups 10–12 (rows
4–6, `tr` rider in slot 3): `ginit`, five `trabs 5` + `kf4` + `blk`, `gfix` on 3
slots, `pass3m`. -/
def pG10 : Nat := 405 + ginit + 5 * trabs 5 + 5 * (kf4 + blk) + gfix 3 + pass3m
def pG11 : Nat := 406 + ginit + 5 * trabs 5 + 5 * (kf4 + blk) + gfix 3 + pass3m
def pG12 : Nat := 407 + ginit + 5 * trabs 5 + 5 * (kf4 + blk) + gfix 3 + pass3m
/-- `4898 … 5435`: mixed group 13 (last `tr` block `trabs 1` with padding,
`cext 8` into `TRL`). -/
def pG13 : Nat :=
  467 + ginit + 4 * trabs 5 + trabs 1 + 5 * (kf4 + blk) + cext 8 + gfix 3 + pass3m
/-- `5435 … 5593`: the Kronecker group 14 (row 7, columns 3–6): `ginit`, five
`kf4` + `blk`, `gfix` on 4 slots, `pass3k14`. -/
def pG14 : Nat := 249 + ginit + 5 * (kf4 + blk) + gfix 4 + pass3k14
/-- `5593 … 6591`: μ = `H(tr ‖ 0 ‖ 0 ‖ M)` by `kf1` (`hash_mu`): setup 982, one
loop visit (`kf1` + `absorb17` + 88) per 136 bytes of `tr ‖ 0 ‖ 0 ‖ M` plus one
(the exit visit), the padding and final permutation (`kf1` + 202). -/
def pMu (mlen : Nat) : Nat :=
  982 + ((66 + mlen) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `6591 … 6646`: `tbuild`, `csum` per row group. -/
def pCt : Nat := 84 + 2 * (tbuild + csum)
/-- `6646 … 6724`: `intt`, `usehint`, `pack 4` per row group. -/
def pW : Nat := 120 + 2 * (intt + usehint + pack 4)
/-- `6724 …`: the final hash (eight absorbing `kf1` visits of the 17-lane
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

end MlDsaOpt87.Proofs
