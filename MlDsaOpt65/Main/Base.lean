import MlDsaOpt65.Main.Frame
import MlDsaOpt65.Budget
set_option warningAsError true
/-!
# Main-flow segments: budgets and shared definitions (ML-DSA-65)

The main flow is cut into segments between the boundaries of `Main/Inv.lean`;
each segment is one theorem in `Main/Seg*.lean`. Every segment budget is the
static cost of its glue plus the budgets of its calls
(`python3 scripts/proofgen_gas_param.py 65 --schedule`, `p_*`; the glue is the
longest static path with every call costed 0).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Gas

/-- `0 … 992`: size check, the sizing store and the `RC4` / `RC1` tables
(static cost; memory expansion to `memWords` is added by the trace). -/
def pInit : Nat := 658
/-- `992 … 1110`: `dz [ZH, Z0]`, `dz [ZH2, Z0 + 2560]`, flag masking and check,
`dhint`, `AND`. -/
def pZh : Nat := 89 + 2 * dz + dhint
/-- `1110 … 3093`: the 248 NTT zeta records. -/
def pTbl : Nat := 2232
/-- `3093 … 3115`: `ntt(ZH)`, `ntt(ZH2)`. -/
def pNtt : Nat := 36 + 2 * ntt
/-- `3115 … 3565`: `RHO1` (ρ and c̃ lanes spread, ten `spr` calls). -/
def pRho : Nat := 705 + 10 * spr
/-- `3565 … 3578`: `group [15, 0, 0]`, `AND`. -/
def pG0 : Nat := 25 + group
/-- `3578 … 3634`: `group [15, s, 0]`, `s = 1 … 4`, `AND` (one segment each). -/
def pG1 : Nat := 26 + group
def pG2 : Nat := 26 + group
def pG3 : Nat := 26 + group
def pG4 : Nat := 26 + group
/-- `3634 … 4033`: group 5 (instances 0–2: `A[4][0]`, `A[5][0]`, `A[4][1]`; `tr`
blocks 0–4): `ginit`, five `trabs 5` + `kf4` + `blk`, `gfix [7]` (three active
slots), `AND`, `pass3x5`. -/
def pG5 : Nat := 392 + ginit + 5 * (trabs 5 + kf4 + blk) + gfix 3 + pass3x5
/-- `4033 … 4468`: group 6 (instances 3–5: `A[5][1]`, `A[4][2]`, `A[5][2]`; `tr`
blocks 5–9), `pass3x6`. -/
def pG6 : Nat := 395 + ginit + 5 * (trabs 5 + kf4 + blk) + gfix 3 + pass3x6
/-- `4468 … 4972`: group 7 (instances 6–8: `A[4][3]`, `A[5][3]`, `A[4][4]`; `tr`
blocks 10–14, `cext 8` into `TRL`), `pass3x7`. -/
def pG7 : Nat :=
  455 + ginit + 4 * trabs 5 + trabs 2 + 5 * (kf4 + blk) + cext 8 + gfix 3 + pass3x7
/-- `4972 … 5190`: group 8 (instance 9: `A[5][4]`; the c̃ stream: two `cext 17`
into `CB`; the μ rider: `mu0`, `cext 8` into `MU`), `gfix [1]`, `pass3x8`, the
return `JUMPDEST`. -/
def pG8 : Nat := 341 + ginit + mu0 + 5 * (kf4 + blk) + 2 * cext 17 + cext 8 + gfix 1 + pass3x8
/-- `5190 … 6499`: μ, from the SIMD slot (`|M| ≤ 69`, 195) or by `kf1`
(`hash_mu`): selection 24, setup 983, one loop visit (`kf1` + `absorb17` + 88)
per 136 bytes of `tr ‖ 0 ‖ 0 ‖ M` plus one, the final permutation (`kf1` + 202). -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 69 then 195
  else 24 + 983 + ((66 + mlen) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `6499 … 6509`: `sib`, `AND`. -/
def pSib : Nat := 19 + sib
/-- `6509 … 6564`: `tbuild`, `csum` for each row group. -/
def pCt : Nat := 84 + 2 * (tbuild + csum)
/-- `6564 … 6642`: `intt`, `usehint`, `pack` for each row group (4 and 2 rows). -/
def pW : Nat := 120 + 2 * (intt + usehint) + pack 4 + pack 2
/-- `6642 …`: the final hash (six absorbing `kf1` visits and the last one),
the 48-byte c̃ comparison, `mstore(0, ok)`, `return(0, 32)`. -/
def pFin : Nat := 220 + 6 * (kf1 + 495) + (kf1 + 485)

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

end MlDsaOpt65.Proofs
