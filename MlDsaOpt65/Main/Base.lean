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
/-- `992 … 1101`: `dz [ZH, Z0]`, `dz [ZH2, Z0 + 2560]`, flag masking and check. -/
def pZ : Nat := 71 + 2 * dz
/-- `1101 … 3084`: the 248 NTT zeta records. -/
def pTbl : Nat := 2232
/-- `3084 … 3106`: `ntt(ZH)`, `ntt(ZH2)`, the return `JUMPDEST`. -/
def pNtt : Nat := 36 + 2 * ntt
/-- `3106 … 3556`: `RHO1` (ρ and c̃ lanes spread, ten `spr` calls). -/
def pRho : Nat := 705 + 10 * spr
/-- `3556 … 5242`: ExpandA: the five pure groups of row group 0 (copies to
`CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000`, then `pass3f4`), the mixed groups
5 … 7 (row group 1 instances, `tr`; copies to `CW`, `HP`, `HP + 0x2000`), group
8 (`A[5][4]`, c̃ stream, μ's blocks 0 … 4 in slot 2, `mub0`/`mub`, the `mulong`
region), `pass3f8`. Longest static path: row group 0 2038895
(`Exp.exp_pure`), groups 5–7 1152470 (`Exp.gG57`), group 8 and `pass3f8` on the
`mulong` path (`|M| ≥ 70`: five `mub` instead of `cext [MU, 2, 8]`) 432185
(the short-μ path is 13870 cheaper). -/
def pExp : Nat := 3623550
/-- `5242 … 5356`: zero the side buffers in `CW`, `HP`, `HP + 0x2000`, `dhint`, `AND`. -/
def pZd : Nat := 2448 + dhint
/-- `5356 … 6172`: μ, from `MU` (`|M| ≤ 613`, 195) or by `kf1` from slot 2's
state (`hash_mu`): selection 24, setup (`cext 25`, replication, block 5) 6884,
one loop visit (`kf1` + `absorb17` + 88) per further 136 bytes plus one, the
final permutation (`kf1` + 202). -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 613 then 195
  else 24 + 6884 + ((mlen - 614) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)
/-- `6172 … 6182`: `sib`, `AND`. -/
def pSib : Nat := 19 + sib
/-- `6182 … 6237`: `tbuild`, `csum` for each row group. -/
def pCt : Nat := 84 + 2 * (tbuild + csum)
/-- `6237 … 6293`: `intt` (with UseHint), `pack` for each row group (4 and 2 rows). -/
def pW : Nat := 84 + 2 * intt + pack 4 + pack 2
/-- `6293 …`: the final hash (six absorbing `kf1` visits and the last one),
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
