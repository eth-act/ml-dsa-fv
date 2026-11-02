import MlDsaOptGlam65.Main.Frame
import MlDsaOptGlam65.Budget
import MlDsaOptGlam65.Layout
/- Ported from `MlDsaOpt65/Main/Base.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Main-flow segments: budgets and shared definitions (ML-DSA-65)

The main flow is cut into segments between the boundaries of `Main/Inv.lean`;
each segment is one theorem in `Main/Seg*.lean`. Every segment budget is the
static cost of its glue plus the budgets of its calls
(`python3 scripts/proofgen_gas_param.py 65 --schedule`, `p_*`; the glue is the
longest static path with every call costed 0).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Gas

open MlDsaOpt65.Proofs MlDsaOpt65.Proofs.Gas

/-- `0 … 15`: size check and the sizing store (static cost; memory expansion
to `memWords` is added by the trace).  -- glam: no iota tables -/
def pInit : Nat := 29
/-- `992 … 1101`: `dz [ZH, Z0]`, `dz [ZH2, Z0 + 2560]`, flag masking and check. -/
def pZ : Nat := 71 + 2 * dz
/-- `124 … 2043`: the 240 records of the 4 + 4 NTT's table.  -- glam -/
def pTbl : Nat := 2160
/-- `3084 … 3106`: `ntt(ZH)`, `ntt(ZH2)`, the return `JUMPDEST`. -/
def pNtt : Nat := 36 + 2 * ntt
/-- `3106 … 3556`: `RHO1` (ρ and c̃ lanes spread, ten `spr` calls). -/
def pRho : Nat := 705 + 10 * spr
/-- `3556 … 4903`: ExpandA: the five pure groups of row group 0 (copies to
`CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000`, then `pass3f4`), the mixed groups
5 … 7 (row group 1 instances, `tr`; copies to `CW`, `HP`, `HP + 0x2000`), group
8 (`A[5][4]`, c̃ stream, μ's blocks 0 … 4 in slot 2, `mub0`/`mub`, the `mulong`
region), `pass3f8`. Longest static path: row group 0 2038895
(`Exp.exp_pure`), groups 5–7 1152470 (`Exp.gG57`), group 8 and `pass3f8` on the
`mulong` path (`|M| ≥ 70`: five `mub` instead of `cext [MU, 2, 8]`) 432185
(the short-μ path is 13870 cheaper). -/
def pExp : Nat := 3623550  -- glam: provisional (v4's), until the 42-call schedule's `seg_exp`
/-- `4903 … 5356`: zero the side buffers in `CW`, `HP`, `HP + 0x2000`, `dhint`, `AND`. -/
def pZd : Nat := 2448 + dhint
/-- `5017 … 5843`: μ, from `MU` (`|M| ≤ 69`, 195) or by `kf1` from μ's sponge after
block 0, slot 2 of the state image `MUIMG` (`hash_mu`): selection 24, setup 6971
(`MCOPY` to `KS` 87, `cext 25` 5167, replication 522, block 1's `absorb17` 1195),
one loop visit (`kf1` + `absorb17` + 88) per further full block (`⌊(|M| + 66) / 136⌋ - 1`
of them), the padded last block and the final permutation (`kf1` + 225).  -- glam: exact -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 69 then 195
  else 24 + 6971 + (mlen - 70) / 136 * (kf1 + absorb17 + 88) + (kf1 + 225)
/-- `5843 … 6182`: `sib`, `AND`. -/
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

end MlDsaOptGlam65.Proofs
