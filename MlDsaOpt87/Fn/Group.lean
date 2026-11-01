import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Fn.Ginit.Call
import MlDsaOpt87.Fn.Group.Pass3
import MlDsaOpt87.Fn.Group.Pass3m
import MlDsaOpt87.Fn.Group.Seed
import MlDsaOpt87.Fn.Group.Squeeze
import MlDsaOpt87.Fn.Group.Main
/-!
# Fused ExpandA · ẑ: `pass3`, `ginit`, `group` (ML-DSA-87, WP6)

`pass3 [64 k, zh, acc]` accumulates `acc[t] += ABUF[t] · lane k of zh[t]`
lane-wise (one `MUL` per word); ML-DSA-87 calls it only from `group`
(`zh = ZH + 0x2000 (col / 4)`, `acc = ACC + 0x2000 rb`). `pass3m [lm, 64 k, zh, acc]`
masks the candidate words by `lm` first; the main flow calls it for the mixed
groups 10–13 with `[lm, 64 k, ZH or ZH2, 0xe900]`. Both contracts are exact word
equations; the lane reading is a pure lemma. Proofs: `Fn/Group/Pass3.lean`,
`Fn/Group/Pass3m.lean` (ported from ML-DSA-44, pointers generalised).

`ginit` (`Fn/Ginit/Call.lean`) builds the kf4 state of a SIMD group;
`ginitWord`, `Rho1At`, `gOk`, `groupFrame` are in `Fn/Group/Defs.lean`.

`group [amask, col, rb, ret] ↦ [ok]` is one pure ExpandA SIMD group: column
`col`, slot `r` the row `4 rb + r` when bit `r` of `amask` is set (row `4 rb`
otherwise): `ginit`, five `kf4` + `blk`, `gfix amask`, `pass3`. ML-DSA-87 calls
it with `[15, col, 0]`, `col < 7`, and `[15, col, 1]`, `col < 3`. Proof:
`Fn/Group/Seed.lean` (`gL4_eq`, `ginit_group`, `aI_aSeed`), `Fn/Group/Squeeze.lean`
(`squeezes`), `Fn/Group/{Prologue,Blocks}.lean` (glue blocks) and
`Fn/Group/Main.lean` (`GroupP.g1_group_reach`).
-/

namespace MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3**: `[64 k, zh, acc, ret]`; `acc[t] += ABUF[t] · lane k of zh[t]`.
`zh` lies below `ACC` (ẑ: `ZH`, `ZH2`), `acc` inside the accumulators. -/
theorem pass3_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3 ret tail) (m : ByteArray) {k zh acc : Nat} (hk : k < 4)
    (hzh : zh + 8192 ≤ ACC) (hacc : ACC ≤ acc) (hacc' : acc + 8192 ≤ HP) :
    ∃ m', (∀ t, t < 256 → word m' (acc + 32 * t) =
        (word m (acc + 32 * t) + word m (ABUF + 32 * t) * lane (word m (zh + 32 * t)) k) % 2 ^ 256) ∧
      FrameExcept m m' [(acc, acc + 8192)] ∧
      Call s Entry.pass3 [wd (64 * k), wd zh, wd acc] ret tail m [] m' Gas.pass3 :=
  GroupP.pass3_reach hs hr m hk hzh hacc hacc'

/-- **pass3m**: `[lm, 64 k, zh, acc, ret]`; as `pass3` with the candidate words
masked by `lm` (the lanes of active slots). -/
theorem pass3m_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3m ret tail) (m : ByteArray) {k lm zh acc : Nat} (hk : k < 4)
    (hlm : lm < 2 ^ 256) (hzh : zh + 8192 ≤ ACC) (hacc : ACC ≤ acc) (hacc' : acc + 8192 ≤ HP) :
    ∃ m', (∀ t, t < 256 → word m' (acc + 32 * t) =
        (word m (acc + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * lane (word m (zh + 32 * t)) k) %
          2 ^ 256) ∧
      FrameExcept m m' [(acc, acc + 8192)] ∧
      Call s Entry.pass3m [wd lm, wd (64 * k), wd zh, wd acc] ret tail m [] m' Gas.pass3m :=
  GroupP.pass3m_reach hs hr m hk hlm hzh hacc hacc'

/-- **group**: `[amask, col, rb, ret] ↦ [ok]`; `ok = gOk` (every active
slot's `A[4 rb + r][col]` exists), and then every word of the row-group-`rb`
accumulators gains `(A[4 rb + r][col][t])_r · ẑ_col[t]`, `ẑ_col` lane `col % 4`
of `ZH + 0x2000 (col / 4)`; inactive lanes (`amask` bit clear) carry some value
below `2^23` (a raw `blk` candidate: `gfix` leaves them alone). Writes only
`groupFrame rb`; gas `Gas.group`. Proof (`GroupP.g1_group_reach`, port of
`MlDsaOpt44/Fn/Group/Main.lean`): `gB amask col rb`, the prologue's lane 4 `GroupP.gL4` (`gL4_eq`), seeds
`seedState 168 (aSeed cd (gRow amask rb k) col)` (`ginit_group`, `aI_aSeed`),
`squeezes`, `gfix_call` (incl. its kept-inactive-lanes conjunct), `pass3_reach`
at `zh = ZH + 8192 (col / 4)`, `acc = ACC + 8192 rb`. -/
theorem group_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (hamask : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (gOk s.executionEnv.calldata amask col rb = true →
        ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ACC + 8192 * rb + 32 * t) =
          (word m (ACC + 8192 * rb + 32 * t) +
            pack4 (fun r => if amask.testBit r then
                ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat else junk r t) *
              lane (word m (ZH + 8192 * (col / 4) + 32 * t)) (col % 4)) % 2 ^ 256) ∧
      FrameExcept m m' (groupFrame rb) ∧
      Call s Entry.group [wd amask, wd col, wd rb] ret tail m
        [flag (gOk s.executionEnv.calldata amask col rb)] m' Gas.group :=
  GroupP.g1_group_reach hs hr m hrc hrho hamask hcol hrb hcd

end MlDsaOpt87.Proofs
