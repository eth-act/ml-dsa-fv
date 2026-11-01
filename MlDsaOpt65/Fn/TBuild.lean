import MlDsaOpt65.Fn.TBuild.Run
set_option warningAsError true
/-!
# `tbuild`: the `c · t1` window table (65/87 generalisation of `MlDsaOpt44/Fn/Ct.lean`)

`tbuild [tp, off, ret]` writes the window table of the four `t1` rows packed at calldata
offset `off`: 768 16-bit fields per row, interleaved by row (field `(e, r)` big-endian at byte
`tp + 6142 − 8e − 2r`): `e < 256` and `e ≥ 512` hold `1023 − t1_r[e mod 256]`,
`256 ≤ e < 512` hold `t1_r[e − 256]` (`TTable`, `Fn/TBuild/Defs.lean`). Call sites:
`(0x5000, 32)` (rows 0–3) and `(0x6800, 0x520)` (rows 4–7, `t1f_520`).
-/

namespace MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **tbuild**: `[tp, off, ret]`; table at `[tp, tp + 6144)`, rows read from calldata
`[off, off + 1280)`. -/
theorem tbuild_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.tbuild ret tail) (m : ByteArray) {tp off : Nat} (htp : tp + 6144 ≤ 65536)
    (hcd : off + 1280 ≤ s.executionEnv.calldata.size) :
    ∃ m', TTable m' tp off s.executionEnv.calldata ∧
      FrameExcept m m' [(tp, tp + 6144)] ∧
      Call s Entry.tbuild [wd tp, wd off] ret tail m [] m' Gas.tbuild :=
  TB.tbuild_main hs hr m htp hcd

end MlDsaOpt65.Proofs
