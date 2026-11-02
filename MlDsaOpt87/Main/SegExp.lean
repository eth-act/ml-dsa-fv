import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Group
import MlDsaOpt87.Fn.Sponge
/-! # Segment `3371 … 5551`: ExpandA (v4, open)

All fifteen groups: the ten pure groups `group [15, s, rb]` (rows 0–3 of
columns 0–6, rows 4–7 of columns 0–2), the mixed groups 10–13 (rows 4–6 of
columns 3–6, the `tr` rider in slot 3, `TRL` after group 13) and the
Kronecker group 14 (row 7, columns 3–6); the copies of `ABUF` to the side
buffers `CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000`, and the fused passes
`pass3f4`, `pass3f6`, `pass3f10`, `pass3f14` into `ACC`. One segment for now;
the v3 group proofs (`Main/SegGroups.lean`, `Main/SegMixed.lean`,
`Main/SegKron.lean`, `Main/S{3,5}`, removed in the v4 retarget) show the shape
of its parts. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

theorem seg_exp {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3371 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 5551 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp := by
  sorry

end MlDsaOpt87.Proofs
