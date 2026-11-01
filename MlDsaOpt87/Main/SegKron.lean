import MlDsaOpt87.Main.Base
import MlDsaOpt87.Main.S5.G14
/-! # Segment `5435 … 5593`: the Kronecker group 14 (row 7, columns 3–6) -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `5435 … 5593`: `HAVE6 := 0`, `ginit [0, 15, 0, l4]` with the seeds of
`A[7][6], A[7][5], A[7][4], A[7][3]` in slots 0–3, five `kf4` + `blk`, `gfix 15`
(flag `okRow7`), `pass3k14` (`pass3k14_call`: lane 3 of `ACC + 0x2000` gains
`Σ_{i<4} A[7][3+i][t] · ẑ_{3+i}[t]`, lanes 0–2 unchanged). Then `AccAt`:
under `okA` every guard of `InvTr` holds, both accumulator tables hold the
exact sums over all seven columns (`< 7 · 2^23 · 2^28 < 2^58`), and
`accSum ≡ azRow (mod q)` by `ZHatAt` (as the end of `MlDsaOpt44/Main/SegG234`). Proof: `Main/S5/G14`, `Main/S5/Acc`. -/
theorem seg_g14 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvTr s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5435 [flag b] m)
        (callState s 5593 [flag (b && okRow7 s.executionEnv.calldata)] m') Gas.pG14 :=
  s5_seg_g14 hs hcd hI b

end MlDsaOpt87.Proofs
