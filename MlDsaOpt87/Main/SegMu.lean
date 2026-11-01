import MlDsaOpt87.Main.Base
/-! # Segment `5593 … 6591`: μ by `kf1` (`hash_mu`) -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `5593 … 6591`, open: `KS[x] := cpl x (rep TRL[x])` (`x < 8`), `hash_mu`:
zero lanes 8–24, absorb `0 ‖ 0 ‖ M[0, 70)` inline, loop `(66 + |M|) / 136`
times `kf1` + `absorb17`, pad, `kf1`, `FIN[x] := rep μ_x` (`FinMu`). Needs
"`kf1` sponge = `Fips202.absorb`" and `le64_trOf`. Mirror the long-message
branch of `MlDsaOpt44/Main/SegMu.lean` + `Main/Mu/*` (no `|M| ≤ 69` branch). -/
theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv6 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 5593 [flag b] m) (callState s 6591 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry

end MlDsaOpt87.Proofs
