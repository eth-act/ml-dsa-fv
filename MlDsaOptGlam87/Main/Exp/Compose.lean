import MlDsaOptGlam87.Main.Exp.Pure
import MlDsaOptGlam87.Main.Exp.G14
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/Exp/Compose.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# ExpandA from its three sub-segments (ML-DSA-87, v4)

`3371 … 3612` (`exp_pure`, groups 0–9, `Exp.MixIn`), `3612 … 5394` (the mixed
groups 10–13, `Exp.InvG14`; a hypothesis here), `5394 … 4510` (group 14,
`pass3f14`, `exp_g14`, `InvW`); the fifteen flags compose to `okZ ∧ okA`
(`flags_okA`).
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Exp

open MlDsaOpt87.Proofs

theorem seg_exp_of {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) {c1013 : Nat}
    (H : ∀ (m : ByteArray) (b : Bool), MixIn s.executionEnv.calldata m →
      ∃ m', InvG14 s.executionEnv.calldata m' ∧
        Reach (callState s 2571 [flag b] m)
          (callState s 4353 [flag (mixFlag s.executionEnv.calldata b)] m') c1013)
    (hc : pureCost + c1013 + gG14 ≤ Gas.pExp) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 2330 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 4510 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp := by
  obtain ⟨m1, h1, r1⟩ := exp_pure hs hcd (invE_of_inv4 hI) (okZ s.executionEnv.calldata)
  obtain ⟨m2, h2, r2⟩ := H m1 _ h1
  obtain ⟨m3, h3, r3⟩ := exp_g14 hs hcd h2 _
  refine ⟨m3, h3, ?_⟩
  have e : (mixFlag s.executionEnv.calldata (pureFlag s.executionEnv.calldata (okZ s.executionEnv.calldata)) &&
      okRow7 s.executionEnv.calldata) = (okZ s.executionEnv.calldata && okA s.executionEnv.calldata) := by
    unfold mixFlag pureFlag; exact flags_okA _ _
  rw [← e]
  exact ((r1.trans r2).trans r3).mono hc

end Exp

end MlDsaOptGlam87.Proofs
