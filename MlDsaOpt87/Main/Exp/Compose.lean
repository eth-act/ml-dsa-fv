import MlDsaOpt87.Main.Exp.Pure
import MlDsaOpt87.Main.Exp.G14
set_option warningAsError true
/-!
# ExpandA from its three sub-segments (ML-DSA-87, v4)

`3371 … 3612` (`exp_pure`, groups 0–9, `Exp.MixIn`), `3612 … 5394` (the mixed
groups 10–13, `Exp.InvG14`; a hypothesis here), `5394 … 5551` (group 14,
`pass3f14`, `exp_g14`, `InvW`); the fifteen flags compose to `okZ ∧ okA`
(`flags_okA`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Exp

theorem seg_exp_of {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) {c1013 : Nat}
    (H : ∀ (m : ByteArray) (b : Bool), MixIn s.executionEnv.calldata m →
      ∃ m', InvG14 s.executionEnv.calldata m' ∧
        Reach (callState s 3612 [flag b] m)
          (callState s 5394 [flag (mixFlag s.executionEnv.calldata b)] m') c1013)
    (hc : pureCost + c1013 + gG14 ≤ Gas.pExp) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3371 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 5551 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
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

end MlDsaOpt87.Proofs
