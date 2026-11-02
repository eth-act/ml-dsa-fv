import MlDsaOpt65.Main.Exp.Pure
set_option warningAsError true
/-!
# ExpandA from its three sub-segments (ML-DSA-65, v4)

`3556 … 3674` (`exp_pure`), `3674 … 5022` (groups 5–7, `Exp.InvG8`),
`5022 … 5242` (group 8, `pass3f8`, `InvW`); the flags compose to `okZ ∧ okA`
(`okA_eq`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Exp

theorem seg_exp_of {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) {c57 c8 : Nat}
    (H57 : ∀ (m : ByteArray) (b : Bool), PureOut s.executionEnv.calldata m →
      ∃ m', InvG8 s.executionEnv.calldata m' ∧
        Reach (callState s 3674 [flag b] m)
          (callState s 5022 [flag (b && okIUpTo s.executionEnv.calldata 9)] m') c57)
    (H8 : ∀ (m : ByteArray) (b : Bool), InvG8 s.executionEnv.calldata m →
      ∃ m', InvW s.executionEnv.calldata m' ∧
        Reach (callState s 5022 [flag b] m)
          (callState s 5242 [flag (b && okI s.executionEnv.calldata 9)] m') c8)
    (hc : gPure + 5 * Gas.group + Gas.pass3f4 + c57 + c8 ≤ Gas.pExp) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3556 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 5242 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp := by
  obtain ⟨m1, h1, r1⟩ := exp_pure hs hcd hI (okZ s.executionEnv.calldata)
  obtain ⟨m2, h2, r2⟩ := H57 m1 _ h1
  obtain ⟨m3, h3, r3⟩ := H8 m2 _ h2
  refine ⟨m3, h3, ?_⟩
  have e : (okZ s.executionEnv.calldata && okA s.executionEnv.calldata) =
      (((okZ s.executionEnv.calldata && okUpTo0 s.executionEnv.calldata 5) &&
        okIUpTo s.executionEnv.calldata 9) && okI s.executionEnv.calldata 9) := by
    rw [okA_eq]; simp only [Bool.and_assoc]
  rw [e]
  exact ((r1.trans r2).trans r3).mono (by omega)

end Exp

end MlDsaOpt65.Proofs
