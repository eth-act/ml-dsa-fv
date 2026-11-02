import MlDsaOpt44.Main.Short
import MlDsaOpt44.Main.SegInit
import MlDsaOpt44.Main.SegZ
import MlDsaOpt44.Main.SegTbl
import MlDsaOpt44.Main.SegNtt
import MlDsaOpt44.Main.SegRho
import MlDsaOpt44.Main.SegGroups
import MlDsaOpt44.Main.SegG2
import MlDsaOpt44.Main.SegWin
import MlDsaOpt44.Main.SegZd
import MlDsaOpt44.Main.SegMu
import MlDsaOpt44.Main.SegSib
import MlDsaOpt44.Main.SegCt
import MlDsaOpt44.Main.SegW
import MlDsaOpt44.Main.SegFin
set_option warningAsError true
/-!
# The full verification path

`valid_trace`: from any frame entry with calldata of at least `|pk| + |σ|`
bytes, the segments of `Main/Segments.lean` compose to a `RETURN` of the
verification word within `Gas.schedule`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem all_all_comm {α β : Type} (l₁ : List α) (l₂ : List β) (p : α → β → Bool) :
    (l₁.all fun a => l₂.all fun b => p a b) = (l₂.all fun b => l₁.all fun a => p a b) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun h b hb a ha => h a ha b hb, fun h a ha b hb => h b hb a ha⟩

/-- The returned bit is the bytecode-flow verdict. -/
theorem result_bit (cd : ByteArray) (E : Bool) (m : ByteArray) (hI : Inv9 cd m)
    (hE : ∀ X : ByteArray, X.size = 832 → FinAt m X → E = (ctOf cd == Fips204.H X 32)) :
    (ok3 cd && E) = optAccepts cd := by
  cases h3 : ok3 cd with
  | false =>
    unfold optAccepts
    simp only [ok3, ok2] at h3
    revert h3
    cases okZ cd <;> cases okH cd <;> cases okA cd <;> cases okC cd <;> simp
  | true =>
    rw [hE _ (finBytes_size cd) (hI.fin h3)]
    unfold optAccepts
    simp only [ok3, ok2, Bool.and_eq_true] at h3
    simp [h3]

/-- The total cost of the valid path is the schedule. -/
theorem valid_cost (size : Nat) (h : 3732 ≤ size) :
    Gas.pInit + MachineState.memCost memWords + Gas.pZ + Gas.pTbl +
        Gas.pNtt + Gas.pRho + Gas.pG0 + Gas.pG1 + Gas.pG2 + Gas.pWin + Gas.pZd + Gas.pMu (size - 3732) +
        Gas.pSib + Gas.pCt + Gas.pW + Gas.pFin ≤
      Gas.schedule size := by
  unfold Gas.schedule
  rw [if_neg (by omega)]

theorem valid_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hpc : callState s₀ 0 [] .empty = s₀)
    (hfit : s₀.executionEnv.calldata.size < 2 ^ 64) (hlen : 3732 ≤ s₀.executionEnv.calldata.size) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s₀ final,
      g.cost ≤ Gas.schedule s₀.executionEnv.calldata.size ∧ final.halt = .Returned ∧
        final.hReturn = spec s₀.executionEnv.calldata ∧ FrameLocal s₀ final := by
  obtain ⟨m0, hI0, hR0⟩ := seg_init h0 haw hlen hfit
  have hR0' := hR0.of_eq hpc rfl
  have hs : Ctx (sized s₀) := sized_ctx h0 hfit
  have hcd : (sized s₀).executionEnv.calldata = s₀.executionEnv.calldata := rfl
  generalize hs1 : sized s₀ = s₁ at hs hR0' hcd
  have hlen1 : HDR ≤ s₁.executionEnv.calldata.size := by rw [hcd]; exact hlen
  obtain ⟨m1, hI1, hR1⟩ := seg_z hs hlen1 hI0
  obtain ⟨m2, hI2, hR2⟩ := seg_tbl hs hI1 (okZ s₁.executionEnv.calldata)
  obtain ⟨m3, hI3, hR3⟩ := seg_ntt hs hI2 (okZ s₁.executionEnv.calldata) hlen1
  obtain ⟨m4, hI4, hR4⟩ := seg_rho hs hI3 (okZ s₁.executionEnv.calldata)
  obtain ⟨m5, hI5, hR5⟩ := seg_g0 hs hlen1 hI4 (okZ s₁.executionEnv.calldata)
  obtain ⟨m6, hI6, hR6⟩ := seg_g1 hs hlen1 hI5
    (okZ s₁.executionEnv.calldata && okCol s₁.executionEnv.calldata 0)
  obtain ⟨m7, hI7, hR7⟩ := seg_g2 hs hlen1 hI6
    ((okZ s₁.executionEnv.calldata && okCol s₁.executionEnv.calldata 0) &&
      okCol s₁.executionEnv.calldata 1)
  obtain ⟨m8, hI8, hR8⟩ := seg_win hs hlen1 hI7
  obtain ⟨m9, hI9, hR9⟩ := seg_zd hs hlen1 hI8
    (okZ s₁.executionEnv.calldata && okA s₁.executionEnv.calldata)
  obtain ⟨m10, hI10, hR10⟩ := seg_mu hs hlen1 hI9 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m11, hI11, hR11⟩ := seg_sib hs hlen1 hI10 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m12, hI12, hR12⟩ := seg_ct hs hlen1 hI11
    (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)
  obtain ⟨m13, hI13, hR13⟩ := seg_w hs hlen1 hI12
    (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)
  obtain ⟨E, pc, stk, m14, hE, hR14⟩ := seg_fin hs hlen1 hI13.rc1
    (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)
  have hbit : ((ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata) && E) =
      optAccepts s₁.executionEnv.calldata := result_bit _ E m13 hI13 hE
  have h := hR0'.trans hR1 |>.trans hR2 |>.trans hR3 |>.trans hR4 |>.trans hR5 |>.trans hR6
    |>.trans hR7 |>.trans hR8 |>.trans hR9 |>.trans hR10 |>.trans hR11 |>.trans hR12 |>.trans hR13
    |>.trans hR14
  obtain ⟨g, hg⟩ := h
  refine ⟨_, g, ?_, rfl, ?_, ?_⟩
  · refine hg.trans ?_
    have := valid_cost s₀.executionEnv.calldata.size hlen
    rw [← hcd]
    unfold mlenOf
    rw [hcd]
    omega
  · change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hbit, ← hcd,
      ← accepts_eq_optAccepts _ (by rw [hcd]; exact hlen)]
  · rw [← hs1]
    rfl

end MlDsaOpt44.Proofs
