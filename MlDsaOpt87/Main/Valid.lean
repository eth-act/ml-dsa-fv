import MlDsaOpt87.Main.Short
import MlDsaOpt87.Main.SegInit
import MlDsaOpt87.Main.SegZ
import MlDsaOpt87.Main.SegTbl
import MlDsaOpt87.Main.SegNtt
import MlDsaOpt87.Main.SegRho
import MlDsaOpt87.Main.SegExp
import MlDsaOpt87.Main.SegZd
import MlDsaOpt87.Main.SegMu
import MlDsaOpt87.Main.SegSib
import MlDsaOpt87.Main.SegCt
import MlDsaOpt87.Main.SegW
import MlDsaOpt87.Main.SegFin
set_option warningAsError true
/-!
# The full verification path (ML-DSA-87)

`valid_trace`: from any frame entry with calldata of at least `|pk| + |σ|`
bytes, the segments of `Main/Seg*.lean` compose to a `RETURN` of the
verification word within `Gas.schedule`.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsa87

/-- The returned bit is the bytecode-flow verdict. -/
theorem result_bit (cd : ByteArray) (E : Bool) (m : ByteArray) (hI : Inv9 cd m)
    (hE : ∀ X : ByteArray, X.size = 1088 → FinAt m X → E = (ctOf cd == Fips204.H X 64)) :
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

/-- The total cost of the valid path (segments in program order) is the schedule. -/
theorem valid_cost (size : Nat) (h : 7219 ≤ size) :
    Gas.pInit + MachineState.memCost memWords + Gas.pZ + Gas.pTbl + Gas.pNtt + Gas.pRho +
        Gas.pExp + Gas.pZd + Gas.pMu (size - 7219) + Gas.pSib + Gas.pCt + Gas.pW + Gas.pFin ≤
      Gas.schedule size := by
  unfold Gas.schedule
  rw [if_neg (by omega)]
  exact le_of_eq (by ac_rfl)

theorem valid_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hpc : callState s₀ 0 [] .empty = s₀)
    (hfit : s₀.executionEnv.calldata.size < 2 ^ 64) (hlen : 7219 ≤ s₀.executionEnv.calldata.size) :
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
  obtain ⟨m4, hI4, hR4⟩ := seg_rho hs hlen1 hI3 (okZ s₁.executionEnv.calldata)
  obtain ⟨m5, hI5, hR5⟩ := seg_exp hs hlen1 hI4
  obtain ⟨m6, hI6, hR6⟩ := seg_zd hs hlen1 hI5
    (okZ s₁.executionEnv.calldata && okA s₁.executionEnv.calldata)
  obtain ⟨m7, hI7, hR7⟩ := seg_mu hs hlen1 hI6 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m8, hI8, hR8⟩ := seg_sib hs hlen1 hI7 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m9, hI9, hR9⟩ := seg_ct hs hlen1 hI8 (ok2 s₁.executionEnv.calldata && okC
    s₁.executionEnv.calldata)
  obtain ⟨m10, hI10, hR10⟩ := seg_w hs hlen1 hI9 (ok2 s₁.executionEnv.calldata && okC
    s₁.executionEnv.calldata)
  obtain ⟨E, pc, stk, m11, hE, hR11⟩ := seg_fin hs hlen1 hI10.rc1 (ok2 s₁.executionEnv.calldata &&
    okC s₁.executionEnv.calldata)
  have hbit : ((ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata) && E) = optAccepts
    s₁.executionEnv.calldata := result_bit _ E m10 hI10 hE
  have h := hR0'.trans hR1 |>.trans hR2 |>.trans hR3 |>.trans hR4 |>.trans hR5 |>.trans hR6
    |>.trans hR7 |>.trans hR8 |>.trans hR9 |>.trans hR10 |>.trans hR11
  obtain ⟨g, hg⟩ := h
  refine ⟨_, g, ?_, rfl, ?_, ?_⟩
  · refine hg.trans ?_
    have e : mlenOf s₁.executionEnv.calldata = s₀.executionEnv.calldata.size - 7219 := by
      rw [hcd]; rfl
    rw [e]
    exact valid_cost s₀.executionEnv.calldata.size hlen
  · change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hbit, ← hcd,
      ← accepts_eq_optAccepts _ (by rw [hcd]; exact hlen)]
  · rw [← hs1]
    rfl

end MlDsaOpt87.Proofs
