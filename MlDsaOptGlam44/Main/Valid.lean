import MlDsaOptGlam44.Main.Short
import MlDsaOptGlam44.Main.SegInit
import MlDsaOptGlam44.Main.SegZ
import MlDsaOptGlam44.Main.SegTbl
import MlDsaOptGlam44.Main.SegNtt
import MlDsaOptGlam44.Main.SegRho
import MlDsaOptGlam44.Main.SegGroups
import MlDsaOptGlam44.Main.SegG2
import MlDsaOptGlam44.Main.SegWin
import MlDsaOptGlam44.Main.SegZd
import MlDsaOptGlam44.Main.SegMu
import MlDsaOptGlam44.Main.SegSib
import MlDsaOptGlam44.Main.SegCt
import MlDsaOptGlam44.Main.SegW
import MlDsaOptGlam44.Main.SegFin
import MlDsaOptGlam44.Main.SegSwitch
import MlDsaOptGlam44.Gas
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/Valid.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# The full verification path

`valid_trace`: from any frame entry with calldata of at least `|pk| + |σ|`
bytes, the segments compose to a `RETURN` of the verification word within
`Gas.schedule`. Glamsterdam: after ExpandA's second group the long-message
switch (`Main/SegSwitch.lean`) selects the packed schedule (`|M| < 342`,
`packed_tail`: v4's segments) or the long-message schedule (`seg_alt`, an
**open item**); both reach `6030` (after SampleInBall) with `Inv7`.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

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

/-- **Open item** (glam): `2436 … 6030` on the long-message schedule
(`|M| ≥ 342`): the jump to `alt`, the previous schedule's groups (the last one
carrying up to five μ blocks through `mub` / `mulong`), `pass3f4b`, the shared
code with `FLAG = 0` (`dhint`, `hash_mu` from `muimg`, SampleInBall with c's
second block already squeezed). -/
theorem seg_alt {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (hge : 4074 ≤ s.executionEnv.calldata.size) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 2436
          [flag ((okZ s.executionEnv.calldata && okCol s.executionEnv.calldata 0) &&
            okCol s.executionEnv.calldata 1)] m)
        (callState s 6030 [flag (ok2 s.executionEnv.calldata && okC s.executionEnv.calldata)] m')
        (Gas.pAlt (mlenOf s.executionEnv.calldata)) := by
  sorry  -- glam: open item (the long-message schedule)

/-- `2436 … 6030` on the packed schedule (`|M| < 342`): the switch, v4's group 2,
window, the jump to the shared code, the side buffers and hints, μ and
SampleInBall. -/
theorem packed_tail {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (hlt : s.executionEnv.calldata.size < 4074) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 2436
          [flag ((okZ s.executionEnv.calldata && okCol s.executionEnv.calldata 0) &&
            okCol s.executionEnv.calldata 1)] m)
        (callState s 6030 [flag (ok2 s.executionEnv.calldata && okC s.executionEnv.calldata)] m')
        (Gas.pPacked (mlenOf s.executionEnv.calldata)) := by
  obtain ⟨m1, hI1, hf1, hR1⟩ := seg_switch hs hI _ hlt
  obtain ⟨m2, hI2, hR2⟩ := seg_g2 hs hcd hI1 _ hf1
  obtain ⟨m3, hI3, hR3⟩ := seg_win hs hcd hI2
  have hR3' := seg_join hs (m := m3) (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)
  obtain ⟨m4, hI4, hR4⟩ := seg_zd hs hcd hI3 (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)
  obtain ⟨m5, hI5, hR5⟩ := seg_mu hs hcd hI4 (ok2 s.executionEnv.calldata)
  obtain ⟨m6, hI6, hR6⟩ := seg_sib hs hcd hI5 (ok2 s.executionEnv.calldata)
  refine ⟨m6, hI6, ?_⟩
  have h := hR1.trans hR2 |>.trans hR3 |>.trans hR3' |>.trans hR4 |>.trans hR5 |>.trans hR6
  exact h.mono (le_of_eq (by unfold Gas.pPacked; rfl))

/-- The total cost of the valid path is the schedule. -/
theorem valid_cost (size : Nat) (h : 3732 ≤ size) :
    Gas.pInit + MachineState.memCost memWords + Gas.pZ + Gas.pTbl +
        Gas.pNtt + Gas.pRho + Gas.pG0 + Gas.pG1 +
        (if size - 3732 < 342 then Gas.pPacked (size - 3732) else Gas.pAlt (size - 3732)) +
        Gas.pCt + Gas.pW + Gas.pFin ≤
      Gas.schedule size := by
  unfold Gas.schedule
  rw [if_neg (show ¬ size < 3732 by omega)]

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
  -- the long-message switch
  have hT : ∃ m11, Inv7 s₁.executionEnv.calldata m11 ∧
      Reach (callState s₁ 2436
          [flag ((okZ s₁.executionEnv.calldata && okCol s₁.executionEnv.calldata 0) &&
            okCol s₁.executionEnv.calldata 1)] m6)
        (callState s₁ 6030 [flag (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)] m11)
        (if s₁.executionEnv.calldata.size - 3732 < 342 then Gas.pPacked (s₁.executionEnv.calldata.size - 3732)
          else Gas.pAlt (s₁.executionEnv.calldata.size - 3732)) := by
    by_cases hm : s₁.executionEnv.calldata.size - 3732 < 342
    · obtain ⟨m11, hI11, hR11⟩ := packed_tail hs hlen1 hI6 (by unfold HDR at hlen1; omega)
      exact ⟨m11, hI11, by rw [if_pos hm]; exact hR11⟩
    · obtain ⟨m11, hI11, hR11⟩ := seg_alt hs hlen1 hI6 (by unfold HDR at hlen1; omega)
      exact ⟨m11, hI11, by rw [if_neg hm]; exact hR11⟩
  obtain ⟨m11, hI11, hR11⟩ := hT
  obtain ⟨m12, hI12, hR12⟩ := seg_ct hs hlen1 hI11
    (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)
  obtain ⟨m13, hI13, hR13⟩ := seg_w hs hlen1 hI12
    (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)
  obtain ⟨E, pc, stk, m14, hE, hR14⟩ := seg_fin hs hlen1 hI13.rc1
    (ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata)
  have hbit : ((ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata) && E) =
      optAccepts s₁.executionEnv.calldata := result_bit _ E m13 hI13 hE
  have h := hR0'.trans hR1 |>.trans hR2 |>.trans hR3 |>.trans hR4 |>.trans hR5 |>.trans hR6
    |>.trans hR11 |>.trans hR12 |>.trans hR13 |>.trans hR14
  obtain ⟨g, hg⟩ := h
  refine ⟨_, g, ?_, rfl, ?_, ?_⟩
  · refine hg.trans ?_
    have := valid_cost s₀.executionEnv.calldata.size hlen
    rw [← hcd]
    rw [hcd]
    omega
  · change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hbit, ← hcd,
      ← accepts_eq_optAccepts _ (by rw [hcd]; exact hlen)]
  · rw [← hs1]
    rfl

end MlDsaOptGlam44.Proofs
