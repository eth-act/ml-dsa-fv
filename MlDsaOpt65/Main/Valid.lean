import MlDsaOpt65.Main.Short
import MlDsaOpt65.Main.SegInit
import MlDsaOpt65.Main.SegZh
import MlDsaOpt65.Main.SegTbl
import MlDsaOpt65.Main.SegNtt
import MlDsaOpt65.Main.SegRho
import MlDsaOpt65.Main.SegGroups
import MlDsaOpt65.Main.SegG5
import MlDsaOpt65.Main.SegG6
import MlDsaOpt65.Main.SegG7
import MlDsaOpt65.Main.SegG8
import MlDsaOpt65.Main.SegMu
import MlDsaOpt65.Main.SegSib
import MlDsaOpt65.Main.SegCt
import MlDsaOpt65.Main.SegW
import MlDsaOpt65.Main.SegFin
set_option warningAsError true
/-!
# The full verification path (ML-DSA-65)

`valid_trace`: from any frame entry with calldata of at least `|pk| + |σ| = 5261`
bytes, the segments of `Main/Seg*.lean` compose to a `RETURN` of the
verification word within `Gas.schedule`.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- Flag of ExpandA group `n < 10` (code order): rows `0 … 3` of column `n` for
`n < 5`, rows 4, 5 of column `n − 5` otherwise. -/
def gCol (cd : ByteArray) (n : Nat) : Bool := if n < 5 then okCol0 cd n else okCol1 cd (n - 5)

/-- The flag on the stack after `n` ExpandA groups. -/
def gFlags (cd : ByteArray) : Nat → Bool
  | 0 => ok1 cd
  | n + 1 => gFlags cd n && gCol cd n

/-- The flags of the ten ExpandA groups, accumulated in code order, are `okA`. -/
theorem flags_eq (cd : ByteArray) : gFlags cd 10 = ok2 cd := by
  simp only [gFlags, gCol, ok2, okA, okCol0, okCol1,
    show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.all_cons, List.all_nil, Bool.and_true]
  simp only [show (0 : Nat) < 5 from by decide, show (1 : Nat) < 5 from by decide,
    show (2 : Nat) < 5 from by decide, show (3 : Nat) < 5 from by decide,
    show (4 : Nat) < 5 from by decide, show ¬ (5 : Nat) < 5 from by decide,
    show ¬ (6 : Nat) < 5 from by decide, show ¬ (7 : Nat) < 5 from by decide,
    show ¬ (8 : Nat) < 5 from by decide, show ¬ (9 : Nat) < 5 from by decide, if_true, if_false]
  ac_rfl

/-- The returned bit is the bytecode-flow verdict. -/
theorem result_bit (cd : ByteArray) (E : Bool) (m : ByteArray) (hI : Inv9 cd m)
    (hE : ∀ X : ByteArray, X.size = 832 → FinAt m X → E = (ctOf cd == Fips204.H X 48)) :
    (ok3 cd && E) = optAccepts cd := by
  cases h3 : ok3 cd with
  | false =>
    unfold optAccepts
    simp only [ok3, ok2, ok1] at h3
    simp [h3]
  | true =>
    rw [hE _ (finBytes_size cd) (hI.fin h3)]
    unfold optAccepts
    simp only [ok3, ok2, ok1] at h3
    simp [h3]

/-- The total cost of the valid path is the schedule. -/
theorem valid_cost (size : Nat) (h : 5261 ≤ size) :
    Gas.pInit + MachineState.memCost memWords + Gas.pZh + Gas.pTbl + Gas.pNtt + Gas.pRho +
        Gas.pG0 + Gas.pG1 + Gas.pG2 + Gas.pG3 + Gas.pG4 + Gas.pG5 + Gas.pG6 + Gas.pG7 + Gas.pG8 +
        Gas.pG9 + Gas.pMu (size - 5261) + Gas.pSib + Gas.pCt + Gas.pW + Gas.pFin ≤
      Gas.schedule size := by
  unfold Gas.schedule
  rw [if_neg (by omega)]

theorem valid_trace {s₀ : State} (h0 : Ctx0 s₀) (haw : s₀.activeWords.toNat = 0)
    (hpc : callState s₀ 0 [] .empty = s₀)
    (hfit : s₀.executionEnv.calldata.size < 2 ^ 64) (hlen : 5261 ≤ s₀.executionEnv.calldata.size) :
    ∃ final : State, ∃ g : EvmProof.GasSteps s₀ final,
      g.cost ≤ Gas.schedule s₀.executionEnv.calldata.size ∧ final.halt = .Returned ∧
        final.hReturn = MlDsa65.spec s₀.executionEnv.calldata ∧ FrameLocal s₀ final := by
  obtain ⟨m0, hI0, hR0⟩ := seg_init h0 haw hlen hfit
  have hR0' := hR0.of_eq hpc rfl
  have hs : Ctx (sized s₀) := sized_ctx h0 hfit
  have hcd : (sized s₀).executionEnv.calldata = s₀.executionEnv.calldata := rfl
  generalize hs1 : sized s₀ = s₁ at hs hR0' hcd
  have hlen1 : HDR ≤ s₁.executionEnv.calldata.size := by rw [hcd]; exact hlen
  obtain ⟨m1, hI1, hR1⟩ := seg_zh hs hlen1 hI0
  obtain ⟨m2, hI2, hR2⟩ := seg_tbl hs hI1 (ok1 s₁.executionEnv.calldata)
  obtain ⟨m3, hI3, hR3⟩ := seg_ntt hs hI2 (ok1 s₁.executionEnv.calldata) hlen1
  obtain ⟨m4, hI4, hR4⟩ := seg_rho hs hI3 (ok1 s₁.executionEnv.calldata)
  obtain ⟨m5, hI5, hR5⟩ := seg_g0 hs hlen1 hI4 (gFlags s₁.executionEnv.calldata 0)
  obtain ⟨m6, hI6, hR6⟩ := seg_g1 hs hlen1 hI5 (gFlags s₁.executionEnv.calldata 1)
  obtain ⟨m7, hI7, hR7⟩ := seg_g2 hs hlen1 hI6 (gFlags s₁.executionEnv.calldata 2)
  obtain ⟨m8, hI8, hR8⟩ := seg_g3 hs hlen1 hI7 (gFlags s₁.executionEnv.calldata 3)
  obtain ⟨m9, hI9, hR9⟩ := seg_g4 hs hlen1 hI8 (gFlags s₁.executionEnv.calldata 4)
  obtain ⟨m10, hI10, hR10⟩ := seg_g5 hs hlen1 hI9 (gFlags s₁.executionEnv.calldata 5)
  obtain ⟨m11, hI11, hR11⟩ := seg_g6 hs hlen1 hI10 (gFlags s₁.executionEnv.calldata 6)
  obtain ⟨m12, hI12, hR12⟩ := seg_g7 hs hlen1 hI11 (gFlags s₁.executionEnv.calldata 7)
  obtain ⟨m13, hI13, hR13⟩ := seg_g8 hs hlen1 hI12 (gFlags s₁.executionEnv.calldata 8)
  obtain ⟨m14, hI14, hR14⟩ := seg_g9 hs hlen1 hI13 (gFlags s₁.executionEnv.calldata 9)
  have hR14' : Reach (callState s₁ 5221 [flag (gFlags s₁.executionEnv.calldata 9)] m13)
      (callState s₁ 5236 [flag (ok2 s₁.executionEnv.calldata)] m14) Gas.pG9 := by
    rw [← flags_eq]; exact hR14
  obtain ⟨m15, hI15, hR15⟩ := seg_mu hs hlen1 hI14 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m16, hI16, hR16⟩ := seg_sib hs hI15 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m17, hI17, hR17⟩ := seg_ct hs hlen1 hI16 (ok2 s₁.executionEnv.calldata && okC
    s₁.executionEnv.calldata)
  obtain ⟨m18, hI18, hR18⟩ := seg_w hs hlen1 hI17 (ok2 s₁.executionEnv.calldata && okC
    s₁.executionEnv.calldata)
  obtain ⟨E, pc, stk, m19, hE, hR19⟩ := seg_fin hs hlen1 hI18.rc1 (ok2 s₁.executionEnv.calldata &&
    okC s₁.executionEnv.calldata)
  have hbit : ((ok2 s₁.executionEnv.calldata && okC s₁.executionEnv.calldata) && E) = optAccepts
    s₁.executionEnv.calldata := result_bit _ E m18 hI18 hE
  have h := ((((((((((((((((((hR0'.trans hR1).trans hR2).trans hR3).trans hR4).trans hR5).trans
    hR6).trans hR7).trans hR8).trans hR9).trans hR10).trans hR11).trans hR12).trans hR13).trans
    hR14').trans hR15).trans hR16).trans hR17).trans hR18).trans hR19
  obtain ⟨g, hg⟩ := h
  refine ⟨_, g, ?_, rfl, ?_, ?_⟩
  · refine hg.trans ?_
    have e : mlenOf s₁.executionEnv.calldata = s₀.executionEnv.calldata.size - 5261 := by
      rw [hcd]; rfl
    rw [e]
    exact valid_cost s₀.executionEnv.calldata.size hlen
  · change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hbit, ← hcd,
      ← accepts_eq_optAccepts _ (by rw [hcd]; exact hlen)]
  · rw [← hs1]
    rfl

end MlDsaOpt65.Proofs
