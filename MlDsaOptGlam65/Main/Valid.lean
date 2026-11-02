import MlDsaOptGlam65.Main.Short
import MlDsaOptGlam65.Main.SegInit
import MlDsaOptGlam65.Main.SegZ
import MlDsaOptGlam65.Main.SegTbl
import MlDsaOptGlam65.Main.SegNtt
import MlDsaOptGlam65.Main.SegRho
import MlDsaOptGlam65.Main.SegExp
import MlDsaOptGlam65.Main.SegZd
import MlDsaOptGlam65.Main.SegMu
import MlDsaOptGlam65.Main.SegSib
import MlDsaOptGlam65.Main.SegCt
import MlDsaOptGlam65.Main.SegW
import MlDsaOptGlam65.Main.SegFin
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/Valid.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# The full verification path (ML-DSA-65)

`valid_trace`: from any frame entry with calldata of at least `|pk| + |σ| = 5261`
bytes, the segments of `Main/Seg*.lean` compose to a `RETURN` of the
verification word within `Gas.schedule`.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- Flag of ExpandA group `n < 9` (code order): rows `0 … 3` of column `n` for
`n < 5`, the row-group-1 instances `3 (n − 5) … 3 (n − 5) + 2` for groups 5–7
and instance 9 for group 8 (`okI`). -/
def gCol (cd : ByteArray) (n : Nat) : Bool :=
  if n < 5 then okCol0 cd n
  else if n < 8 then okI cd (3 * (n - 5)) && okI cd (3 * (n - 5) + 1) && okI cd (3 * (n - 5) + 2)
  else okI cd 9

/-- The flag on the stack after `n` ExpandA groups. -/
def gFlags (cd : ByteArray) : Nat → Bool
  | 0 => okZ cd
  | n + 1 => gFlags cd n && gCol cd n

/-- The flags of the nine ExpandA groups, accumulated in code order, are `okA`. -/
theorem flags_eq (cd : ByteArray) : gFlags cd 9 = (okZ cd && okA cd) := by
  simp only [gFlags, gCol, okA, okCol0, okI,
    show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, show List.range 5 = [0, 1, 2, 3, 4] from rfl,
    List.all_cons, List.all_nil, Bool.and_true, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul,
    Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, if_true, if_false]
  ac_rfl

/-- The returned bit is the bytecode-flow verdict. -/
theorem result_bit (cd : ByteArray) (E : Bool) (m : ByteArray) (hI : Inv9 cd m)
    (hE : ∀ X : ByteArray, X.size = 832 → FinAt m X → E = (ctOf cd == Fips204.H X 48)) :
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
theorem valid_cost (size : Nat) (h : 5261 ≤ size) :
    Gas.pInit + MachineState.memCost memWords + Gas.pZ + Gas.pTbl + Gas.pNtt + Gas.pRho +
        Gas.pExp + Gas.pZd + Gas.pMu (size - 5261) + Gas.pSib + Gas.pCt + Gas.pW + Gas.pFin ≤
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
  obtain ⟨m1, hI1, hR1⟩ := seg_z hs hlen1 hI0
  obtain ⟨m2, hI2, hR2⟩ := seg_tbl hs hI1 (okZ s₁.executionEnv.calldata)
  obtain ⟨m3, hI3, hR3⟩ := seg_ntt hs hI2 (okZ s₁.executionEnv.calldata) hlen1
  obtain ⟨m4, hI4, hR4⟩ := seg_rho hs hI3 (okZ s₁.executionEnv.calldata)
  obtain ⟨m5, hI5, hR5⟩ := seg_exp hs hlen1 hI4
  obtain ⟨m6, hI6, hR6⟩ := seg_zd hs hlen1 hI5
    (okZ s₁.executionEnv.calldata && okA s₁.executionEnv.calldata)
  obtain ⟨m7, hI7, hR7⟩ := seg_mu hs hlen1 hI6 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m8, hI8, hR8⟩ := seg_sib hs hI7 (ok2 s₁.executionEnv.calldata)
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
    have e : mlenOf s₁.executionEnv.calldata = s₀.executionEnv.calldata.size - 5261 := by
      rw [hcd]; rfl
    rw [e]
    exact valid_cost s₀.executionEnv.calldata.size hlen
  · change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, hbit, ← hcd,
      ← accepts_eq_optAccepts _ (by rw [hcd]; exact hlen)]
  · rw [← hs1]
    rfl

end MlDsaOptGlam65.Proofs
