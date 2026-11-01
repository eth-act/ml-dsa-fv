import MlDsaOpt87.Main.Short
import MlDsaOpt87.Main.SegInit
import MlDsaOpt87.Main.SegZh
import MlDsaOpt87.Main.SegSib
import MlDsaOpt87.Main.SegTbl
import MlDsaOpt87.Main.SegNtt
import MlDsaOpt87.Main.SegRho
import MlDsaOpt87.Main.SegGroups
import MlDsaOpt87.Main.SegMixed
import MlDsaOpt87.Main.SegKron
import MlDsaOpt87.Main.SegMu
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

/-- The flag of ExpandA group `i` (`Main/Inv.lean`): rows 0–3 of column `i`
(`i < 7`), rows 4–7 of column `i − 7` (`i < 10`), rows 4–6 of column `i − 7`
(the mixed groups, `i < 14`), row 7 of columns 3–6 (`i = 14`). -/
def groupFlag (cd : ByteArray) : Nat → Bool
  | 0 => okCol cd 0 0 4
  | 1 => okCol cd 0 1 4
  | 2 => okCol cd 0 2 4
  | 3 => okCol cd 0 3 4
  | 4 => okCol cd 0 4 4
  | 5 => okCol cd 0 5 4
  | 6 => okCol cd 0 6 4
  | 7 => okCol cd 1 0 4
  | 8 => okCol cd 1 1 4
  | 9 => okCol cd 1 2 4
  | 10 => okCol cd 1 3 3
  | 11 => okCol cd 1 4 3
  | 12 => okCol cd 1 5 3
  | 13 => okCol cd 1 6 3
  | _ => okRow7 cd

/-- The stack flag after the first `n` ExpandA groups: `ok2` and the group
flags, in the order the code ANDs them. -/
def groupsUpTo (cd : ByteArray) : Nat → Bool
  | 0 => ok2 cd
  | n + 1 => groupsUpTo cd n && groupFlag cd n

/-- After the fifteen ExpandA groups the flag is `ok3 = ok2 ∧ okA` (every
`A[r][s]`, `r < 8`, `s < 7`, is checked by exactly one group). -/
theorem flags_eq (cd : ByteArray) : groupsUpTo cd 15 = ok3 cd := by
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  have h7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h3 : List.range 3 = [0, 1, 2] := rfl
  simp only [groupsUpTo, groupFlag]
  unfold ok3 okA okCol okRow7
  rw [h8, h7, h4, h3]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Nat.reduceMul, Nat.reduceAdd]
  ac_rfl

/-- The returned bit is the bytecode-flow verdict. -/
theorem result_bit (cd : ByteArray) (E : Bool) (m : ByteArray) (hI : Inv9 cd m)
    (hE : ∀ X : ByteArray, X.size = 1088 → FinAt m X → E = (ctOf cd == Fips204.H X 64)) :
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
theorem valid_cost (size : Nat) (h : 7219 ≤ size) :
    Gas.pInit + MachineState.memCost memWords + Gas.pZh + Gas.pSib + Gas.pTbl + Gas.pNtt +
        Gas.pRho + Gas.pG0 + Gas.pG1 + Gas.pG2 + Gas.pG3 + Gas.pG4 + Gas.pG5 + Gas.pG6 +
        Gas.pG7 + Gas.pG8 + Gas.pG9 + Gas.pG10 + Gas.pG11 + Gas.pG12 + Gas.pG13 + Gas.pG14 +
        Gas.pCt + Gas.pW + Gas.pFin + Gas.pMu (size - 7219) ≤
      Gas.schedule size := by
  unfold Gas.schedule
  rw [if_neg (by omega)]

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
  obtain ⟨m1, hI1, hR1⟩ := seg_zh hs hlen1 hI0
  obtain ⟨m2, hI2, hR2⟩ := seg_sib hs hlen1 hI1 (ok1 s₁.executionEnv.calldata)
  obtain ⟨m3, hI3, hR3⟩ := seg_tbl hs hI2 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m4, hI4, hR4⟩ := seg_ntt hs hI3 (ok2 s₁.executionEnv.calldata) hlen1
  obtain ⟨m5, hI5, hR5⟩ := seg_rho hs hlen1 hI4 (ok2 s₁.executionEnv.calldata)
  obtain ⟨m6, hI6, hR6⟩ := seg_g0 hs hlen1 hI5 (groupsUpTo s₁.executionEnv.calldata 0)
  obtain ⟨m7, hI7, hR7⟩ := seg_g1 hs hlen1 hI6 (groupsUpTo s₁.executionEnv.calldata 1)
  obtain ⟨m8, hI8, hR8⟩ := seg_g2 hs hlen1 hI7 (groupsUpTo s₁.executionEnv.calldata 2)
  obtain ⟨m9, hI9, hR9⟩ := seg_g3 hs hlen1 hI8 (groupsUpTo s₁.executionEnv.calldata 3)
  obtain ⟨m10, hI10, hR10⟩ := seg_g4 hs hlen1 hI9 (groupsUpTo s₁.executionEnv.calldata 4)
  obtain ⟨m11, hI11, hR11⟩ := seg_g5 hs hlen1 hI10 (groupsUpTo s₁.executionEnv.calldata 5)
  obtain ⟨m12, hI12, hR12⟩ := seg_g6 hs hlen1 hI11 (groupsUpTo s₁.executionEnv.calldata 6)
  obtain ⟨m13, hI13, hR13⟩ := seg_g7 hs hlen1 hI12 (groupsUpTo s₁.executionEnv.calldata 7)
  obtain ⟨m14, hI14, hR14⟩ := seg_g8 hs hlen1 hI13 (groupsUpTo s₁.executionEnv.calldata 8)
  obtain ⟨m15, hI15, hR15⟩ := seg_g9 hs hlen1 hI14 (groupsUpTo s₁.executionEnv.calldata 9)
  obtain ⟨m16, hI16, hR16⟩ := seg_g10 hs hlen1 hI15 (groupsUpTo s₁.executionEnv.calldata 10)
  obtain ⟨m17, hI17, hR17⟩ := seg_g11 hs hlen1 hI16 (groupsUpTo s₁.executionEnv.calldata 11)
  obtain ⟨m18, hI18, hR18⟩ := seg_g12 hs hlen1 hI17 (groupsUpTo s₁.executionEnv.calldata 12)
  obtain ⟨m19, hI19, hR19⟩ := seg_g13 hs hlen1 hI18 (groupsUpTo s₁.executionEnv.calldata 13)
  obtain ⟨m20, hI20, hR20⟩ := seg_g14 hs hlen1 hI19 (groupsUpTo s₁.executionEnv.calldata 14)
  obtain ⟨m21, hI21, hR21⟩ := seg_mu hs hlen1 hI20 (groupsUpTo s₁.executionEnv.calldata 15)
  obtain ⟨m22, hI22, hR22⟩ := seg_ct hs hlen1 hI21 (groupsUpTo s₁.executionEnv.calldata 15)
  obtain ⟨m23, hI23, hR23⟩ := seg_w hs hlen1 hI22 (groupsUpTo s₁.executionEnv.calldata 15)
  obtain ⟨E, pc, stk, m24, hE, hR24⟩ := seg_fin hs hlen1 hI23.rc1 (groupsUpTo s₁.executionEnv.calldata 15)
  have hbit : (ok3 s₁.executionEnv.calldata && E) = optAccepts s₁.executionEnv.calldata :=
    result_bit _ E m23 hI23 hE
  have h := (((((((((((((((((((((((hR0'.trans hR1).trans hR2).trans hR3).trans hR4).trans
    hR5).trans hR6).trans hR7).trans hR8).trans hR9).trans hR10).trans hR11).trans hR12).trans
    hR13).trans hR14).trans hR15).trans hR16).trans hR17).trans hR18).trans hR19).trans
    hR20).trans hR21).trans hR22).trans hR23).trans hR24
  obtain ⟨g, hg⟩ := h
  refine ⟨_, g, ?_, rfl, ?_, ?_⟩
  · refine hg.trans ?_
    have := valid_cost s₀.executionEnv.calldata.size hlen
    rw [← hcd]
    unfold mlenOf HDR
    rw [hcd]
    omega
  · change MachineState.readPadded _ 0 32 = _
    rw [readPadded_mstore0, spec_eq, flags_eq, hbit, ← hcd,
      ← accepts_eq_optAccepts _ (by rw [hcd]; exact hlen)]
  · rw [← hs1]
    rfl

end MlDsaOpt87.Proofs
