import MlDsaOpt87.Main.Base
set_option warningAsError true
/-!
# The public gas schedule (ML-DSA-87)

A function of the calldata length only, composed from the segment budgets of
`Main/Base.lean` (themselves sums of subroutine budgets and static glue
costs). Data-dependent control flow is charged at its proved worst case:
RejNTTPoly fix-ups including the sixth squeeze in every group, SampleInBall's
byte loop (with the second `H(c̃)` block), HintBitUnpack's loops; μ's block
count depends on the message length only (always the `kf1` sponge).

`schedule (7219 + n) = 8,189,449 + ⌊(66 + n) / 136⌋ · 33,819` (`schedule_msg`):
8,189,449 for `n ≤ 69`, 8,223,268 for `70 ≤ n ≤ 205`, and 33,819 more per
further 136 message bytes (`python3 scripts/proofgen_gas_param.py 87
--schedule`). The measured adversarial worst case of `docs/opt.md` is
7,954,105 for `n = 0`; the difference is the conservative fix-up and
SampleInBall loop counts.
-/

namespace MlDsaOpt87.Proofs.Gas

/-- Calldata shorter than `pk ‖ σ`: return the zero word (34 gas of
instructions plus one word of memory). -/
def short : Nat := 37

/-- **The public gas schedule.** The fixed segments (in program order, the μ
segment last) plus μ's message-dependent part. -/
def schedule (size : Nat) : Nat :=
  if size < 7219 then short else
    pInit + EvmSemantics.MachineState.memCost memWords + pZh + pSib + pTbl + pNtt + pRho +
      pG0 + pG1 + pG2 + pG3 + pG4 + pG5 + pG6 + pG7 + pG8 + pG9 +
      pG10 + pG11 + pG12 + pG13 + pG14 + pCt + pW + pFin + pMu (size - 7219)

/-- The schedule in closed form: one more `kf1` block per 136 message bytes. -/
theorem schedule_msg (n : Nat) :
    schedule (7219 + n) = 8189449 + (66 + n) / 136 * 33819 := by
  unfold schedule
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  have hc : pInit + EvmSemantics.MachineState.memCost memWords + pZh + pSib + pTbl + pNtt + pRho +
      pG0 + pG1 + pG2 + pG3 + pG4 + pG5 + pG6 + pG7 + pG8 + pG9 +
      pG10 + pG11 + pG12 + pG13 + pG14 + pCt + pW + pFin = 8121875 := by decide
  rw [hc]
  unfold pMu
  have hk : kf1 + absorb17 + 88 = 33819 := rfl
  have hp : kf1 + 202 = 32773 := rfl
  rw [hk, hp]
  generalize (66 + n) / 136 = X
  rw [Nat.add_mul, Nat.one_mul]
  omega

end MlDsaOpt87.Proofs.Gas
