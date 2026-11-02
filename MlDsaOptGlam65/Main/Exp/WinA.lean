import MlDsaOptGlam65.Main.Exp.WinDefs
import MlDsaOpt65.Fn.Group.Seed
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The window, calls 35–39 and `pass3f7` (`3739 … 4400`)

`kmove` puts `tr` (after blocks 0 … 9) into slot 1, `ginit` starts `A44`, `A34`,
`A33` in slots 0, 2, 3; calls 35, 36 absorb `tr`'s blocks 10, 11 (slot 1); the
state is saved to `IMGA = 0x14a00`; `kmove` moves `tr` to slot 0, `ginit` starts
`A54` in slot 1; calls 37, 38 absorb blocks 12, 13 (slot 0); the state is saved to
`IMGB = 0x14d20`; `kmove` restores `A44` from `IMGA` into slot 0; call 39 (full
`blk` of block 4); `HAVE6 := 0`, `gfix 12` fixes `P = (A34, A33)` (slots 2, 3)
and keeps the other lanes of blocks 0 … 4 and the flag words (`blk`'s whole
block 4 is the tail `blkt` would make); `AND`; `pass3f7` (row group 0 into `ACC`).
-/

namespace MlDsaOptGlam65.Proofs.Exp

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding Rho1At ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

/-- Close `Avoids rs lo hi` for literal layout ranges. -/
macro "w_frame" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW,
    ABUF, FL, ZH, ZH2, BASES, IDX, ACC, HP, FIN, RHO1, CB, TRL, MU, BK, TT, SP, TOP, KZ, SB, MUIMG]
  omega))

/-- `ginit` inside the window (no `HAVE6` store before it). -/
theorem wginit {s : State} (hs : Ctx s) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S I : Nat → Fips202.SpongeState}
    {keep kmask amult cmult l4 : Nat} {L : Nat → Nat} (ha : amult < 16) (hc : cmult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hl4 : l4 = il L) (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true →
      amult.testBit k = false ∧ cmult.testBit k = false ∧ L k = 0)
    (hkept : ∀ k, k < 4 → kmask.testBit k = true → I k = S k)
    (hfresh : ∀ k, k < 4 → kmask.testBit k = false → ∀ x, x < 25 →
      S4.freshLane amult cmult (fun x => le64 s.executionEnv.calldata (8 * x))
        (fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) L k x = laneOf (I k) x)
    {pc0 r c0 : Nat} {stk : List UInt256} {b : Bool}
    (g0 : Reach (callState s pc0 stk m)
      (callState s 17659 [wd l4, wd cmult, wd amult, wd keep, wd r, flag b] m) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 I ∧ FrameExcept m m1 [(KS, KS + 800)] ∧
      Reach (callState s pc0 stk m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  have hkeep' : keep < 2 ^ 256 := by rw [hkeep]; exact il_lt _
  have hl4' : l4 < 2 ^ 256 := by rw [hl4]; exact il_lt _
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := r) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m (keep := keep) (amult := amult) (cmult := cmult) (l4 := l4)
    hkeep' (by omega) (by omega) hl4'
  exact ⟨m1, S4.ks4_ginit (kmask := kmask) (L := L) (ρ := fun x => le64 s.executionEnv.calldata (8 * x))
      (c := fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) (S := S)
      ha hc hkeep hl4 (fun x hx => hrho.1 x hx) (fun x hx => hrho.2 x hx) hand
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) hL hdisj hkept hfresh hg, hf1, g0.trans hc1⟩

/-- The `kmove` result as a `ginit` keep input. -/
theorem and_keep {w : Nat → Nat} (hw : ∀ k, k < 4 → w k < 2 ^ 64) (kmask : Nat) :
    il w &&& (il fun k => if kmask.testBit k then M64 else 0) =
      il fun k => if kmask.testBit k then w k else 0 := by
  rw [il_and]
  apply il_congr; intro k hk
  split
  · rw [show M64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hw k hk)]
  · exact Nat.and_zero _

theorem keep2 : (0x2222222222222222222222222222222222222222222222222222222222222222 : Nat) =
    il fun k => if (2 : Nat).testBit k then M64 else 0 := by decide +kernel
theorem keepD : (0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd : Nat) =
    il fun k => if (13 : Nat).testBit k then M64 else 0 := by decide +kernel

/-- The seeds of `P`'s slots. -/
def IP (cd : ByteArray) (sl : Nat) : Fips202.SpongeState := if sl = 2 then sA cd 3 4 else sA cd 3 3

theorem flag_P {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(12 : Nat).testBit sl || (aI (IP cd sl)).isSome) = okP cd := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (12 : Nat).testBit 0 = false by decide, show (12 : Nat).testBit 1 = false by decide,
    show (12 : Nat).testBit 2 = true by decide, show (12 : Nat).testBit 3 = true by decide,
    IP, okP, if_true, if_false, show (3 : Nat) ≠ 2 by decide, sA, GroupP.aI_aSeed hcd,
    Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and, Bool.and_true]

/-- What the window's second half needs (pc 4400). -/
structure WinMid (cd m : ByteArray) : Prop where
  g5 : G5In cd m
  ks : KS4 m (W cd 4)
  lanes : ∀ b, b < 5 → ∀ i, i < 56 → ∀ sl, sl < 2 →
    lane (word m (ABUF + 1792 * b + 32 * i)) sl = cand (W cd b sl) i
  flags : ∀ b, b < 5 → ∀ g, g < 7 → word m (FL + 224 * b + 32 * g) = flagWord (W cd b) g
  imgB : St4At m 0x14d20 (W cd 3)
  acc7 : ∃ m7, (∀ t, t < 256 → word m (ACC + 32 * t) = p3f7Word m7 t) ∧ ZHatAt m7 cd ∧
    BufCol m7 CW cd 0 ∧ BufCol m7 HP cd 1 ∧ BufCol m7 (HP + 8192) cd 2 ∧
    Col3Hi m7 ACC cd 3 ∧ Col3Hi m7 (SB + 8192) cd 4 ∧
    (okA cd = true → ∀ t, t < 256 →
      lane (word m7 (ABUF + 32 * t)) 2 = ((aD cd 3 4)[t]!).toNat ∧
      lane (word m7 (ABUF + 32 * t)) 3 = ((aD cd 3 3)[t]!).toNat)

end MlDsaOptGlam65.Proofs.Exp
