import MlDsaOptGlam65.Main.Exp.G02
import MlDsaOptGlam65.Main.Exp.G34
import MlDsaOptGlam65.Main.Exp.G56
import MlDsaOptGlam65.Main.Exp.Win
set_option warningAsError true
/-!
# Segment `2515 … 4903`: ExpandA, the 42-call schedule (glam ML-DSA-65)

Composed from four sub-segments (`Main/Exp/Bound.lean` has the boundaries):

* `Exp.exp_g02` (calls 0–14): `group [15, s, 0]` for `s < 3`, copies of `ABUF`
  to `CW`, `HP`, `HP + 0x2000` (`Main/Exp/G02.lean`);
* `Exp.exp_g34` (calls 15–24): rows 4 and 5 (columns 3, 2, 1, 0 in slots 0 … 3),
  copies to `ACC + 0x2000`, `SB` (`Main/Exp/G34.lean`, generated groups in `Exp/G/`);
* `Exp.exp_g56` (calls 25–34): `tr`'s blocks 0 … 9 in slot 0, rows 0 … 2 of
  columns 3, 4 in slots 1 … 3, copies to `ACC`, `SB + 0x2000` (`Main/Exp/G56.lean`);
* `Exp.exp_win` (calls 35–41): `tr`'s blocks 10 … 14, `P = (A34, A33)`,
  `KX = (A44, A54)` merged by `lmerge`, c̃'s stream, μ's block 0 (`mub0`), the
  state image `MUIMG`, `pass3f7`, `pass3f8` (`Main/Exp/Win*.lean`; the
  accumulation is `Exp.accAt_glam`, `Main/Exp/Acc.lean`).

The four costs sum to exactly `Gas.pExp` (`pExp_eq`).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Exp

theorem pExp_eq : Gas.pExp = gG02 + gG34 + gG56 + cWin := by
  simp only [Gas.pExp, gG02, gG34, gG56, cWin, cW1, cW2a, cW2b, cB1, cB2, cB3, Gas.group, Gas.ginit, Gas.kf4,
    Gas.blk, Gas.blkh, Gas.gfix, Gas.gfix0, Gas.blkt, Gas.fixNo, Gas.fixSq, Gas.trabs, Gas.kmove, Gas.lmerge,
    Gas.cext, Gas.mub0, Gas.pass3f7, Gas.pass3f8]

/-- All flags of the schedule's groups and fix-ups together: `okA`. -/
theorem okA_glam (cd : ByteArray) (z : Bool) :
    (((((((((z && okCol0 cd 0) && okCol0 cd 1) && okCol0 cd 2) && okRow cd 4) && okRow cd 5) &&
      okCol3 cd 3) && okCol3 cd 4) && okP cd) && okKX cd) = (z && okA cd) := by
  simp only [okCol0, okRow, okCol3, okP, okKX, okA, show List.range 4 = [0, 1, 2, 3] from rfl,
    show List.range 3 = [0, 1, 2] from rfl, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl,
    show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.all_cons, List.all_nil, Bool.and_true,
    Nat.sub_zero, show (3 : Nat) - 1 = 2 from rfl, show (3 : Nat) - 2 = 1 from rfl,
    show (3 : Nat) - 3 = 0 from rfl]
  generalize (aOf cd 0 0).isSome = a00
  generalize (aOf cd 0 1).isSome = a01
  generalize (aOf cd 0 2).isSome = a02
  generalize (aOf cd 0 3).isSome = a03
  generalize (aOf cd 0 4).isSome = a04
  generalize (aOf cd 1 0).isSome = a10
  generalize (aOf cd 1 1).isSome = a11
  generalize (aOf cd 1 2).isSome = a12
  generalize (aOf cd 1 3).isSome = a13
  generalize (aOf cd 1 4).isSome = a14
  generalize (aOf cd 2 0).isSome = a20
  generalize (aOf cd 2 1).isSome = a21
  generalize (aOf cd 2 2).isSome = a22
  generalize (aOf cd 2 3).isSome = a23
  generalize (aOf cd 2 4).isSome = a24
  generalize (aOf cd 3 0).isSome = a30
  generalize (aOf cd 3 1).isSome = a31
  generalize (aOf cd 3 2).isSome = a32
  generalize (aOf cd 3 3).isSome = a33
  generalize (aOf cd 3 4).isSome = a34
  generalize (aOf cd 4 0).isSome = a40
  generalize (aOf cd 4 1).isSome = a41
  generalize (aOf cd 4 2).isSome = a42
  generalize (aOf cd 4 3).isSome = a43
  generalize (aOf cd 4 4).isSome = a44
  generalize (aOf cd 5 0).isSome = a50
  generalize (aOf cd 5 1).isSome = a51
  generalize (aOf cd 5 2).isSome = a52
  generalize (aOf cd 5 3).isSome = a53
  generalize (aOf cd 5 4).isSome = a54
  simp only [Bool.and_comm, Bool.and_left_comm]

theorem seg_exp {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 2515 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 4903 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp := by
  obtain ⟨m1, h1, r1⟩ := exp_g02 hs hcd hI (okZ s.executionEnv.calldata)
  obtain ⟨m2, h2, r2⟩ := exp_g34 hs hcd h1 _
  obtain ⟨m3, h3, r3⟩ := exp_g56 hs hcd h2 _
  obtain ⟨m4, h4, r4⟩ := exp_win hs hcd h3 _
  refine ⟨m4, h4, ?_⟩
  rw [pExp_eq, ← okA_glam]
  exact ((r1.trans r2).trans r3).trans r4

end MlDsaOptGlam65.Proofs
