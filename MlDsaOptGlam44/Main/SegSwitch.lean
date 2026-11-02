import MlDsaOptGlam44.Main.SegGroups
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
set_option warningAsError true
/-!
# The long-message switch (`gen_opt.py`, R4-7, glam 44 only)

ExpandA's first two groups are shared. At `2436` the code tests
`CALLDATASIZE < HDR + 342` (`0x0fea`):

* `|M| < 342`: `FLAG := 1` and the packed schedule follows (v4's groups and
  window, `2452 … 3948`), then a jump to the shared code at `altj` (`5081`);
* `|M| ≥ 342`: a jump to `alt` (`3953`), the previous schedule (its last group
  carries up to five μ blocks; `mulong`, `pass3f4b`), which falls through to
  `altj` with `FLAG = 0`.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

/-- The switch block on the packed side: the test falls through and stores
`FLAG = 1`. -/
theorem switch_packed_block {s : State} (hs : Ctx s) {m : ByteArray} (b : Bool)
    (hlt : s.executionEnv.calldata.size < 4074) :
    Reach (callState s 2436 [flag b] m)
      (callState s 2452 [flag b] (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 1 32) FLAG)) 33 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  glam44_rreach [940, 941, 942, 943, 944, 945, 946, 947, 948] with [FLAG, hlt]

/-- The switch block on the long side: the jump to `alt`. -/
theorem switch_alt_block {s : State} (hs : Ctx s) {m : ByteArray} (b : Bool)
    (hge : 4074 ≤ s.executionEnv.calldata.size) :
    Reach (callState s 2436 [flag b] m) (callState s 3953 [flag b] m) 24 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hn : ¬ s.executionEnv.calldata.size < 4074 := by omega
  glam44_rreach [940, 941, 942, 943, 944, 945] with [hn]

/-- `2436 … 2452` on the packed schedule: `InvG1` is kept and `FLAG = 1`. -/
theorem seg_switch {s : State} (hs : Ctx s) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (b : Bool) (hlt : s.executionEnv.calldata.size < 4074) :
    ∃ m', InvG1 s.executionEnv.calldata m' ∧ word m' FLAG = 1 ∧
      Reach (callState s 2436 [flag b] m) (callState s 2452 [flag b] m') Gas.pSw := by
  have hfr := FrameExcept.mstore m FLAG 1
  refine ⟨_, ⟨⟨hI.toInvX.frame hfr (by unfold FLAG; avoids_tac) (by unfold FLAG; avoids_tac)
      (by unfold FLAG; avoids_tac) (by unfold FLAG; avoids_tac) (by unfold FLAG; avoids_tac)
      (by unfold FLAG; avoids_tac) (by unfold FLAG; avoids_tac),
      hI.c0.frame hfr (by unfold FLAG; avoids_tac)⟩, hI.c1.frame hfr (by unfold FLAG; avoids_tac)⟩,
    word_mstore m FLAG 1 (by norm_num), ?_⟩
  exact (switch_packed_block hs b hlt).mono (by unfold Gas.pSw; omega)

/-- `3948 … 5081`: the packed schedule's jump to the shared code (`altj`). -/
theorem seg_join {s : State} (hs : Ctx s) {m : ByteArray} (b : Bool) :
    Reach (callState s 3948 [flag b] m) (callState s 5081 [flag b] m) Gas.pJoin := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h : Reach (callState s 3948 [flag b] m) (callState s 5081 [flag b] m) 12 := by
    glam44_rreach [1347, 1348, 1349]
  exact h.mono (by unfold Gas.pJoin; omega)

end MlDsaOptGlam44.Proofs
