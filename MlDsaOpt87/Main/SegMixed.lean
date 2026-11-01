import MlDsaOpt87.Main.Base
import MlDsaOpt87.Main.S5.G10
import MlDsaOpt87.Main.S5.G11
import MlDsaOpt87.Main.S5.G12
import MlDsaOpt87.Main.S5.G13
/-! # Segments `3530 … 5435`: the mixed groups 10–13 (rows 4–6, `tr` rider) -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-!
Groups 10–13 run `A[4][c], A[5][c], A[6][c]` (`c = 3 … 6`) in slots 0–2 and the
`tr = H(pk, 64)` sponge in slot 3 (`TrSlot`: 5 blocks of the padded public
key per group, the slot carried over by `ginit`'s `keep`). Mirror the mixed
groups of `MlDsaOpt44/Main/SegG234/*` (`ks4_ginit`, `ks4_xor_slot`,
`trLane_eq`, `le64_padPk_*`, `le64_trOf`, `pending_of_blocks`). The masked
`pass3m` leaves lane 3 (row 7) of `ACC + 0x2000` unchanged (`AccMid`).

Proofs: `Main/S5/G10` … `Main/S5/G13` on top of `Main/S5/{Sponge,Round}`.
-/

/-- `3530 … 3963`: mixed group 10. `HAVE6 := 0`; `ginit [0, 7, 0, l4]` (slots
0–2 seeded with `A[4..6][3]`, slot 3 the zero state); five rounds of `trabs`
(slot 3, `tr` blocks `0 … 4` of `padPk`), `kf4`, `blk`; `gfix 7` (flag
`okCol cd 1 3 3`, `KS4` preserved); `pass3m [ACC + 0x2000, ZH, 192, lanes 0–2]`. -/
theorem seg_g10 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvB s.executionEnv.calldata m 3) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 4 ∧
      Reach (callState s 3530 [flag b] m)
        (callState s 3963 [flag (b && okCol s.executionEnv.calldata 1 3 3)] m') Gas.pG10 :=
  s5_seg_g10 hs hcd hI b

/-- `3963 … 4430`: mixed group 11. `ginit [spread(2^64 − 1) · 8, 7, 0, l4]`
(slot 3 kept); five rounds of `trabs` (`tr` blocks `5 … 9`), `kf4`, `blk`;
`gfix 7` (flag `okCol cd 1 4 3`); `pass3m [ACC + 0x2000, ZH2, 0, lanes 0–2]`. -/
theorem seg_g11 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvT s.executionEnv.calldata m 4) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 5 ∧
      Reach (callState s 3963 [flag b] m)
        (callState s 4430 [flag (b && okCol s.executionEnv.calldata 1 4 3)] m') Gas.pG11 :=
  s5_seg_g11 hs hcd hI b

/-- `4430 … 4898`: mixed group 12. `ginit` keeping slot 3; five rounds of
`trabs` (`tr` blocks `10 … 14`), `kf4`, `blk`; `gfix 7` (flag `okCol cd 1 5 3`);
`pass3m [ACC + 0x2000, ZH2, 64, lanes 0–2]`. -/
theorem seg_g12 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvT s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 6 ∧
      Reach (callState s 4430 [flag b] m)
        (callState s 4898 [flag (b && okCol s.executionEnv.calldata 1 5 3)] m') Gas.pG12 :=
  s5_seg_g12 hs hcd hI b

/-- `4898 … 5435`: mixed group 13. `ginit` keeping slot 3; `tr` blocks
`15 … 18` by `trabs 5`, the last block 19 by `trabs 1` plus the padding XORs
(`0x1F` into lane 1, `0x80` into lane 16 of slot 3), each followed by `kf4`,
`blk`; then `cext [TRL, 3, 8]` (`TrlAt`: slot 3 is `absorb (padPk cd)`, its
first 8 lanes are `tr`), `gfix 7` (flag `okCol cd 1 6 3`),
`pass3m [ACC + 0x2000, ZH2, 128, lanes 0–2]`. -/
theorem seg_g13 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvT s.executionEnv.calldata m 6) (b : Bool) :
    ∃ m', InvTr s.executionEnv.calldata m' ∧
      Reach (callState s 4898 [flag b] m)
        (callState s 5435 [flag (b && okCol s.executionEnv.calldata 1 6 3)] m') Gas.pG13 :=
  s5_seg_g13 hs hcd hI b

end MlDsaOpt87.Proofs
