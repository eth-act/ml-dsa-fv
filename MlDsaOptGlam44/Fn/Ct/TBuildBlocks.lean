import MlDsaOpt44.Fn.Decode.Bswap
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Layout
/- Ported from `MlDsaOpt44/Fn/Ct/TBuildBlocks.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option linter.unusedSimpArgs false
/-!
# `tbuild` (WP10): straight-line blocks

Loop heads: `13937` (chunk loop, stack `pa, TT, off, end, ret` with `TT = 20480`,
`end = TT + 2208 = 22688`) and `14328` (word loop, stack `sh, V3, V2, V1, V0, pa, …`).
The windows `V_r` enter as `leNat cd (off + 320 r) 32` (`bsw_word`); the word loop
body is cut after the cell/transpose network (`tbW`, kept abstract in the store block).
-/

namespace MlDsaOptGlam44.Proofs.TB

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ

/-! ## Shapes `glam44_block` leaves -/

/-- Gather: 40 bits of `V_r` from bit `sh` into lane `r`. -/
def tgW (sh V0 V1 V2 V3 : Nat) : Nat :=
  (1099511627775 &&& V3 / 2 ^ sh) * 6277101735386680763835789423207666416102355444464034512896 |||
    ((1099511627775 &&& V2 / 2 ^ sh) * 340282366920938463463374607431768211456 |||
      ((1099511627775 &&& V1 / 2 ^ sh) * 18446744073709551616 ||| 1099511627775 &&& V0 / 2 ^ sh))

/-- First spreading stage: 20-bit halves of each lane to 32-bit units. -/
def ts1 (x : Nat) : Nat :=
  6582011952183088782295924477334101861609978183833731334774194175 &&& x |||
    (6901739764772334502984731304745083193639544484091638668092185431244800 &&& x) * 4096

/-- Second spreading stage: 10-bit fields to 16-bit cells. -/
def ts2 (x : Nat) : Nat :=
  27580025446916579586740047030762717305835781530194468456916412547466239 &&& x |||
    (28241946057642577496821808159501022521175840286919135699882406448605428736 &&& x) * 64

/-- Delta swap of the bits selected by `m` with the bits `d` above them. -/
def tdsw (m d x : Nat) : Nat :=
  (m &&& (x ^^^ x % 2 ^ 256 / 2 ^ d)) * 2 ^ d ^^^ m &&& (x ^^^ x % 2 ^ 256 / 2 ^ d) ^^^ x

/-- The word stored at `pa`. -/
def tbW (sh V0 V1 V2 V3 : Nat) : Nat :=
  tdsw 6277005955876855982367846414099012818794836107166352343040 48
    (tdsw 340282366841710300967557013907638845440 96 (ts2 (ts1 (tgW sh V0 V1 V2 V3))))

/-- The word stored at `pa ± 2048`. -/
def tbN (X : Nat) : Nat :=
  (1807512127714571876376182462255096204072559614144354879260930929123294905343 ^^^ X) % 2 ^ 256

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem tb_pro (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 21045 (wd 20480 :: wd 32 :: wd ret :: tail) M)
      (callState s 21058 (wd 24544 :: wd 20480 :: wd 32 :: wd 22688 :: wd ret :: tail) M) 25 := by
  glam44_rreach [9076, 9077, 9078, 9079, 9080, 9081, 9082, 9083, 9084]

theorem tb_l0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 21058 (wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21239 (wd (leNat s.executionEnv.calldata off 32) ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 172 := by
  glam44_rreach [9085, 9086, 9087, 9088, 9089, 9090, 9091, 9092, 9093, 9094, 9095, 9096, 9097, 9098, 9099, 9100, 9101, 9102, 9103, 9104, 9105, 9106, 9107, 9108, 9109, 9110, 9111, 9112, 9113, 9114, 9115, 9116, 9117, 9118, 9119, 9120, 9121, 9122, 9123, 9124, 9125, 9126, 9127, 9128, 9129, 9130, 9131, 9132, 9133, 9134, 9135, 9136, 9137, 9138, 9139, 9140, 9141, 9142] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 21239 (wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21306 (wd (leNat s.executionEnv.calldata (320 + off) 32) :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 165 := by
  glam44_rreach [9143, 9144, 9145, 9146, 9147, 9148, 9149, 9150, 9151, 9152, 9153, 9154, 9155, 9156, 9157, 9158, 9159, 9160, 9161, 9162, 9163, 9164, 9165, 9166, 9167, 9168, 9169, 9170, 9171, 9172, 9173, 9174, 9175, 9176, 9177, 9178, 9179, 9180, 9181, 9182, 9183, 9184, 9185, 9186, 9187, 9188, 9189, 9190, 9191, 9192, 9193, 9194, 9195, 9196, 9197] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 21306 (wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21373 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 165 := by
  glam44_rreach [9198, 9199, 9200, 9201, 9202, 9203, 9204, 9205, 9206, 9207, 9208, 9209, 9210, 9211, 9212, 9213, 9214, 9215, 9216, 9217, 9218, 9219, 9220, 9221, 9222, 9223, 9224, 9225, 9226, 9227, 9228, 9229, 9230, 9231, 9232, 9233, 9234, 9235, 9236, 9237, 9238, 9239, 9240, 9241, 9242, 9243, 9244, 9245, 9246, 9247, 9248, 9249, 9250, 9251, 9252] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 21373 (wd V2 :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21449 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) :: wd V2 :: wd V1 :: wd V0 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 187 := by
  glam44_rreach [9253, 9254, 9255, 9256, 9257, 9258, 9259, 9260, 9261, 9262, 9263, 9264, 9265, 9266, 9267, 9268, 9269, 9270, 9271, 9272, 9273, 9274, 9275, 9276, 9277, 9278, 9279, 9280, 9281, 9282, 9283, 9284, 9285, 9286, 9287, 9288, 9289, 9290, 9291, 9292, 9293, 9294, 9295, 9296, 9297, 9298, 9299, 9300, 9301, 9302, 9303, 9304, 9305, 9306, 9307, 9308, 9309, 9310, 9311, 9312, 9313, 9314, 9315, 9316] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_A (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {sh V0 V1 V2 V3 pa off : Nat}
    (hsh : sh ≤ 200) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 21449 (wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21707 (wd (tbW sh V0 V1 V2 V3) :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 214 := by
  glam44_rreach [9317, 9318, 9319, 9320, 9321, 9322, 9323, 9324, 9325, 9326, 9327, 9328, 9329, 9330, 9331, 9332, 9333, 9334, 9335, 9336, 9337, 9338, 9339, 9340, 9341, 9342, 9343, 9344, 9345, 9346, 9347, 9348, 9349, 9350, 9351, 9352, 9353, 9354, 9355, 9356, 9357, 9358, 9359, 9360, 9361, 9362, 9363, 9364, 9365, 9366, 9367, 9368, 9369, 9370, 9371, 9372, 9373, 9374, 9375, 9376, 9377, 9378, 9379, 9380, 9381, 9382, 9383, 9384, 9385, 9386, 9387, 9388] with [tbW, tdsw, ts2, ts1, tgW]

/-- Memory after the three stores of one word-loop visit. -/
def st3 (M : ByteArray) (pa X : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
    (Data.Bytes.natToBytesPadded X 32) pa) (Data.Bytes.natToBytesPadded (tbN X) 32) (2048 + pa))
    (Data.Bytes.natToBytesPadded (tbN X) 32) (pa - 2048)

theorem tb_B (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X sh V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hsh : sh + 40 < 240) (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 66080) :
    Reach (callState s 21707 (wd X :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21449 (wd (40 + sh) :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail)
        (st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [9389, 9390, 9391, 9392, 9393, 9394, 9395, 9396, 9397, 9398, 9399, 9400, 9401, 9402, 9403, 9404, 9405, 9406, 9407, 9408, 9409, 9410, 9411, 9412, 9413, 9414, 9415] with [st3, tbN]

theorem tb_Bx (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 66080) :
    Reach (callState s 21707 (wd X :: wd 200 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21775 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail)
        (st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [9389, 9390, 9391, 9392, 9393, 9394, 9395, 9396, 9397, 9398, 9399, 9400, 9401, 9402, 9403, 9404, 9405, 9406, 9407, 9408, 9409, 9410, 9411, 9412, 9413, 9414, 9415] with [st3, tbN]

theorem tb_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 pa off : Nat}
    (_hne : pa ≠ 22496) (hle : 22688 ≤ pa) (hpa : pa < 2 ^ 64) (_hoff : off < 2 ^ 64) :
    Reach (callState s 21775 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 21058 (wd pa :: wd 20480 :: wd (30 + off) :: wd 22688 :: wd ret :: tail) M) 90 := by
  glam44_rreach [9416, 9417, 9418, 9419, 9420, 9421, 9422, 9423, 9424, 9425, 9426, 9427, 9428, 9429, 9430, 9431, 9432, 9433, 9434, 9435, 9436, 9437, 9438, 9445, 9446, 9447]

theorem tb_cl (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 : Nat} :
    Reach (callState s 21775 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd 22624 :: wd 20480 :: wd 302 :: wd 22688 :: wd ret :: tail) M)
      (callState s 21058 (wd 22688 :: wd 20480 :: wd 322 :: wd 22688 :: wd ret :: tail) M) 107 := by
  have h : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129640258 =
      UInt256.ofNat 322 := ofNat_eq_ofNat_iff.mpr (by norm_num)
  glam44_rreach [9416, 9417, 9418, 9419, 9420, 9421, 9422, 9423, 9424, 9425, 9426, 9427, 9428, 9429, 9430, 9431, 9432, 9433, 9434, 9435, 9436, 9437, 9438, 9439, 9440, 9441, 9442, 9443, 9444, 9445, 9446, 9447] with [h]

set_option maxRecDepth 100000 in
theorem tb_exit (hs : Ctx s) (htl : tail.length ≤ 960) (hj : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) {V0 V1 V2 V3 : Nat} :
    Reach (callState s 21775 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd 22496 :: wd 20480 :: wd 322 :: wd 22688 :: wd ret :: tail) M)
      (callState s ret tail M) 58 := by
  glam44_rreach [9416, 9417, 9418, 9419, 9420, 9421, 9422, 9423, 9424, 9425, 9426, 9427, 9428, 9448, 9449, 9450, 9451, 9452, 9453] with [hj]

end

end MlDsaOptGlam44.Proofs.TB
