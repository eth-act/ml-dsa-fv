import MlDsaOpt44.Fn.Ntt.Step
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Ntt/Ctl.lean` by `scripts/proofgen_port.py 87` --sub 32768=40960 --sub 33792=41984 --sub 43264=59648 --sub 44288=60672 --sub 66080=91680 --sub 60000=70000; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# Prologues, loop control and exits of `ntt` / `intt` (WP7)

Each loop of `scripts/opt_ntt.py` ends with a pointer update and a compare:
`*_cont` is the taken back edge, `*_exit` the fall-through into the next
pass (or the return); pass B has an inner (`ci`) and an outer (`co`) back edge.
-/

namespace MlDsaOpt87.Proofs.NttW2  -- port: second instance

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt87.Proofs MlDsaOpt44.Proofs

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

local notation "cC2" => UInt256.ofNat 105209460187928082099348286046428385038300376303896864318478598146
local notation "cM" => UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855
local notation "cCI" => UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960) (mem : ByteArray)
  (ret : Nat)
include hs htail

/-! ## Forward -/

theorem f_pro :
    Reach (callState s 17787 (UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem)
      (callState s 17851 (UInt256.ofNat 40960 :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem) 19 := by
  opt87_reach [7980, 7981, 7982, 7983, 7984, 7985, 7986]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 41984) :
    Reach (callState s 18332 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17851 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 41984 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [8312, 8313, 8314, 8315, 8316, 8317, 8318]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 41984) :
    Reach (callState s 18332 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18348 (UInt256.ofNat 40960 :: UInt256.ofNat 4096 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt87_reach [8312, 8313, 8314, 8315, 8316, 8317, 8318, 8319, 8320, 8321, 8322]

theorem fB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18831 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18348 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [8676, 8677, 8678, 8679, 8680, 8681, 8682] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 18831 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18348 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt87_reach [8676, 8677, 8678, 8679, 8680, 8681, 8682, 8683, 8684, 8685, 8686, 8687, 8688, 8689,
    8690, 8691, 8692, 8693] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 18831 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18866 (UInt256.ofNat 40960 :: UInt256.ofNat 5888 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt87_reach [8676, 8677, 8678, 8679, 8680, 8681, 8682, 8683, 8684, 8685, 8686, 8687, 8688, 8689,
    8690, 8691, 8692, 8693, 8694, 8695, 8696, 8697] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc < 12032) :
    Reach (callState s 19031 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18866 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt87_reach [8823, 8824, 8825, 8826, 8827, 8828, 8829, 8830, 8831, 8832, 8833]

theorem fC_exit (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 19031 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 58 := by
  opt87_reach [8823, 8824, 8825, 8826, 8827, 8828, 8829, 8830, 8831, 8832, 8833, 8834, 8835, 8836,
    8837, 8838, 8839] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 19054 (UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem)
      (callState s 19118 (UInt256.ofNat 59648 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt87_reach [8840, 8841, 8842, 8843, 8844]

theorem iC_cont (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 19367 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19118 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt87_reach [9022, 9023, 9024, 9025, 9026, 9027, 9028, 9029, 9030, 9031, 9032, 9033, 9034]

theorem iC_exit (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 19367 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19392 (UInt256.ofNat 59648 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt87_reach [9022, 9023, 9024, 9025, 9026, 9027, 9028, 9029, 9030, 9031, 9032, 9033, 9034, 9035,
    9036, 9037, 9038]

theorem iB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 19887 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19392 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [9404, 9405, 9406, 9407, 9408, 9409, 9410] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 19887 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19392 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt87_reach [9404, 9405, 9406, 9407, 9408, 9409, 9410, 9411, 9412, 9413, 9414, 9415, 9416, 9417,
    9418, 9419, 9420, 9421, 9422, 9423] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 19887 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19926 (UInt256.ofNat 59648 :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt87_reach [9404, 9405, 9406, 9407, 9408, 9409, 9410, 9411, 9412, 9413, 9414, 9415, 9416, 9417,
    9418, 9419, 9420, 9421, 9422, 9423, 9424, 9425, 9426, 9427, 9428, 9429] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 60672) :
    Reach (callState s 20519 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19926 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [9823, 9824, 9825, 9826, 9827, 9828, 9829]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 60672)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 20519 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt87_reach [9823, 9824, 9825, 9826, 9827, 9828, 9829, 9830, 9831, 9832, 9833, 9834, 9835] with [hj]

end

end MlDsaOpt87.Proofs.NttW2  -- port: second instance
