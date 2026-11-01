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
    Reach (callState s 17719 (UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem)
      (callState s 17783 (UInt256.ofNat 40960 :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem) 19 := by
  opt87_reach [7969, 7970, 7971, 7972, 7973, 7974, 7975]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 41984) :
    Reach (callState s 18264 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17783 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 41984 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [8301, 8302, 8303, 8304, 8305, 8306, 8307]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 41984) :
    Reach (callState s 18264 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18280 (UInt256.ofNat 40960 :: UInt256.ofNat 4096 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt87_reach [8301, 8302, 8303, 8304, 8305, 8306, 8307, 8308, 8309, 8310, 8311]

theorem fB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18763 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18280 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [8665, 8666, 8667, 8668, 8669, 8670, 8671] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 18763 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18280 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt87_reach [8665, 8666, 8667, 8668, 8669, 8670, 8671, 8672, 8673, 8674, 8675, 8676, 8677, 8678,
    8679, 8680, 8681, 8682] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 18763 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18798 (UInt256.ofNat 40960 :: UInt256.ofNat 5888 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt87_reach [8665, 8666, 8667, 8668, 8669, 8670, 8671, 8672, 8673, 8674, 8675, 8676, 8677, 8678,
    8679, 8680, 8681, 8682, 8683, 8684, 8685, 8686] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc < 12032) :
    Reach (callState s 18963 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18798 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt87_reach [8812, 8813, 8814, 8815, 8816, 8817, 8818, 8819, 8820, 8821, 8822]

theorem fC_exit (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 18963 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 58 := by
  opt87_reach [8812, 8813, 8814, 8815, 8816, 8817, 8818, 8819, 8820, 8821, 8822, 8823, 8824, 8825,
    8826, 8827, 8828] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 18986 (UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem)
      (callState s 19050 (UInt256.ofNat 59648 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt87_reach [8829, 8830, 8831, 8832, 8833]

theorem iC_cont (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 19299 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19050 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt87_reach [9011, 9012, 9013, 9014, 9015, 9016, 9017, 9018, 9019, 9020, 9021, 9022, 9023]

theorem iC_exit (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 19299 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19324 (UInt256.ofNat 59648 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt87_reach [9011, 9012, 9013, 9014, 9015, 9016, 9017, 9018, 9019, 9020, 9021, 9022, 9023, 9024,
    9025, 9026, 9027]

theorem iB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 19819 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19324 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [9393, 9394, 9395, 9396, 9397, 9398, 9399] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 19819 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19324 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt87_reach [9393, 9394, 9395, 9396, 9397, 9398, 9399, 9400, 9401, 9402, 9403, 9404, 9405, 9406,
    9407, 9408, 9409, 9410, 9411, 9412] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 19819 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19858 (UInt256.ofNat 59648 :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt87_reach [9393, 9394, 9395, 9396, 9397, 9398, 9399, 9400, 9401, 9402, 9403, 9404, 9405, 9406,
    9407, 9408, 9409, 9410, 9411, 9412, 9413, 9414, 9415, 9416, 9417, 9418] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 60672) :
    Reach (callState s 20451 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19858 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt87_reach [9812, 9813, 9814, 9815, 9816, 9817, 9818]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 60672)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 20451 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt87_reach [9812, 9813, 9814, 9815, 9816, 9817, 9818, 9819, 9820, 9821, 9822, 9823, 9824] with [hj]

end

end MlDsaOpt87.Proofs.NttW2  -- port: second instance
