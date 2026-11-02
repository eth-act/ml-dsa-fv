import MlDsaOpt44.Fn.Ntt.Step
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Ntt/Ctl.lean` by `scripts/proofgen_port.py 65` --sub 32768=40960 --sub 33792=41984 --sub 43264=59648 --sub 44288=60672 --sub 66080=90656 --sub 60000=70000; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# Prologues, loop control and exits of `ntt` / `intt` (WP7)

Each loop of `scripts/opt_ntt.py` ends with a pointer update and a compare:
`*_cont` is the taken back edge, `*_exit` the fall-through into the next
pass (or the return); pass B has an inner (`ci`) and an outer (`co`) back edge.
-/

namespace MlDsaOpt65.Proofs.NttW2  -- port: second instance

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt65.Proofs MlDsaOpt44.Proofs

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
    Reach (callState s 16659 (UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem)
      (callState s 16695 (UInt256.ofNat 40960 :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem) 19 := by
  opt65_reach [7658, 7659, 7652, 7653, 7661, 7662, 7656]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 41984) :
    Reach (callState s 17144 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 16695 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 41984 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [7953, 7954, 7955, 7956, 7957, 7958, 7959]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 41984) :
    Reach (callState s 17144 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17160 (UInt256.ofNat 40960 :: UInt256.ofNat 4096 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt65_reach [7953, 7954, 7955, 7956, 7957, 7958, 7959, 7960, 7961, 7962, 7992]

theorem fB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 17619 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17160 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [8293, 8294, 8295, 8296, 8297, 8298, 8299] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 17619 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17160 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt65_reach [8293, 8294, 8295, 8296, 8297, 8298, 8299, 8300, 8301, 8302, 8303, 8304, 8305, 8306,
    8307, 8308, 8309, 8310] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 17619 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17654 (UInt256.ofNat 40960 :: UInt256.ofNat 5888 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt65_reach [8293, 8294, 8295, 8296, 8297, 8298, 8299, 8300, 8301, 8302, 8303, 8304, 8305, 8306,
    8307, 8308, 8309, 8310, 8311, 8312, 8313, 8367] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc < 12032) :
    Reach (callState s 17811 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17654 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt65_reach [8432, 8433, 8434, 8435, 8436, 8437, 8438, 8439, 8440, 8441, 8442]

theorem fC_exit (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 17811 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 58 := by
  opt65_reach [8432, 8433, 8434, 8435, 8436, 8437, 8438, 8439, 8440, 8441, 8442, 8443, 8444, 8445,
    8446, 8508, 8447] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 17833 (UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem)
      (callState s 17897 (UInt256.ofNat 59648 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt65_reach [8448, 8449, 8450, 8451, 8452]

theorem iC_cont (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 18142 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17897 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt65_reach [8626, 8627, 8628, 8629, 8630, 8631, 8632, 8633, 8634, 8635, 8636, 8637, 8638]

theorem iC_exit (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 18142 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18167 (UInt256.ofNat 59648 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt65_reach [8626, 8627, 8628, 8629, 8630, 8631, 8632, 8633, 8634, 8635, 8636, 8637, 8638, 8639,
    8640, 8641, 8642]

theorem iB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18650 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18167 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [8996, 8997, 8998, 8999, 9000, 9001, 9002] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 18650 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18167 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt65_reach [8996, 8997, 8998, 8999, 9000, 9001, 9002, 9003, 9004, 9005, 9006, 9007, 9008, 9009,
    9010, 9011, 9012, 9013, 9014, 9015] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 18650 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18689 (UInt256.ofNat 59648 :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt65_reach [8996, 8997, 8998, 8999, 9000, 9001, 9002, 9003, 9004, 9005, 9006, 9007, 9008, 9009,
    9010, 9011, 9012, 9013, 9014, 9015, 9016, 9017, 9018, 9019, 9020, 9021] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 60672) :
    Reach (callState s 20518 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18689 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [9715, 9716, 9717, 9718, 9719, 9720, 9721]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 60672)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 20518 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt65_reach [9715, 9716, 9717, 9718, 9719, 9720, 9721, 9722, 9723, 9724, 9725, 9726, 9727] with [hj]

end

end MlDsaOpt65.Proofs.NttW2  -- port: second instance
