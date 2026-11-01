import MlDsaOpt44.Fn.Ntt.Step
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Ntt/Ctl.lean` by `scripts/proofgen_port.py 65` --sub 43264=51456 --sub 44288=52480 --sub 66080=90656 --sub 60000=70000; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# Prologues, loop control and exits of `ntt` / `intt` (WP7)

Each loop of `scripts/opt_ntt.py` ends with a pointer update and a compare:
`*_cont` is the taken back edge, `*_exit` the fall-through into the next
pass (or the return); pass B has an inner (`ci`) and an outer (`co`) back edge.
-/

namespace MlDsaOpt65.Proofs.NttW

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
    Reach (callState s 17159 (UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem)
      (callState s 17223 (UInt256.ofNat 32768 :: UInt256.ofNat 33792 :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem) 19 := by
  opt65_reach [7650, 7651, 7652, 7653, 7654, 7655, 7656]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 33792) :
    Reach (callState s 17704 (UInt256.ofNat pj :: UInt256.ofNat 33792 :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17223 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 33792 :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [7982, 7983, 7984, 7985, 7986, 7987, 7988]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 33792) :
    Reach (callState s 17704 (UInt256.ofNat pj :: UInt256.ofNat 33792 :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17720 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt65_reach [7982, 7983, 7984, 7985, 7986, 7987, 7988, 7989, 7990, 7991, 7992]

theorem fB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18203 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17720 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [8346, 8347, 8348, 8349, 8350, 8351, 8352] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 18203 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17720 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt65_reach [8346, 8347, 8348, 8349, 8350, 8351, 8352, 8353, 8354, 8355, 8356, 8357, 8358, 8359,
    8360, 8361, 8362, 8363] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 18203 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18238 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt65_reach [8346, 8347, 8348, 8349, 8350, 8351, 8352, 8353, 8354, 8355, 8356, 8357, 8358, 8359,
    8360, 8361, 8362, 8363, 8364, 8365, 8366, 8367] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc < 12032) :
    Reach (callState s 18403 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18238 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt65_reach [8493, 8494, 8495, 8496, 8497, 8498, 8499, 8500, 8501, 8502, 8503]

theorem fC_exit (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 18403 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 58 := by
  opt65_reach [8493, 8494, 8495, 8496, 8497, 8498, 8499, 8500, 8501, 8502, 8503, 8504, 8505, 8506,
    8507, 8508, 8509] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 18426 (UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem)
      (callState s 18490 (UInt256.ofNat 51456 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt65_reach [8510, 8511, 8512, 8513, 8514]

theorem iC_cont (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 18739 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18490 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt65_reach [8692, 8693, 8694, 8695, 8696, 8697, 8698, 8699, 8700, 8701, 8702, 8703, 8704]

theorem iC_exit (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 18739 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18764 (UInt256.ofNat 51456 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt65_reach [8692, 8693, 8694, 8695, 8696, 8697, 8698, 8699, 8700, 8701, 8702, 8703, 8704, 8705,
    8706, 8707, 8708]

theorem iB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 19259 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18764 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [9074, 9075, 9076, 9077, 9078, 9079, 9080] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 19259 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18764 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt65_reach [9074, 9075, 9076, 9077, 9078, 9079, 9080, 9081, 9082, 9083, 9084, 9085, 9086, 9087,
    9088, 9089, 9090, 9091, 9092, 9093] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 19259 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19298 (UInt256.ofNat 51456 :: UInt256.ofNat 52480 :: cCI :: cM ::
        UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt65_reach [9074, 9075, 9076, 9077, 9078, 9079, 9080, 9081, 9082, 9083, 9084, 9085, 9086, 9087,
    9088, 9089, 9090, 9091, 9092, 9093, 9094, 9095, 9096, 9097, 9098, 9099] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 52480) :
    Reach (callState s 19891 (UInt256.ofNat pj :: UInt256.ofNat 52480 :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19298 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 52480 :: cCI :: cM ::
        UInt256.ofNat 51456 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [9493, 9494, 9495, 9496, 9497, 9498, 9499]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 52480)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 19891 (UInt256.ofNat pj :: UInt256.ofNat 52480 :: cCI :: cM :: UInt256.ofNat 51456 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt65_reach [9493, 9494, 9495, 9496, 9497, 9498, 9499, 9500, 9501, 9502, 9503, 9504, 9505] with [hj]

end

end MlDsaOpt65.Proofs.NttW
