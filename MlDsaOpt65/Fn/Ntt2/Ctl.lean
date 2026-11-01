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
    Reach (callState s 16856 (UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem)
      (callState s 16920 (UInt256.ofNat 40960 :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem) 19 := by
  opt65_reach [7491, 7492, 7493, 7494, 7495, 7496, 7497]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 41984) :
    Reach (callState s 17401 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 16920 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 41984 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [7823, 7824, 7825, 7826, 7827, 7828, 7829]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 41984) :
    Reach (callState s 17401 (UInt256.ofNat pj :: UInt256.ofNat 41984 :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17417 (UInt256.ofNat 40960 :: UInt256.ofNat 4096 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt65_reach [7823, 7824, 7825, 7826, 7827, 7828, 7829, 7830, 7831, 7832, 7833]

theorem fB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 17900 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17417 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [8187, 8188, 8189, 8190, 8191, 8192, 8193] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 17900 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17417 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt65_reach [8187, 8188, 8189, 8190, 8191, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200,
    8201, 8202, 8203, 8204] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 17900 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17935 (UInt256.ofNat 40960 :: UInt256.ofNat 5888 :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt65_reach [8187, 8188, 8189, 8190, 8191, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200,
    8201, 8202, 8203, 8204, 8205, 8206, 8207, 8208] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc < 12032) :
    Reach (callState s 18100 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17935 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cC2 :: cM ::
        UInt256.ofNat 40960 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt65_reach [8334, 8335, 8336, 8337, 8338, 8339, 8340, 8341, 8342, 8343, 8344]

theorem fC_exit (pj zc : Nat) (hpj : pj < 70000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 18100 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 40960 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 58 := by
  opt65_reach [8334, 8335, 8336, 8337, 8338, 8339, 8340, 8341, 8342, 8343, 8344, 8345, 8346, 8347,
    8348, 8349, 8350] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 18123 (UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem)
      (callState s 18187 (UInt256.ofNat 59648 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt65_reach [8351, 8352, 8353, 8354, 8355]

theorem iC_cont (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 18436 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18187 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt65_reach [8533, 8534, 8535, 8536, 8537, 8538, 8539, 8540, 8541, 8542, 8543, 8544, 8545]

theorem iC_exit (pj zc : Nat) (hpj : pj < 70000) (hzc : zc < 70000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 18436 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18461 (UInt256.ofNat 59648 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt65_reach [8533, 8534, 8535, 8536, 8537, 8538, 8539, 8540, 8541, 8542, 8543, 8544, 8545, 8546,
    8547, 8548, 8549]

theorem iB_ci (pj zb : Nat) (hpj : pj < 70000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18956 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18461 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [8915, 8916, 8917, 8918, 8919, 8920, 8921] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 18956 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18461 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt65_reach [8915, 8916, 8917, 8918, 8919, 8920, 8921, 8922, 8923, 8924, 8925, 8926, 8927, 8928,
    8929, 8930, 8931, 8932, 8933, 8934] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 70000) (hzb : zb < 70000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 18956 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18995 (UInt256.ofNat 59648 :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt65_reach [8915, 8916, 8917, 8918, 8919, 8920, 8921, 8922, 8923, 8924, 8925, 8926, 8927, 8928,
    8929, 8930, 8931, 8932, 8933, 8934, 8935, 8936, 8937, 8938, 8939, 8940] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 60672) :
    Reach (callState s 19588 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18995 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 60672 :: cCI :: cM ::
        UInt256.ofNat 59648 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt65_reach [9334, 9335, 9336, 9337, 9338, 9339, 9340]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 60672)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 19588 (UInt256.ofNat pj :: UInt256.ofNat 60672 :: cCI :: cM :: UInt256.ofNat 59648 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt65_reach [9334, 9335, 9336, 9337, 9338, 9339, 9340, 9341, 9342, 9343, 9344, 9345, 9346] with [hj]

end

end MlDsaOpt65.Proofs.NttW2  -- port: second instance
