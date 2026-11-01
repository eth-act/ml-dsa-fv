import MlDsaOpt44.Fn.Ntt.Step
/-!
# Prologues, loop control and exits of `ntt` / `intt` (WP7)

Each loop of `scripts/opt_ntt.py` ends with a pointer update and a compare:
`*_cont` is the taken back edge, `*_exit` the fall-through into the next
pass (or the return); pass B has an inner (`ci`) and an outer (`co`) back edge.
-/

namespace MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs

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
    Reach (callState s 16897 (UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem)
      (callState s 16961 (UInt256.ofNat 32768 :: UInt256.ofNat 33792 :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem) 19 := by
  opt44_reach [7473, 7474, 7475, 7476, 7477, 7478, 7479]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 33792) :
    Reach (callState s 17442 (UInt256.ofNat pj :: UInt256.ofNat 33792 :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 16961 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 33792 :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [7805, 7806, 7807, 7808, 7809, 7810, 7811]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 33792) :
    Reach (callState s 17442 (UInt256.ofNat pj :: UInt256.ofNat 33792 :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17458 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt44_reach [7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812, 7813, 7814, 7815]

theorem fB_ci (pj zb : Nat) (hpj : pj < 60000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 17941 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17458 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [8169, 8170, 8171, 8172, 8173, 8174, 8175] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 17941 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17458 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt44_reach [8169, 8170, 8171, 8172, 8173, 8174, 8175, 8176, 8177, 8178, 8179, 8180, 8181, 8182,
    8183, 8184, 8185, 8186] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 17941 (UInt256.ofNat pj :: UInt256.ofNat zb :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17976 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt44_reach [8169, 8170, 8171, 8172, 8173, 8174, 8175, 8176, 8177, 8178, 8179, 8180, 8181, 8182,
    8183, 8184, 8185, 8186, 8187, 8188, 8189, 8190] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 60000) (hz : 96 + zc < 12032) :
    Reach (callState s 18141 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17976 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cC2 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt44_reach [8316, 8317, 8318, 8319, 8320, 8321, 8322, 8323, 8324, 8325, 8326]

theorem fC_exit (pj zc : Nat) (hpj : pj < 60000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 18141 (UInt256.ofNat pj :: UInt256.ofNat zc :: cC2 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 58 := by
  opt44_reach [8316, 8317, 8318, 8319, 8320, 8321, 8322, 8323, 8324, 8325, 8326, 8327, 8328, 8329,
    8330, 8331, 8332] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 18164 (UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem)
      (callState s 18228 (UInt256.ofNat 43264 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt44_reach [8333, 8334, 8335, 8336, 8337]

theorem iC_cont (pj zc : Nat) (hpj : pj < 60000) (hzc : zc < 60000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 18477 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18228 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt44_reach [8515, 8516, 8517, 8518, 8519, 8520, 8521, 8522, 8523, 8524, 8525, 8526, 8527]

theorem iC_exit (pj zc : Nat) (hpj : pj < 60000) (hzc : zc < 60000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 18477 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18502 (UInt256.ofNat 43264 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt44_reach [8515, 8516, 8517, 8518, 8519, 8520, 8521, 8522, 8523, 8524, 8525, 8526, 8527, 8528,
    8529, 8530, 8531]

theorem iB_ci (pj zb : Nat) (hpj : pj < 60000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18997 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18502 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [8897, 8898, 8899, 8900, 8901, 8902, 8903] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 18997 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18502 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt44_reach [8897, 8898, 8899, 8900, 8901, 8902, 8903, 8904, 8905, 8906, 8907, 8908, 8909, 8910,
    8911, 8912, 8913, 8914, 8915, 8916] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 18997 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19036 (UInt256.ofNat 43264 :: UInt256.ofNat 44288 :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt44_reach [8897, 8898, 8899, 8900, 8901, 8902, 8903, 8904, 8905, 8906, 8907, 8908, 8909, 8910,
    8911, 8912, 8913, 8914, 8915, 8916, 8917, 8918, 8919, 8920, 8921, 8922] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 44288) :
    Reach (callState s 19629 (UInt256.ofNat pj :: UInt256.ofNat 44288 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 19036 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 44288 :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [9316, 9317, 9318, 9319, 9320, 9321, 9322]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 44288)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 19629 (UInt256.ofNat pj :: UInt256.ofNat 44288 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt44_reach [9316, 9317, 9318, 9319, 9320, 9321, 9322, 9323, 9324, 9325, 9326, 9327, 9328] with [hj]

end

end MlDsaOpt44.Proofs.NttW
