import MlDsaOpt44.Fn.Ntt.V4.Step
/-!
# Prologues, loop control and exits of the v4 `ntt` / `intt` (WP G, H)

As in v3 (`Fn/Ntt/Ctl.lean`), each loop ends with a pointer update and a
compare: `*_cont` is the taken back edge, `*_exit` the fall-through into the
next pass (or the return); pass B has an inner (`ci`) and an outer (`co`) back
edge. v4's forward NTT keeps no `2q` constant on the stack.
-/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

local notation "cM" => UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855
local notation "cCI" => UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960) (mem : ByteArray)
  (ret : Nat)
include hs htail

/-! ## Forward -/

theorem f_pro :
    Reach (callState s 16548 (UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem)
      (callState s 16584 (UInt256.ofNat 32768 :: UInt256.ofNat 33792 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem) 16 := by
  opt44_reach [7507, 7508, 7509, 7510, 7511, 7512]

theorem fA_cont (pj : Nat) (hpj : 32 + pj < 33792) :
    Reach (callState s 17033 (UInt256.ofNat pj :: UInt256.ofNat 33792 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 16584 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 33792 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [7802, 7803, 7804, 7805, 7806, 7807, 7808]

theorem fA_exit (pj : Nat) (hpj : 32 + pj = 33792) :
    Reach (callState s 17033 (UInt256.ofNat pj :: UInt256.ofNat 33792 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17049 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 38 := by
  opt44_reach [7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812]

theorem fB_ci (pj zb : Nat) (hpj : pj < 60000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 17508 (UInt256.ofNat pj :: UInt256.ofNat zb :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17049 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [8142, 8143, 8144, 8145, 8146, 8147, 8148] with [land127]

theorem fB_co (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb < 5888) :
    Reach (callState s 17508 (UInt256.ofNat pj :: UInt256.ofNat zb :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17049 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (224 + zb) :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 68 := by
  opt44_reach [8142, 8143, 8144, 8145, 8146, 8147, 8148, 8149, 8150, 8151, 8152, 8153, 8154, 8155,
    8156, 8157, 8158, 8159] with [land127]

theorem fB_ex (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (hm : (32 + pj) % 128 = 0)
    (hz : 224 + zb = 5888) :
    Reach (callState s 17508 (UInt256.ofNat pj :: UInt256.ofNat zb :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17543 (UInt256.ofNat 32768 :: UInt256.ofNat 5888 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 78 := by
  opt44_reach [8142, 8143, 8144, 8145, 8146, 8147, 8148, 8149, 8150, 8151, 8152, 8153, 8154, 8155,
    8156, 8157, 8158, 8159, 8160, 8161, 8162, 8163] with [land127]

theorem fC_cont (pj zc : Nat) (hpj : pj < 60000) (hz : 96 + zc < 12032) :
    Reach (callState s 17700 (UInt256.ofNat pj :: UInt256.ofNat zc :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17543 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (96 + zc) :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 40 := by
  opt44_reach [8281, 8282, 8283, 8284, 8285, 8286, 8287, 8288, 8289, 8290, 8291]

theorem fC_exit (pj zc : Nat) (hpj : pj < 60000) (hz : 96 + zc = 12032)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 17700 (UInt256.ofNat pj :: UInt256.ofNat zc :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 56 := by
  opt44_reach [8281, 8282, 8283, 8284, 8285, 8286, 8287, 8288, 8289, 8290, 8291, 8292, 8293, 8294,
    8295, 8296] with [hj]

/-! ## Inverse (as v3) -/

theorem i_pro :
    Reach (callState s 17722 (UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem)
      (callState s 17786 (UInt256.ofNat 43264 :: UInt256.ofNat 11936 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  opt44_reach [8297, 8298, 8299, 8300, 8301]

theorem iC_cont (pj zc : Nat) (hpj : pj < 60000) (hzc : zc < 60000) (h96 : 96 ≤ zc)
    (hz : 5888 ≤ zc - 96) :
    Reach (callState s 18031 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 17786 (UInt256.ofNat (128 + pj) :: UInt256.ofNat (zc - 96) :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 46 := by
  opt44_reach [8475, 8476, 8477, 8478, 8479, 8480, 8481, 8482, 8483, 8484, 8485, 8486, 8487]

theorem iC_exit (pj zc : Nat) (hpj : pj < 60000) (hzc : zc < 60000) (h96 : 96 ≤ zc)
    (hz : zc - 96 < 5888) :
    Reach (callState s 18031 (UInt256.ofNat pj :: UInt256.ofNat zc :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18056 (UInt256.ofNat 43264 :: UInt256.ofNat 5664 :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 56 := by
  opt44_reach [8475, 8476, 8477, 8478, 8479, 8480, 8481, 8482, 8483, 8484, 8485, 8486, 8487, 8488,
    8489, 8490, 8491]

theorem iB_ci (pj zb : Nat) (hpj : pj < 60000) (hm : (32 + pj) % 128 ≠ 0) :
    Reach (callState s 18539 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18056 (UInt256.ofNat (32 + pj) :: UInt256.ofNat zb :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [8845, 8846, 8847, 8848, 8849, 8850, 8851] with [land127]

theorem iB_co (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : 4096 ≤ zb - 224) :
    Reach (callState s 18539 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18056 (UInt256.ofNat (896 + (32 + pj)) :: UInt256.ofNat (zb - 224) :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 74 := by
  opt44_reach [8845, 8846, 8847, 8848, 8849, 8850, 8851, 8852, 8853, 8854, 8855, 8856, 8857, 8858,
    8859, 8860, 8861, 8862, 8863, 8864] with [land127]

theorem iB_ex (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (h224 : 224 ≤ zb)
    (hm : (32 + pj) % 128 = 0) (hz : zb - 224 < 4096) :
    Reach (callState s 18539 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18578 (UInt256.ofNat 43264 :: UInt256.ofNat 44288 :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 90 := by
  opt44_reach [8845, 8846, 8847, 8848, 8849, 8850, 8851, 8852, 8853, 8854, 8855, 8856, 8857, 8858,
    8859, 8860, 8861, 8862, 8863, 8864, 8865, 8866, 8867, 8868, 8869, 8870] with [land127]

theorem iA_cont (pj : Nat) (hpj : 32 + pj < 44288) :
    Reach (callState s 20519 (UInt256.ofNat pj :: UInt256.ofNat 44288 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 18578 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 44288 :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 28 := by
  opt44_reach [9636, 9637, 9638, 9639, 9640, 9641, 9642]

theorem iA_exit (pj : Nat) (hpj : 32 + pj = 44288)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 20519 (UInt256.ofNat pj :: UInt256.ofNat 44288 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 46 := by
  opt44_reach [9636, 9637, 9638, 9639, 9640, 9641, 9642, 9643, 9644, 9645, 9646, 9647, 9648] with [hj]

end

end MlDsaOpt44.Proofs.Ntt4
