import MlDsaOptGlam44.Fn.Ntt.Zeta
/-!
# Prologues, loop control and exits of the glam `ntt` / `intt`

Each pass is one loop of 16 iterations ending with a pointer update and a
compare: `*_cont` is the taken back edge, `*_exit` the fall-through into the
next pass (or the return). The inverse's second pass keeps UseHint's four wide
constants on the stack (`cU3 … cU0`).
-/

namespace MlDsaOptGlam44.Proofs.NttG

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.Ntt4
open MlDsaOptGlam44.Proofs MlDsaOptGlam44.Proofs.Infra

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

local notation "cM" => UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855
local notation "cCI" => UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723
local notation "cU0" => UInt256.ofNat 3207598986782593870493972684755717093467514342740420773020159
local notation "cU1" => UInt256.ofNat 276192476357013953623747158765658614701703779022658540142636
local notation "cU2" => UInt256.ofNat 102837757730839990959496584137676933742227568448368519617200127
local notation "cU3" => UInt256.ofNat 6421475075300574421752121441301562791814612862276811058316287

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950) (mem : ByteArray)
  (ret : Nat)
include hs htail

/-! ## Forward -/

theorem f_pro :
    Reach (callState s 23725 (UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem)
      (callState s 23761 (UInt256.ofNat 32768 :: UInt256.ofNat 33280 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem) 16 := by
  glam44_rreach [10350, 10351, 10352, 10353, 10354, 10355]

theorem fwA_cont (pj : Nat) (hpj : 32 + pj < 33280) :
    Reach (callState s 24939 (UInt256.ofNat pj :: UInt256.ofNat 33280 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 23761 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 33280 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 28 := by
  glam44_rreach [11089, 11090, 11091, 11092, 11093, 11094, 11095]

theorem fwA_exit (pj : Nat) (hpj : 32 + pj = 33280) :
    Reach (callState s 24939 (UInt256.ofNat pj :: UInt256.ofNat 33280 :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 24955 (UInt256.ofNat 32768 :: UInt256.ofNat 4096 :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 38 := by
  glam44_rreach [11089, 11090, 11091, 11092, 11093, 11094, 11095, 11096, 11097, 11098, 11099]

theorem fwB_cont (pj zb : Nat) (hpj : pj < 60000) (hz : 480 + zb < 11776) :
    Reach (callState s 26287 (UInt256.ofNat pj :: UInt256.ofNat zb :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 24955 (UInt256.ofNat (512 + pj) :: UInt256.ofNat (480 + zb) :: cM ::
        UInt256.ofNat 32768 :: UInt256.ofNat ret :: tail) mem) 40 := by
  glam44_rreach [11938, 11939, 11940, 11941, 11942, 11943, 11944, 11945, 11946, 11947, 11948]

theorem fwB_exit (pj zb : Nat) (hpj : pj < 60000) (hz : 480 + zb = 11776)
    (hj : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 26287 (UInt256.ofNat pj :: UInt256.ofNat zb :: cM :: UInt256.ofNat 32768 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 56 := by
  glam44_rreach [11938, 11939, 11940, 11941, 11942, 11943, 11944, 11945, 11946, 11947, 11948, 11949,
    11950, 11951, 11952, 11953] with [hj]

/-! ## Inverse -/

theorem i_pro :
    Reach (callState s 26311 (UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem)
      (callState s 26375 (UInt256.ofNat 43264 :: UInt256.ofNat 11296 :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem) 13 := by
  glam44_rreach [11954, 11955, 11956, 11957, 11958]

theorem inA_cont (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (h480 : 480 ≤ zb)
    (hz : 4096 ≤ zb - 480) :
    Reach (callState s 28133 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 26375 (UInt256.ofNat (512 + pj) :: UInt256.ofNat (zb - 480) :: cCI :: cM ::
        UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 46 := by
  glam44_rreach [13053, 13054, 13055, 13056, 13057, 13058, 13059, 13060, 13061, 13062, 13063, 13064,
    13065]

theorem inA_exit (pj zb : Nat) (hpj : pj < 60000) (hzb : zb < 60000) (h480 : 480 ≤ zb)
    (hz : zb - 480 < 4096) :
    Reach (callState s 28133 (UInt256.ofNat pj :: UInt256.ofNat zb :: cCI :: cM :: UInt256.ofNat 43264 ::
        UInt256.ofNat ret :: tail) mem)
      (callState s 28269 (UInt256.ofNat 43264 :: UInt256.ofNat 43776 :: cU3 :: cU2 :: cU1 :: cU0 :: cCI ::
        cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 74 := by
  glam44_rreach [13053, 13054, 13055, 13056, 13057, 13058, 13059, 13060, 13061, 13062, 13063, 13064,
    13065, 13066, 13067, 13068, 13069, 13070, 13071, 13072, 13073, 13074, 13075]

theorem inB_cont (pj : Nat) (hpj : 32 + pj < 43776) :
    Reach (callState s 30913 (UInt256.ofNat pj :: UInt256.ofNat 43776 :: cU3 :: cU2 :: cU1 :: cU0 :: cCI ::
        cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem)
      (callState s 28269 (UInt256.ofNat (32 + pj) :: UInt256.ofNat 43776 :: cU3 :: cU2 :: cU1 :: cU0 ::
        cCI :: cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem) 28 := by
  glam44_rreach [14785, 14786, 14787, 14788, 14789, 14790, 14791]

theorem inB_exit (pj : Nat) (hpj : 32 + pj = 43776)
    (hj : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 30913 (UInt256.ofNat pj :: UInt256.ofNat 43776 :: cU3 :: cU2 :: cU1 :: cU0 :: cCI ::
        cM :: UInt256.ofNat 43264 :: UInt256.ofNat ret :: tail) mem)
      (callState s ret tail mem) 54 := by
  glam44_rreach [14785, 14786, 14787, 14788, 14789, 14790, 14791, 14792, 14793, 14794, 14795, 14796,
    14797, 14798, 14799, 14800, 14801] with [hj]

end

end MlDsaOptGlam44.Proofs.NttG
