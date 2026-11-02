import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-!
# `gfix`: straight-line blocks

Slot-check heads at pcs `10699, 17838, 17890, 17942` and the exit `17994`, stack
`flags :: ok :: amask :: ret :: tail`. Bit 0 of `flags` records that `blkt`
has made the tail of block 4 (before the group's first `fix`).
-/

namespace MlDsaOptGlam44.Proofs.Fix

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

/-- The OR of the first 32 flag words, masked to bit 23 of each lane (as `gfix` computes it). -/
def gflags (M : ByteArray) : Nat :=
  52656145834278593351813509227247135921718862144084218434291761152 &&&
    (word M 32224 ||| (word M 32192 ||| (word M 32160 ||| (word M 32128 ||| (word M 32096 ||| (word M 32064 ||| (word M 32032 ||| (word M 32000 ||| (word M 31968 ||| (word M 31936 ||| (word M 31904 ||| (word M 31872 ||| (word M 31840 ||| (word M 31808 ||| (word M 31776 ||| (word M 31744 ||| (word M 31712 ||| (word M 31680 ||| (word M 31648 ||| (word M 31616 ||| (word M 31584 ||| (word M 31552 ||| (word M 31520 ||| (word M 31488 ||| (word M 31456 ||| (word M 31424 ||| (word M 31392 ||| (word M 31360 ||| (word M 31328 ||| (word M 31296 ||| (word M 31264 ||| (word M 31232))))))))))))))))))))))))))))))))

theorem gflags_def (M : ByteArray) : 52656145834278593351813509227247135921718862144084218434291761152 &&&
    (word M 32224 ||| (word M 32192 ||| (word M 32160 ||| (word M 32128 ||| (word M 32096 ||| (word M 32064 ||| (word M 32032 ||| (word M 32000 ||| (word M 31968 ||| (word M 31936 ||| (word M 31904 ||| (word M 31872 ||| (word M 31840 ||| (word M 31808 ||| (word M 31776 ||| (word M 31744 ||| (word M 31712 ||| (word M 31680 ||| (word M 31648 ||| (word M 31616 ||| (word M 31584 ||| (word M 31552 ||| (word M 31520 ||| (word M 31488 ||| (word M 31456 ||| (word M 31424 ||| (word M 31392 ||| (word M 31360 ||| (word M 31328 ||| (word M 31296 ||| (word M 31264 ||| (word M 31232)))))))))))))))))))))))))))))))) = gflags M := rfl

theorem gflags_lt (M : ByteArray) : gflags M < 2 ^ 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem gflags_mod (M : ByteArray) :
    gflags M % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = gflags M :=
  Nat.mod_eq_of_lt (gflags_lt M)

theorem gone_land (x : Nat) : 1 &&& x = x % 2 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 1

theorem gmod2_mod (x : Nat) :
    x % 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = x % 2 :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

macro "gx_close" : tactic => `(tactic| (all_goals first | (congr 1; omega) | rfl | skip))


theorem gx_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M ≠ 0) :
    Reach (callState s 17591 (wd amask :: wd ret :: tail) M)
      (callState s 17789 (wd (gflags M) :: wd 1 :: wd amask :: wd ret :: tail) M) 317 := by
  glam44_rreach [7101, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117, 7118, 7119, 7120, 7121, 7122, 7123, 7124, 7125, 7126, 7127, 7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139, 7140, 7141, 7142, 7143, 7144, 7145, 7146, 7147, 7148, 7149, 7150, 7151, 7152, 7153, 7154, 7155, 7156, 7157, 7158, 7159, 7160, 7161, 7162, 7163, 7164, 7165, 7166, 7167, 7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7181, 7182, 7183, 7184, 7185, 7186, 7187, 7188, 7189, 7190, 7191, 7192, 7193, 7194, 7195, 7196, 7197, 7198, 7199, 7200, 7201, 7202, 7203, 7204] with [gflags_def, gflags_mod, hf]
  gx_close

theorem gx_fast {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M = 0) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 17591 (wd amask :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) M) 336 := by
  glam44_rreach [7101, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117, 7118, 7119, 7120, 7121, 7122, 7123, 7124, 7125, 7126, 7127, 7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139, 7140, 7141, 7142, 7143, 7144, 7145, 7146, 7147, 7148, 7149, 7150, 7151, 7152, 7153, 7154, 7155, 7156, 7157, 7158, 7159, 7160, 7161, 7162, 7163, 7164, 7165, 7166, 7167, 7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7181, 7182, 7183, 7184, 7185, 7186, 7187, 7188, 7189, 7190, 7191, 7192, 7193, 7194, 7195, 7196, 7197, 7198, 7199, 7200, 7201, 7202, 7203, 7204, 7341, 7342, 7343, 7344, 7345, 7346] with [gflags_def, gflags_mod, hf, hj]
  gx_close

theorem gx_skip0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 0) :
    Reach (callState s 17789 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17838 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 42 := by
  glam44_rreach [7205, 7206, 7207, 7208, 7209, 7210, 7211, 7212, 7213, 7214, 7215, 7216] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17789 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16846 (wd 17820 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 78 := by
  glam44_rreach [7205, 7206, 7207, 7208, 7209, 7210, 7211, 7212, 7213, 7214, 7215, 7216, 7217, 7218, 7219, 7220, 7221, 7222, 7223, 7224] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17820 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 0 :: wd 17833 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 24 := by
  glam44_rreach [7225, 7226, 7227, 7228, 7229, 7230, 7231, 7232]
  gx_close

theorem gx_callF0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17789 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 0 :: wd 17833 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 81 := by
  glam44_rreach [7205, 7206, 7207, 7208, 7209, 7210, 7211, 7212, 7213, 7214, 7215, 7216, 7217, 7218, 7219, 7220, 7221, 7228, 7229, 7230, 7231, 7232] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17833 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17838 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam44_rreach [7233, 7234, 7235, 7236, 7237]
  gx_close

theorem gx_skip1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 0) :
    Reach (callState s 17838 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17890 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam44_rreach [7238, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7247, 7248, 7249, 7250] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17838 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16846 (wd 17871 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam44_rreach [7238, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7247, 7248, 7249, 7250, 7251, 7252, 7253, 7254, 7255, 7256, 7257, 7258] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17871 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 64 :: wd 17885 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam44_rreach [7259, 7260, 7261, 7262, 7263, 7264, 7265, 7266]
  gx_close

theorem gx_callF1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17838 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 64 :: wd 17885 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam44_rreach [7238, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7247, 7248, 7249, 7250, 7251, 7252, 7253, 7254, 7255, 7262, 7263, 7264, 7265, 7266] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17885 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17890 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam44_rreach [7267, 7268, 7269, 7270, 7271]
  gx_close

theorem gx_skip2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 0) :
    Reach (callState s 17890 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17942 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam44_rreach [7272, 7273, 7274, 7275, 7276, 7277, 7278, 7279, 7280, 7281, 7282, 7283, 7284] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17890 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16846 (wd 17923 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam44_rreach [7272, 7273, 7274, 7275, 7276, 7277, 7278, 7279, 7280, 7281, 7282, 7283, 7284, 7285, 7286, 7287, 7288, 7289, 7290, 7291, 7292] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17923 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 128 :: wd 17937 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam44_rreach [7293, 7294, 7295, 7296, 7297, 7298, 7299, 7300]
  gx_close

theorem gx_callF2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17890 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 128 :: wd 17937 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam44_rreach [7272, 7273, 7274, 7275, 7276, 7277, 7278, 7279, 7280, 7281, 7282, 7283, 7284, 7285, 7286, 7287, 7288, 7289, 7296, 7297, 7298, 7299, 7300] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17937 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17942 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam44_rreach [7301, 7302, 7303, 7304, 7305]
  gx_close

theorem gx_skip3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 0) :
    Reach (callState s 17942 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17994 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam44_rreach [7306, 7307, 7308, 7309, 7310, 7311, 7312, 7313, 7314, 7315, 7316, 7317, 7318] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17942 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16846 (wd 17975 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam44_rreach [7306, 7307, 7308, 7309, 7310, 7311, 7312, 7313, 7314, 7315, 7316, 7317, 7318, 7319, 7320, 7321, 7322, 7323, 7324, 7325, 7326] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17975 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 192 :: wd 17989 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam44_rreach [7327, 7328, 7329, 7330, 7331, 7332, 7333, 7334]
  gx_close

theorem gx_callF3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17942 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20297 (wd 192 :: wd 17989 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam44_rreach [7306, 7307, 7308, 7309, 7310, 7311, 7312, 7313, 7314, 7315, 7316, 7317, 7318, 7319, 7320, 7321, 7322, 7323, 7330, 7331, 7332, 7333, 7334] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17989 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17994 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam44_rreach [7335, 7336, 7337, 7338, 7339]
  gx_close

theorem gx_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 17994 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s ret (wd ok :: tail) M) 20 := by
  glam44_rreach [7340, 7341, 7342, 7343, 7344, 7345, 7346]  with [hj]
  gx_close

end MlDsaOptGlam44.Proofs.Fix
