import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py 65` --sub 65280=89856 --sub 66080=90656; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-!
# `gfix`: straight-line blocks

Slot-check heads at pcs `11775, 17496, 17548, 17600` and the exit `17652`, stack
`flags :: ok :: amask :: ret :: tail`. Bit 0 of `flags` records that `blkt`
has made the tail of block 4 (before the group's first `fix`).
-/

namespace MlDsaOptGlam65.Proofs.Fix

open MlDsaOpt65.Proofs

-- port: the 44 `Fix` namespace is not imported here
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

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
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M ≠ 0) :
    Reach (callState s 17249 (wd amask :: wd ret :: tail) M)
      (callState s 17447 (wd (gflags M) :: wd 1 :: wd amask :: wd ret :: tail) M) 317 := by
  glam65_rreach [7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038, 7039, 7040, 7041, 7042, 7043, 7044, 7045, 7046, 7047, 7048, 7049, 7050, 7051, 7052, 7053, 7054, 7055, 7056, 7057, 7058, 7059, 7060, 7061, 7062, 7063, 7064, 7065, 7066, 7067, 7068, 7069, 7070, 7071, 7072, 7073, 7074, 7075, 7076, 7077, 7078, 7079, 7080, 7081, 7082, 7083, 7084, 7085, 7086, 7087, 7088, 7089, 7090, 7091, 7092, 7093, 7094, 7095, 7096, 7097, 7098, 7099, 7100, 7101, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117, 7118, 7119, 7120, 7121, 7122, 7123, 7124, 7125, 7126, 7127] with [gflags_def, gflags_mod, hf]
  gx_close

theorem gx_fast {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M = 0) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam65.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 17249 (wd amask :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) M) 336 := by
  glam65_rreach [7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038, 7039, 7040, 7041, 7042, 7043, 7044, 7045, 7046, 7047, 7048, 7049, 7050, 7051, 7052, 7053, 7054, 7055, 7056, 7057, 7058, 7059, 7060, 7061, 7062, 7063, 7064, 7065, 7066, 7067, 7068, 7069, 7070, 7071, 7072, 7073, 7074, 7075, 7076, 7077, 7078, 7079, 7080, 7081, 7082, 7083, 7084, 7085, 7086, 7087, 7088, 7089, 7090, 7091, 7092, 7093, 7094, 7095, 7096, 7097, 7098, 7099, 7100, 7101, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117, 7118, 7119, 7120, 7121, 7122, 7123, 7124, 7125, 7126, 7127, 7264, 7265, 7266, 7267, 7268, 7269] with [gflags_def, gflags_mod, hf, hj]
  gx_close

theorem gx_skip0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 0) :
    Reach (callState s 17447 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17496 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 42 := by
  glam65_rreach [7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17447 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16552 (wd 17478 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 78 := by
  glam65_rreach [7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139, 7140, 7141, 7142, 7143, 7144, 7145, 7146, 7147] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17478 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 0 :: wd 17491 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 24 := by
  glam65_rreach [7148, 7149, 7150, 7151, 7152, 7153, 7154, 7155]
  gx_close

theorem gx_callF0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17447 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 0 :: wd 17491 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 81 := by
  glam65_rreach [7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139, 7140, 7141, 7142, 7143, 7144, 7151, 7152, 7153, 7154, 7155] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17491 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17496 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam65_rreach [7156, 7157, 7158, 7159, 7160]
  gx_close

theorem gx_skip1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 0) :
    Reach (callState s 17496 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17548 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam65_rreach [7161, 7162, 7163, 7164, 7165, 7166, 7167, 7168, 7169, 7170, 7171, 7172, 7173] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17496 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16552 (wd 17529 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam65_rreach [7161, 7162, 7163, 7164, 7165, 7166, 7167, 7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7181] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17529 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 64 :: wd 17543 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam65_rreach [7182, 7183, 7184, 7185, 7186, 7187, 7188, 7189]
  gx_close

theorem gx_callF1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17496 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 64 :: wd 17543 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam65_rreach [7161, 7162, 7163, 7164, 7165, 7166, 7167, 7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7185, 7186, 7187, 7188, 7189] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17543 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17548 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam65_rreach [7190, 7191, 7192, 7193, 7194]
  gx_close

theorem gx_skip2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 0) :
    Reach (callState s 17548 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17600 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam65_rreach [7195, 7196, 7197, 7198, 7199, 7200, 7201, 7202, 7203, 7204, 7205, 7206, 7207] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17548 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16552 (wd 17581 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam65_rreach [7195, 7196, 7197, 7198, 7199, 7200, 7201, 7202, 7203, 7204, 7205, 7206, 7207, 7208, 7209, 7210, 7211, 7212, 7213, 7214, 7215] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17581 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 128 :: wd 17595 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam65_rreach [7216, 7217, 7218, 7219, 7220, 7221, 7222, 7223]
  gx_close

theorem gx_callF2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17548 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 128 :: wd 17595 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam65_rreach [7195, 7196, 7197, 7198, 7199, 7200, 7201, 7202, 7203, 7204, 7205, 7206, 7207, 7208, 7209, 7210, 7211, 7212, 7219, 7220, 7221, 7222, 7223] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17595 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17600 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam65_rreach [7224, 7225, 7226, 7227, 7228]
  gx_close

theorem gx_skip3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 0) :
    Reach (callState s 17600 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17652 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam65_rreach [7229, 7230, 7231, 7232, 7233, 7234, 7235, 7236, 7237, 7238, 7239, 7240, 7241] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 17600 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 16552 (wd 17633 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam65_rreach [7229, 7230, 7231, 7232, 7233, 7234, 7235, 7236, 7237, 7238, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7247, 7248, 7249] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 17633 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 192 :: wd 17647 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam65_rreach [7250, 7251, 7252, 7253, 7254, 7255, 7256, 7257]
  gx_close

theorem gx_callF3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 17600 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 20056 (wd 192 :: wd 17647 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam65_rreach [7229, 7230, 7231, 7232, 7233, 7234, 7235, 7236, 7237, 7238, 7239, 7240, 7241, 7242, 7243, 7244, 7245, 7246, 7253, 7254, 7255, 7256, 7257] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 17647 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17652 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam65_rreach [7258, 7259, 7260, 7261, 7262]
  gx_close

theorem gx_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 3384 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam65.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 17652 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s ret (wd ok :: tail) M) 20 := by
  glam65_rreach [7263, 7264, 7265, 7266, 7267, 7268, 7269]  with [hj]
  gx_close

end MlDsaOptGlam65.Proofs.Fix
