import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-!
# `gfix`: straight-line blocks

Slot-check heads at pcs `13164, 18407, 18459, 18511` and the exit `18563`, stack
`flags :: ok :: amask :: ret :: tail`. Bit 0 of `flags` records that `blkt`
has made the tail of block 4 (before the group's first `fix`).
-/

namespace MlDsaOptGlam87.Proofs.Fix

open MlDsaOpt87.Proofs

-- port: the 44 `Fix` namespace is not imported here
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

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
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M ≠ 0) :
    Reach (callState s 18160 (wd amask :: wd ret :: tail) M)
      (callState s 18358 (wd (gflags M) :: wd 1 :: wd amask :: wd ret :: tail) M) 317 := by
  glam87_rreach [7628, 7629, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644, 7645, 7646, 7647, 7648, 7649, 7650, 7651, 7652, 7653, 7654, 7655, 7656, 7657, 7658, 7659, 7660, 7661, 7662, 7663, 7664, 7665, 7666, 7667, 7668, 7669, 7670, 7671, 7672, 7673, 7674, 7675, 7676, 7677, 7678, 7679, 7680, 7681, 7682, 7683, 7684, 7685, 7686, 7687, 7688, 7689, 7690, 7691, 7692, 7693, 7694, 7695, 7696, 7697, 7698, 7699, 7700, 7701, 7702, 7703, 7704, 7705, 7706, 7707, 7708, 7709, 7710, 7711, 7712, 7713, 7714, 7715, 7716, 7717, 7718, 7719, 7720, 7721, 7722, 7723, 7724, 7725, 7726, 7727, 7728, 7729, 7730, 7731] with [gflags_def, gflags_mod, hf]
  gx_close

theorem gx_fast {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M = 0) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 18160 (wd amask :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) M) 336 := by
  glam87_rreach [7628, 7629, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644, 7645, 7646, 7647, 7648, 7649, 7650, 7651, 7652, 7653, 7654, 7655, 7656, 7657, 7658, 7659, 7660, 7661, 7662, 7663, 7664, 7665, 7666, 7667, 7668, 7669, 7670, 7671, 7672, 7673, 7674, 7675, 7676, 7677, 7678, 7679, 7680, 7681, 7682, 7683, 7684, 7685, 7686, 7687, 7688, 7689, 7690, 7691, 7692, 7693, 7694, 7695, 7696, 7697, 7698, 7699, 7700, 7701, 7702, 7703, 7704, 7705, 7706, 7707, 7708, 7709, 7710, 7711, 7712, 7713, 7714, 7715, 7716, 7717, 7718, 7719, 7720, 7721, 7722, 7723, 7724, 7725, 7726, 7727, 7728, 7729, 7730, 7731, 7868, 7869, 7870, 7871, 7872, 7873] with [gflags_def, gflags_mod, hf, hj]
  gx_close

theorem gx_skip0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 0) :
    Reach (callState s 18358 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18407 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 42 := by
  glam87_rreach [7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 18358 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17211 (wd 18389 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 78 := by
  glam87_rreach [7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743, 7744, 7745, 7746, 7747, 7748, 7749, 7750, 7751] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 18389 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 0 :: wd 18402 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 24 := by
  glam87_rreach [7752, 7753, 7754, 7755, 7756, 7757, 7758, 7759]
  gx_close

theorem gx_callF0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 18358 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 0 :: wd 18402 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 81 := by
  glam87_rreach [7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743, 7744, 7745, 7746, 7747, 7748, 7755, 7756, 7757, 7758, 7759] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 18402 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18407 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam87_rreach [7760, 7761, 7762, 7763, 7764]
  gx_close

theorem gx_skip1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 0) :
    Reach (callState s 18407 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18459 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam87_rreach [7765, 7766, 7767, 7768, 7769, 7770, 7771, 7772, 7773, 7774, 7775, 7776, 7777] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 18407 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17211 (wd 18440 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam87_rreach [7765, 7766, 7767, 7768, 7769, 7770, 7771, 7772, 7773, 7774, 7775, 7776, 7777, 7778, 7779, 7780, 7781, 7782, 7783, 7784, 7785] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 18440 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 64 :: wd 18454 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam87_rreach [7786, 7787, 7788, 7789, 7790, 7791, 7792, 7793]
  gx_close

theorem gx_callF1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 18407 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 64 :: wd 18454 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam87_rreach [7765, 7766, 7767, 7768, 7769, 7770, 7771, 7772, 7773, 7774, 7775, 7776, 7777, 7778, 7779, 7780, 7781, 7782, 7789, 7790, 7791, 7792, 7793] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 18454 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18459 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam87_rreach [7794, 7795, 7796, 7797, 7798]
  gx_close

theorem gx_skip2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 0) :
    Reach (callState s 18459 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18511 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam87_rreach [7799, 7800, 7801, 7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 18459 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17211 (wd 18492 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam87_rreach [7799, 7800, 7801, 7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812, 7813, 7814, 7815, 7816, 7817, 7818, 7819] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 18492 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 128 :: wd 18506 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam87_rreach [7820, 7821, 7822, 7823, 7824, 7825, 7826, 7827]
  gx_close

theorem gx_callF2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 18459 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 128 :: wd 18506 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam87_rreach [7799, 7800, 7801, 7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812, 7813, 7814, 7815, 7816, 7823, 7824, 7825, 7826, 7827] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 18506 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18511 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam87_rreach [7828, 7829, 7830, 7831, 7832]
  gx_close

theorem gx_skip3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 0) :
    Reach (callState s 18511 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18563 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  glam87_rreach [7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 18511 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 17211 (wd 18544 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  glam87_rreach [7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845, 7846, 7847, 7848, 7849, 7850, 7851, 7852, 7853] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 18544 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 192 :: wd 18558 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  glam87_rreach [7854, 7855, 7856, 7857, 7858, 7859, 7860, 7861]
  gx_close

theorem gx_callF3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 18511 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 19863 (wd 192 :: wd 18558 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  glam87_rreach [7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845, 7846, 7847, 7848, 7849, 7850, 7857, 7858, 7859, 7860, 7861] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 18558 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 18563 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  glam87_rreach [7862, 7863, 7864, 7865, 7866]
  gx_close

theorem gx_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 18563 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s ret (wd ok :: tail) M) 20 := by
  glam87_rreach [7867, 7868, 7869, 7870, 7871, 7872, 7873]  with [hj]
  gx_close

end MlDsaOptGlam87.Proofs.Fix
