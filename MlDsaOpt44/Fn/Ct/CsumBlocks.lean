import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
/-!
# `csum` (WP10): generated block lemmas of the loop body

Loop head `14744`, stack `[bu, cw, g, sp, TT, ret]` (`bu = TT − 32 u`,
`cw = CW + 128 u`, `sp = SP + 128 u`, `g` the running `n_neg`). Five blocks:
three load-and-add blocks over the 39 `BASES` entries (the `MLOAD` addresses
need `BASES[m] ≤ 6112`), the 16-bit transpose, then the four emits and the
loop test. Definitions mirror the instruction semantics (see `Fn/Hint/PackBlocks`).
-/

set_option linter.unusedVariables false

namespace MlDsaOpt44.Proofs.CS

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

def cs1o0 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 :=
  ((UInt256.ofNat (word M (bu + word M (41440)))) + ((UInt256.ofNat (word M (bu + word M (41408)))) + ((UInt256.ofNat (word M (bu + word M (41376)))) + ((UInt256.ofNat (word M (bu + word M (41344)))) + ((UInt256.ofNat (word M (bu + word M (41312)))) + ((UInt256.ofNat (word M (bu + word M (41280)))) + ((UInt256.ofNat (word M (bu + word M (41248)))) + ((UInt256.ofNat (word M (bu + word M (41216)))) + ((UInt256.ofNat (word M (bu + word M (41184)))) + ((UInt256.ofNat (word M (bu + word M (41152)))) + ((UInt256.ofNat (word M (bu + word M (41120)))) + ((UInt256.ofNat (word M (bu + word M (41088)))) + ((UInt256.ofNat (word M (bu + word M (41056)))) + ((UInt256.ofNat (word M (bu + word M (41024)))) + ((UInt256.ofNat (word M (bu + word M (40992)))) + (UInt256.ofNat (word M (bu + word M (40960)))))))))))))))))))

def cs2o0 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  ((UInt256.ofNat (word M (bu + word M (41952)))) + ((UInt256.ofNat (word M (bu + word M (41920)))) + ((UInt256.ofNat (word M (bu + word M (41888)))) + ((UInt256.ofNat (word M (bu + word M (41856)))) + ((UInt256.ofNat (word M (bu + word M (41824)))) + ((UInt256.ofNat (word M (bu + word M (41792)))) + ((UInt256.ofNat (word M (bu + word M (41760)))) + ((UInt256.ofNat (word M (bu + word M (41728)))) + ((UInt256.ofNat (word M (bu + word M (41696)))) + ((UInt256.ofNat (word M (bu + word M (41664)))) + ((UInt256.ofNat (word M (bu + word M (41632)))) + ((UInt256.ofNat (word M (bu + word M (41600)))) + ((UInt256.ofNat (word M (bu + word M (41568)))) + ((UInt256.ofNat (word M (bu + word M (41536)))) + ((UInt256.ofNat (word M (bu + word M (41504)))) + ((UInt256.ofNat (word M (bu + word M (41472)))) + x0))))))))))))))))

def cs3o0 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  ((UInt256.ofNat (word M (bu + word M (42176)))) + ((UInt256.ofNat (word M (bu + word M (42144)))) + ((UInt256.ofNat (word M (bu + word M (42112)))) + ((UInt256.ofNat (word M (bu + word M (42080)))) + ((UInt256.ofNat (word M (bu + word M (42048)))) + ((UInt256.ofNat (word M (bu + word M (42016)))) + ((UInt256.ofNat (word M (bu + word M (41984)))) + x0)))))))

def cs4o0 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  (((((UInt256.ofNat 6277005955876855982367846414099012818794836107166352343040).land ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).xor ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).shiftRight (UInt256.ofNat 48)))).shiftLeft (UInt256.ofNat 48)).xor ((UInt256.ofNat 6277005955876855982367846414099012818794836107166352343040).land ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).xor ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).shiftRight (UInt256.ofNat 48))))).xor (((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0))

def cs5g (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  ((((g + (UInt256.ofNat (word M (cw)))) + (UInt256.ofNat (word M (32 + cw)))) + (UInt256.ofNat (word M (64 + cw)))) + (UInt256.ofNat (word M (96 + cw))))

def cs5w0 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  (((UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969) * (g + (UInt256.ofNat (word M (cw))))) + (((UInt256.ofNat 411369862228566123880278864766078120783549026323861987005628415).land x0).shiftLeft (UInt256.ofNat 13)))

def cs5w1 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  (((UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969) * ((g + (UInt256.ofNat (word M (cw)))) + (UInt256.ofNat (word M (32 + cw))))) + (((UInt256.ofNat 411369862228566123880278864766078120783549026323861987005628415).land (x0.shiftRight (UInt256.ofNat 16))).shiftLeft (UInt256.ofNat 13)))

def cs5w2 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  (((UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969) * (((g + (UInt256.ofNat (word M (cw)))) + (UInt256.ofNat (word M (32 + cw)))) + (UInt256.ofNat (word M (64 + cw))))) + (((UInt256.ofNat 411369862228566123880278864766078120783549026323861987005628415).land (x0.shiftRight (UInt256.ofNat 32))).shiftLeft (UInt256.ofNat 13)))

def cs5w3 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  (((UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969) * ((((g + (UInt256.ofNat (word M (cw)))) + (UInt256.ofNat (word M (32 + cw)))) + (UInt256.ofNat (word M (64 + cw)))) + (UInt256.ofNat (word M (96 + cw))))) + (((UInt256.ofNat 411369862228566123880278864766078120783549026323861987005628415).land (x0.shiftRight (UInt256.ofNat 48))).shiftLeft (UInt256.ofNat 13)))

theorem cs_b1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 14876 (wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M)
      (callState s 14971 (cs1o0 M bu cw sp g :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M) 286 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hb40960 : word M 40960 ≤ 6112 := by simpa using hB 0 (by norm_num)
  have hb40992 : word M 40992 ≤ 6112 := by simpa using hB 1 (by norm_num)
  have hb41024 : word M 41024 ≤ 6112 := by simpa using hB 2 (by norm_num)
  have hb41056 : word M 41056 ≤ 6112 := by simpa using hB 3 (by norm_num)
  have hb41088 : word M 41088 ≤ 6112 := by simpa using hB 4 (by norm_num)
  have hb41120 : word M 41120 ≤ 6112 := by simpa using hB 5 (by norm_num)
  have hb41152 : word M 41152 ≤ 6112 := by simpa using hB 6 (by norm_num)
  have hb41184 : word M 41184 ≤ 6112 := by simpa using hB 7 (by norm_num)
  have hb41216 : word M 41216 ≤ 6112 := by simpa using hB 8 (by norm_num)
  have hb41248 : word M 41248 ≤ 6112 := by simpa using hB 9 (by norm_num)
  have hb41280 : word M 41280 ≤ 6112 := by simpa using hB 10 (by norm_num)
  have hb41312 : word M 41312 ≤ 6112 := by simpa using hB 11 (by norm_num)
  have hb41344 : word M 41344 ≤ 6112 := by simpa using hB 12 (by norm_num)
  have hb41376 : word M 41376 ≤ 6112 := by simpa using hB 13 (by norm_num)
  have hb41408 : word M 41408 ≤ 6112 := by simpa using hB 14 (by norm_num)
  have hb41440 : word M 41440 ≤ 6112 := by simpa using hB 15 (by norm_num)
  opt44_reach [6703, 6568, 6569, 6705, 6706, 6707, 6573, 6574, 6709, 6710, 6711, 6712, 6579, 6580, 6714, 6715, 6716, 6717, 6585, 6586, 6719, 6720, 6721, 6722, 6591, 6592, 6724, 6725, 6726, 6727, 6597, 6598, 6729, 6730, 6731, 6732, 6603, 6604, 6734, 6735, 6736, 6737, 6609, 6610, 6739, 6740, 6741, 6742, 6615, 6616, 6744, 6745, 6746, 6747, 6621, 6622, 6749, 6750, 6751, 6752, 6627, 6628, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773, 6774, 6775, 6776, 6777, 6778, 6779, 6780, 6781, 6782, 6783, 6784, 6785, 6786, 6787] with [cs1o0, word_mstore_disjoint]

theorem cs_b2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 14971 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M)
      (callState s 15099 (cs2o0 M bu cw sp g x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M) 288 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hb41472 : word M 41472 ≤ 6112 := by simpa using hB 16 (by norm_num)
  have hb41504 : word M 41504 ≤ 6112 := by simpa using hB 17 (by norm_num)
  have hb41536 : word M 41536 ≤ 6112 := by simpa using hB 18 (by norm_num)
  have hb41568 : word M 41568 ≤ 6112 := by simpa using hB 19 (by norm_num)
  have hb41600 : word M 41600 ≤ 6112 := by simpa using hB 20 (by norm_num)
  have hb41632 : word M 41632 ≤ 6112 := by simpa using hB 21 (by norm_num)
  have hb41664 : word M 41664 ≤ 6112 := by simpa using hB 22 (by norm_num)
  have hb41696 : word M 41696 ≤ 6112 := by simpa using hB 23 (by norm_num)
  have hb41728 : word M 41728 ≤ 6112 := by simpa using hB 24 (by norm_num)
  have hb41760 : word M 41760 ≤ 6112 := by simpa using hB 25 (by norm_num)
  have hb41792 : word M 41792 ≤ 6112 := by simpa using hB 26 (by norm_num)
  have hb41824 : word M 41824 ≤ 6112 := by simpa using hB 27 (by norm_num)
  have hb41856 : word M 41856 ≤ 6112 := by simpa using hB 28 (by norm_num)
  have hb41888 : word M 41888 ≤ 6112 := by simpa using hB 29 (by norm_num)
  have hb41920 : word M 41920 ≤ 6112 := by simpa using hB 30 (by norm_num)
  have hb41952 : word M 41952 ≤ 6112 := by simpa using hB 31 (by norm_num)
  opt44_reach [6788, 6789, 6790, 6791, 6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811, 6812, 6813, 6814, 6815, 6816, 6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826, 6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842, 6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858, 6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869, 6870, 6871, 6872, 6873, 6874, 6875, 6876, 6877, 6878, 6879, 6880, 6881, 6882, 6883] with [cs2o0, word_mstore_disjoint]

theorem cs_b3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 15099 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M)
      (callState s 15155 (cs3o0 M bu cw sp g x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M) 126 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hb41984 : word M 41984 ≤ 6112 := by simpa using hB 32 (by norm_num)
  have hb42016 : word M 42016 ≤ 6112 := by simpa using hB 33 (by norm_num)
  have hb42048 : word M 42048 ≤ 6112 := by simpa using hB 34 (by norm_num)
  have hb42080 : word M 42080 ≤ 6112 := by simpa using hB 35 (by norm_num)
  have hb42112 : word M 42112 ≤ 6112 := by simpa using hB 36 (by norm_num)
  have hb42144 : word M 42144 ≤ 6112 := by simpa using hB 37 (by norm_num)
  have hb42176 : word M 42176 ≤ 6112 := by simpa using hB 38 (by norm_num)
  opt44_reach [6884, 6885, 6886, 6887, 6888, 6889, 6890, 6891, 6892, 6893, 6894, 6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905, 6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914, 6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925] with [cs3o0, word_mstore_disjoint]

theorem cs_b4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 15155 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M)
      (callState s 15223 (cs4o0 M bu cw sp g x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M) 72 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933, 6934, 6935, 6936, 6937, 6938, 6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946, 6947, 6948, 6949] with [cs4o0, word_mstore_disjoint]

theorem cs_b5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112)
    (hlt : cw + 128 < 20480) :
    Reach (callState s 15223 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M)
      (callState s 14876 (wd (bu - 32) :: wd (128 + cw) :: cs5g M bu cw sp g x0 :: wd (128 + sp) :: wd 20480 :: wd (ret) :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (cs5w0 M bu cw sp g x0).toNat 32) (sp)) (Data.Bytes.natToBytesPadded (cs5w1 M bu cw sp g x0).toNat 32) (32 + sp)) (Data.Bytes.natToBytesPadded (cs5w2 M bu cw sp g x0).toNat 32) (64 + sp)) (Data.Bytes.natToBytesPadded (cs5w3 M bu cw sp g x0).toNat 32) (96 + sp))) 319 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6950, 6951, 6952, 6828, 6954, 6955, 6956, 6832, 6833, 6957, 6958, 6961, 6837, 6838, 6839, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6847, 6971, 6972, 6973, 6851, 6975, 6853, 6977, 6855, 6856, 6978, 6858, 6859, 6860, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6870, 6990, 6991, 6992, 6874, 6994, 6876, 6996, 6878, 6879, 6997, 6881, 6882, 6883, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006, 7007, 6893, 7009, 7010, 7011, 6897, 7013, 6899, 7015, 6901, 6902, 7016, 6904, 6905, 6906, 7018, 7019, 7020, 7021, 7022, 7023, 7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038] with [cs5w0, cs5w1, cs5w2, cs5w3, cs5g, word_mstore_disjoint]

theorem cs_b5x {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112)
    (hlt : cw + 128 = 20480) :
    Reach (callState s 15223 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd 20480 :: wd (ret) :: tail) M)
      (callState s 15441 (wd (bu - 32) :: wd (128 + cw) :: cs5g M bu cw sp g x0 :: wd (128 + sp) :: wd 20480 :: wd (ret) :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (cs5w0 M bu cw sp g x0).toNat 32) (sp)) (Data.Bytes.natToBytesPadded (cs5w1 M bu cw sp g x0).toNat 32) (32 + sp)) (Data.Bytes.natToBytesPadded (cs5w2 M bu cw sp g x0).toNat 32) (64 + sp)) (Data.Bytes.natToBytesPadded (cs5w3 M bu cw sp g x0).toNat 32) (96 + sp))) 319 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6950, 6951, 6952, 6828, 6954, 6955, 6956, 6832, 6833, 6957, 6958, 6961, 6837, 6838, 6839, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6847, 6971, 6972, 6973, 6851, 6975, 6853, 6977, 6855, 6856, 6978, 6858, 6859, 6860, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6870, 6990, 6991, 6992, 6874, 6994, 6876, 6996, 6878, 6879, 6997, 6881, 6882, 6883, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006, 7007, 6893, 7009, 7010, 7011, 6897, 7013, 6899, 7015, 6901, 6902, 7016, 6904, 6905, 6906, 7018, 7019, 7020, 7021, 7022, 7023, 7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038] with [cs5w0, cs5w1, cs5w2, cs5w3, cs5g, word_mstore_disjoint]


end MlDsaOpt44.Proofs.CS
