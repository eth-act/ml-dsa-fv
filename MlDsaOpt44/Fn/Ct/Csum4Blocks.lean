import MlDsaOpt44.Fn.Ct.CsumMath
import MlDsaOpt44.Fn.Ball.Defs
import MlDsaOpt44.Infra.Reflect
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# `csum` (v4, WP I): block lemmas of the loop

Loop head `14876`, stack `[bu, cw, g, sp, b10, …, b0, rest…]` (`bu = TT − 32 u`,
`cw = CW + 128 u`, `sp = SP + 128 u`, `g` the replicated, pre-negated running
count, `b_i = BASES[i]` read once at entry). Blocks: the window loads of bases
0 … 15 (0 … 10 from the stack), 16 … 31, 32 … 38, the 16-bit transpose, then
the four code subtractions and emits and the loop test. The definitions mirror
the instruction semantics; `opt44_reach … with [def]` checks them.
-/

namespace MlDsaOpt44.Proofs.CS4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

def c4e (M : ByteArray) : UInt256 :=
  UInt256.ofNat 6734003226702759863354143558464062379622511764189856289006183085183 - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 * (UInt256.ofNat 39 - UInt256.ofNat (word M 4000))

def c4s1 (M : ByteArray) (bu b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat) : UInt256 :=
  ((UInt256.ofNat (word M (bu + word M (41440)))) + ((UInt256.ofNat (word M (bu + word M (41408)))) + ((UInt256.ofNat (word M (bu + word M (41376)))) + ((UInt256.ofNat (word M (bu + word M (41344)))) + ((UInt256.ofNat (word M (bu + word M (41312)))) + ((UInt256.ofNat (word M (bu + b10))) + ((UInt256.ofNat (word M (bu + b9))) + ((UInt256.ofNat (word M (bu + b8))) + ((UInt256.ofNat (word M (bu + b7))) + ((UInt256.ofNat (word M (bu + b6))) + ((UInt256.ofNat (word M (bu + b5))) + ((UInt256.ofNat (word M (bu + b4))) + ((UInt256.ofNat (word M (bu + b3))) + ((UInt256.ofNat (word M (bu + b2))) + ((UInt256.ofNat (word M (bu + b1))) + (UInt256.ofNat (word M (bu + b0))))))))))))))))))

def c4s2 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  ((UInt256.ofNat (word M (bu + word M (41952)))) + ((UInt256.ofNat (word M (bu + word M (41920)))) + ((UInt256.ofNat (word M (bu + word M (41888)))) + ((UInt256.ofNat (word M (bu + word M (41856)))) + ((UInt256.ofNat (word M (bu + word M (41824)))) + ((UInt256.ofNat (word M (bu + word M (41792)))) + ((UInt256.ofNat (word M (bu + word M (41760)))) + ((UInt256.ofNat (word M (bu + word M (41728)))) + ((UInt256.ofNat (word M (bu + word M (41696)))) + ((UInt256.ofNat (word M (bu + word M (41664)))) + ((UInt256.ofNat (word M (bu + word M (41632)))) + ((UInt256.ofNat (word M (bu + word M (41600)))) + ((UInt256.ofNat (word M (bu + word M (41568)))) + ((UInt256.ofNat (word M (bu + word M (41536)))) + ((UInt256.ofNat (word M (bu + word M (41504)))) + ((UInt256.ofNat (word M (bu + word M (41472)))) + x0))))))))))))))))

def c4s3 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  ((UInt256.ofNat (word M (bu + word M (42176)))) + ((UInt256.ofNat (word M (bu + word M (42144)))) + ((UInt256.ofNat (word M (bu + word M (42112)))) + ((UInt256.ofNat (word M (bu + word M (42080)))) + ((UInt256.ofNat (word M (bu + word M (42048)))) + ((UInt256.ofNat (word M (bu + word M (42016)))) + ((UInt256.ofNat (word M (bu + word M (41984)))) + x0)))))))

def c4T (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256) : UInt256 :=
  (((((UInt256.ofNat 6277005955876855982367846414099012818794836107166352343040).land ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).xor ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).shiftRight (UInt256.ofNat 48)))).shiftLeft (UInt256.ofNat 48)).xor ((UInt256.ofNat 6277005955876855982367846414099012818794836107166352343040).land ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).xor ((((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0).shiftRight (UInt256.ofNat 48))))).xor (((((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96)))).shiftLeft (UInt256.ofNat 96)).xor ((UInt256.ofNat 340282366841710300967557013907638845440).land (x0.xor (x0.shiftRight (UInt256.ofNat 96))))).xor x0))


def c4g1 (M : ByteArray) (cw : Nat) (g : UInt256) : UInt256 := g - UInt256.ofNat (word M cw)
def c4g2 (M : ByteArray) (cw : Nat) (g : UInt256) : UInt256 := c4g1 M cw g - UInt256.ofNat (word M (32 + cw))
def c4g3 (M : ByteArray) (cw : Nat) (g : UInt256) : UInt256 := c4g2 M cw g - UInt256.ofNat (word M (64 + cw))
def c4g4 (M : ByteArray) (cw : Nat) (g : UInt256) : UInt256 := c4g3 M cw g - UInt256.ofNat (word M (96 + cw))
def c4w0 (M : ByteArray) (cw : Nat) (g x : UInt256) : UInt256 := c4g1 M cw g - (UInt256.ofNat 3369941911376413686827244460163711965458833623645077397550107975680).land (x.shiftLeft (UInt256.ofNat 13))
def c4w1 (M : ByteArray) (cw : Nat) (g x : UInt256) : UInt256 := c4g2 M cw g - (UInt256.ofNat 3369941911376413686827244460163711965458833623645077397550107975680).land (x.shiftRight (UInt256.ofNat 3))
def c4w2 (M : ByteArray) (cw : Nat) (g x : UInt256) : UInt256 := c4g3 M cw g - (UInt256.ofNat 3369941911376413686827244460163711965458833623645077397550107975680).land (x.shiftRight (UInt256.ofNat 19))
def c4w3 (M : ByteArray) (cw : Nat) (g x : UInt256) : UInt256 := c4g4 M cw g - (UInt256.ofNat 3369941911376413686827244460163711965458833623645077397550107975680).land (x.shiftRight (UInt256.ofNat 35))

theorem c4_entry {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (sp tt : Nat) :
    Reach (callState s 14762 (wd sp :: wd tt :: rest) M)
      (callState s 14876 (wd tt :: wd 12288 :: c4e M :: wd sp :: wd (word M 41280) :: wd (word M 41248) :: wd (word M 41216) :: wd (word M 41184) :: wd (word M 41152) :: wd (word M 41120) :: wd (word M 41088) :: wd (word M 41056) :: wd (word M 41024) :: wd (word M 40992) :: wd (word M 40960) :: wd sp :: wd tt :: rest) M) 102 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6669, 6670, 6671, 6672, 6673, 6674, 6675, 6676, 6677, 6678, 6679, 6680, 6681, 6682, 6683, 6684, 6685, 6686, 6687, 6688, 6689, 6690, 6691, 6692, 6693, 6694, 6695, 6696, 6697, 6698, 6699, 6700, 6701, 6702] with [c4e]

theorem c4_b1 {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} (hb0 : b0 ≤ 6112) (hb1 : b1 ≤ 6112) (hb2 : b2 ≤ 6112) (hb3 : b3 ≤ 6112) (hb4 : b4 ≤ 6112) (hb5 : b5 ≤ 6112) (hb6 : b6 ≤ 6112) (hb7 : b7 ≤ 6112) (hb8 : b8 ≤ 6112) (hb9 : b9 ≤ 6112) (hb10 : b10 ≤ 6112) (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 14876 (wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M)
      (callState s 14971 (c4s1 M bu b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M) 253 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hm41312 : word M 41312 ≤ 6112 := by simpa using hB 11 (by norm_num)
  have hm41344 : word M 41344 ≤ 6112 := by simpa using hB 12 (by norm_num)
  have hm41376 : word M 41376 ≤ 6112 := by simpa using hB 13 (by norm_num)
  have hm41408 : word M 41408 ≤ 6112 := by simpa using hB 14 (by norm_num)
  have hm41440 : word M 41440 ≤ 6112 := by simpa using hB 15 (by norm_num)
  opt44_reach [6703, 6704, 6705, 6706, 6707, 6708, 6709, 6710, 6711, 6712, 6713, 6714, 6715, 6716, 6717, 6718, 6719, 6720, 6721, 6722, 6723, 6724, 6725, 6726, 6727, 6728, 6729, 6730, 6731, 6732, 6733, 6734, 6735, 6736, 6737, 6738, 6739, 6740, 6741, 6742, 6743, 6744, 6745, 6746, 6747, 6748, 6749, 6750, 6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773, 6774, 6775, 6776, 6777, 6778, 6779, 6780, 6781, 6782, 6783, 6784, 6785, 6786, 6787] with [c4s1, word_mstore_disjoint]

theorem c4_b2 {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 14971 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M)
      (callState s 15099 (c4s2 M bu cw sp g x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M) 288 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hm41472 : word M 41472 ≤ 6112 := by simpa using hB 16 (by norm_num)
  have hm41504 : word M 41504 ≤ 6112 := by simpa using hB 17 (by norm_num)
  have hm41536 : word M 41536 ≤ 6112 := by simpa using hB 18 (by norm_num)
  have hm41568 : word M 41568 ≤ 6112 := by simpa using hB 19 (by norm_num)
  have hm41600 : word M 41600 ≤ 6112 := by simpa using hB 20 (by norm_num)
  have hm41632 : word M 41632 ≤ 6112 := by simpa using hB 21 (by norm_num)
  have hm41664 : word M 41664 ≤ 6112 := by simpa using hB 22 (by norm_num)
  have hm41696 : word M 41696 ≤ 6112 := by simpa using hB 23 (by norm_num)
  have hm41728 : word M 41728 ≤ 6112 := by simpa using hB 24 (by norm_num)
  have hm41760 : word M 41760 ≤ 6112 := by simpa using hB 25 (by norm_num)
  have hm41792 : word M 41792 ≤ 6112 := by simpa using hB 26 (by norm_num)
  have hm41824 : word M 41824 ≤ 6112 := by simpa using hB 27 (by norm_num)
  have hm41856 : word M 41856 ≤ 6112 := by simpa using hB 28 (by norm_num)
  have hm41888 : word M 41888 ≤ 6112 := by simpa using hB 29 (by norm_num)
  have hm41920 : word M 41920 ≤ 6112 := by simpa using hB 30 (by norm_num)
  have hm41952 : word M 41952 ≤ 6112 := by simpa using hB 31 (by norm_num)
  opt44_reach [6788, 6789, 6790, 6791, 6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811, 6812, 6813, 6814, 6815, 6816, 6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826, 6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842, 6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858, 6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869, 6870, 6871, 6872, 6873, 6874, 6875, 6876, 6877, 6878, 6879, 6880, 6881, 6882, 6883] with [c4s2, word_mstore_disjoint]

theorem c4_b3 {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 15099 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M)
      (callState s 15155 (c4s3 M bu cw sp g x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M) 126 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hm41984 : word M 41984 ≤ 6112 := by simpa using hB 32 (by norm_num)
  have hm42016 : word M 42016 ≤ 6112 := by simpa using hB 33 (by norm_num)
  have hm42048 : word M 42048 ≤ 6112 := by simpa using hB 34 (by norm_num)
  have hm42080 : word M 42080 ≤ 6112 := by simpa using hB 35 (by norm_num)
  have hm42112 : word M 42112 ≤ 6112 := by simpa using hB 36 (by norm_num)
  have hm42144 : word M 42144 ≤ 6112 := by simpa using hB 37 (by norm_num)
  have hm42176 : word M 42176 ≤ 6112 := by simpa using hB 38 (by norm_num)
  opt44_reach [6884, 6885, 6886, 6887, 6888, 6889, 6890, 6891, 6892, 6893, 6894, 6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905, 6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914, 6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925] with [c4s3, word_mstore_disjoint]

theorem c4_b4 {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) :
    Reach (callState s 15155 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M)
      (callState s 15223 (c4T M bu cw sp g x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M) 72 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933, 6934, 6935, 6936, 6937, 6938, 6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946, 6947, 6948, 6949] with [c4T, word_mstore_disjoint]

theorem c4_b5 {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hlt : cw + 128 < 20480) :
    Reach (callState s 15223 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M)
      (callState s 14876 (wd (bu - 32) :: wd (128 + cw) :: c4g4 M cw g :: wd (128 + sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (c4w0 M cw g x0).toNat 32) (sp)) (Data.Bytes.natToBytesPadded (c4w1 M cw g x0).toNat 32) (32 + sp)) (Data.Bytes.natToBytesPadded (c4w2 M cw g x0).toNat 32) (64 + sp)) (Data.Bytes.natToBytesPadded (c4w3 M cw g x0).toNat 32) (96 + sp))) 269 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006, 7007, 7008, 7009, 7010, 7011, 7012, 7013, 7014, 7015, 7016, 7017, 7018, 7019, 7020, 7021, 7022, 7023, 7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038] with [c4g1, c4g2, c4g3, c4g4, c4w0, c4w1, c4w2, c4w3, word_mstore_disjoint]

theorem c4_b5x {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963) (M : ByteArray) (bu cw sp : Nat) (g : UInt256) (x0 : UInt256)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480) (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hlt : cw + 128 = 20480) :
    Reach (callState s 15223 (x0 :: wd (bu) :: wd (cw) :: g :: wd (sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) M)
      (callState s 15441 (wd (bu - 32) :: wd (128 + cw) :: c4g4 M cw g :: wd (128 + sp) :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: rest) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (c4w0 M cw g x0).toNat 32) (sp)) (Data.Bytes.natToBytesPadded (c4w1 M cw g x0).toNat 32) (32 + sp)) (Data.Bytes.natToBytesPadded (c4w2 M cw g x0).toNat 32) (64 + sp)) (Data.Bytes.natToBytesPadded (c4w3 M cw g x0).toNat 32) (96 + sp))) 269 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006, 7007, 7008, 7009, 7010, 7011, 7012, 7013, 7014, 7015, 7016, 7017, 7018, 7019, 7020, 7021, 7022, 7023, 7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038] with [c4g1, c4g2, c4g3, c4g4, c4w0, c4w1, c4w2, c4w3, word_mstore_disjoint]

theorem c4_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) (a b c d e : Nat) (g : UInt256) {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat} :
    Reach (callState s 15441 (wd a :: wd b :: g :: wd c :: wd b10 :: wd b9 :: wd b8 :: wd b7 :: wd b6 :: wd b5 :: wd b4 :: wd b3 :: wd b2 :: wd b1 :: wd b0 :: wd d :: wd e :: wd ret :: tail) M)
      (callState s ret tail M) 42 := by
  opt44_reach [7039, 7040, 7041, 7042, 7043, 7044, 7045, 7046, 7047, 7048, 7049, 7050, 7051, 7052, 7053, 7054, 7055, 7056] with [hj]

end MlDsaOpt44.Proofs.CS4
