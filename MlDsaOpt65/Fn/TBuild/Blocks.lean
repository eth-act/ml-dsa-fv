import MlDsaOpt44.Fn.Ct.TBuildMath
import MlDsaOpt65.Budget
import MlDsaOpt65.Layout
/- Ported from `MlDsaOpt44/Fn/Ct/TBuildBlocks.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `tbuild`: straight-line blocks, generalised to the table pointer `T` (port)

-- port: the 44 lemmas fix `TT = 20480`, `end = 22688` and the clamp offsets; here the table
pointer `T`, the end `E = T + 2208` and the calldata offset `off` are free (65/87 call
`tbuild` with `(0x5000, 32)` and `(0x6800, 0x520)`). The shapes `tgW … tbN`, `st3` are the
44 definitions (`MlDsaOpt44.Proofs.TB`).

Loop heads: `14905` (chunk loop, stack `pa, T, off, E, ret`) and `15296` (word loop,
stack `sh, V3, V2, V1, V0, pa, …`).
-/

namespace MlDsaOpt65.Proofs.TB

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.TB

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ

section
variable {s : State} {ret : Nat} {tail : List UInt256} {T E : Nat}

theorem tb_pro (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {off : Nat} :
    Reach (callState s 14892 (wd T :: wd off :: wd ret :: tail) M)
      (callState s 14905 (wd (T + 4064) :: wd T :: wd off :: wd (T + 2208) :: wd ret :: tail) M) 25 := by
  opt65_reach [6575, 6576, 6577, 6578, 6579, 6580, 6581, 6582, 6583] with [Nat.add_comm _ T]  -- port: symbolic `T`

theorem tb_l0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14905 (wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15086 (wd (leNat s.executionEnv.calldata off 32) ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 172 := by
  opt65_reach [6584, 6585, 6586, 6587, 6588, 6589, 6590, 6591, 6592, 6593, 6594, 6595, 6596, 6597, 6598, 6599, 6600, 6601, 6602, 6603, 6604, 6605, 6606, 6607, 6608, 6609, 6610, 6611, 6612, 6613, 6614, 6615, 6616, 6617, 6618, 6619, 6620, 6621, 6622, 6623, 6624, 6625, 6626, 6627, 6628, 6629, 6630, 6631, 6632, 6633, 6634, 6635, 6636, 6637, 6638, 6639, 6640, 6641] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15086 (wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15153 (wd (leNat s.executionEnv.calldata (320 + off) 32) :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  opt65_reach [6642, 6643, 6644, 6645, 6646, 6647, 6648, 6649, 6650, 6651, 6652, 6653, 6654, 6655, 6656, 6657, 6658, 6659, 6660, 6661, 6662, 6663, 6664, 6665, 6666, 6667, 6668, 6669, 6670, 6671, 6672, 6673, 6674, 6675, 6676, 6677, 6678, 6679, 6680, 6681, 6682, 6683, 6684, 6685, 6686, 6687, 6688, 6689, 6690, 6691, 6692, 6693, 6694, 6695, 6696] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15153 (wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15220 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  opt65_reach [6697, 6698, 6699, 6700, 6701, 6702, 6703, 6704, 6705, 6706, 6707, 6708, 6709, 6710, 6711, 6712, 6713, 6714, 6715, 6716, 6717, 6718, 6719, 6720, 6721, 6722, 6723, 6724, 6725, 6726, 6727, 6728, 6729, 6730, 6731, 6732, 6733, 6734, 6735, 6736, 6737, 6738, 6739, 6740, 6741, 6742, 6743, 6744, 6745, 6746, 6747, 6748, 6749, 6750, 6751] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15220 (wd V2 :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15296 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) :: wd V2 :: wd V1 :: wd V0 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 187 := by
  opt65_reach [6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773, 6774, 6775, 6776, 6777, 6778, 6779, 6780, 6781, 6782, 6783, 6784, 6785, 6786, 6787, 6788, 6789, 6790, 6791, 6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811, 6812, 6813, 6814, 6815] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_A (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {sh V0 V1 V2 V3 pa off : Nat}
    (hsh : sh ≤ 200) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 15296 (wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15554 (wd (tbW sh V0 V1 V2 V3) :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 214 := by
  opt65_reach [6816, 6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826, 6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842, 6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858, 6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869, 6870, 6871, 6872, 6873, 6874, 6875, 6876, 6877, 6878, 6879, 6880, 6881, 6882, 6883, 6884, 6885, 6886, 6887] with [tbW, tdsw, ts2, ts1, tgW]

theorem tb_B (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X sh V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hsh : sh + 40 < 240) (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 90656) :
    Reach (callState s 15554 (wd X :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15296 (wd (40 + sh) :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [6888, 6889, 6890, 6891, 6892, 6893, 6894, 6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905, 6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914] with [TB.st3, tbN]

theorem tb_Bx (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 90656) :
    Reach (callState s 15554 (wd X :: wd 200 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15622 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [6888, 6889, 6890, 6891, 6892, 6893, 6894, 6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905, 6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914] with [TB.st3, tbN]

theorem tb_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 pa off : Nat}
    (_hne : pa ≠ E - 192) (hle : E ≤ pa) (hpa : pa < 2 ^ 64) (_hoff : off < 2 ^ 64) (hE : 192 ≤ E) :
    Reach (callState s 15622 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14905 (wd pa :: wd T :: wd (30 + off) :: wd E :: wd ret :: tail) M) 90 := by
  opt65_reach [6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925, 6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933, 6934, 6935, 6936, 6937, 6944, 6945, 6946]

theorem tb_cl (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 off : Nat}
    (hE : 192 ≤ E) (hE2 : E < 2 ^ 64) (_hoff : off < 2 ^ 64) :
    Reach (callState s 15622 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 64) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14905 (wd E :: wd T :: wd (20 + off) :: wd E :: wd ret :: tail) M) 107 := by
  opt65_reach [6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925, 6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933, 6934, 6935, 6936, 6937, 6938, 6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946]
  exact ofNat_eq_ofNat_iff.mpr (by omega)  -- port: symbolic `off`

set_option maxRecDepth 100000 in
theorem tb_exit (hs : Ctx s) (htl : tail.length ≤ 960) (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) {V0 V1 V2 V3 off : Nat} (hE : 192 ≤ E) (hE2 : E < 2 ^ 64)
    (_hoff : off < 2 ^ 64) :
    Reach (callState s 15622 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 192) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s ret tail M) 58 := by
  opt65_reach [6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925, 6926, 6927, 6947, 6948, 6949, 6950, 6951, 6952] with [hj]

end

end MlDsaOpt65.Proofs.TB
