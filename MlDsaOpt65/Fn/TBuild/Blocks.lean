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

Loop heads: `14534` (chunk loop, stack `pa, T, off, E, ret`) and `14925` (word loop,
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
    Reach (callState s 14521 (wd T :: wd off :: wd ret :: tail) M)
      (callState s 14534 (wd (T + 4064) :: wd T :: wd off :: wd (T + 2208) :: wd ret :: tail) M) 25 := by
  opt65_reach [6405, 6406, 6407, 6408, 6409, 6410, 6411, 6412, 6413]
  exact ⟨by rw [Nat.add_comm], by rw [Nat.add_comm]⟩  -- port: symbolic `T`

theorem tb_l0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14534 (wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14715 (wd (leNat s.executionEnv.calldata off 32) ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 172 := by
  opt65_reach [6414, 6415, 6416, 6417, 6418, 6419, 6420, 6421, 6422, 6423, 6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431, 6432, 6433, 6434, 6435, 6436, 6437, 6438, 6439, 6440, 6441, 6442, 6443, 6444, 6445, 6446, 6447, 6448, 6449, 6450, 6451, 6452, 6453, 6454, 6455, 6456, 6457, 6458, 6459, 6460, 6461, 6462, 6463, 6464, 6465, 6466, 6467, 6468, 6469, 6470, 6471] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14715 (wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14782 (wd (leNat s.executionEnv.calldata (320 + off) 32) :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  opt65_reach [6472, 6473, 6474, 6475, 6476, 6477, 6478, 6479, 6480, 6481, 6482, 6483, 6484, 6485, 6486, 6487, 6488, 6489, 6490, 6491, 6492, 6493, 6494, 6495, 6496, 6497, 6498, 6499, 6500, 6501, 6502, 6503, 6504, 6505, 6506, 6507, 6508, 6509, 6510, 6511, 6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519, 6520, 6521, 6522, 6523, 6524, 6525, 6526] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14782 (wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14849 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  opt65_reach [6527, 6528, 6529, 6530, 6531, 6532, 6533, 6534, 6535, 6536, 6537, 6538, 6539, 6540, 6541, 6542, 6543, 6544, 6545, 6546, 6547, 6548, 6549, 6550, 6551, 6552, 6553, 6554, 6555, 6556, 6557, 6558, 6559, 6560, 6561, 6562, 6563, 6564, 6565, 6566, 6567, 6568, 6569, 6570, 6571, 6572, 6573, 6574, 6575, 6576, 6577, 6578, 6579, 6580, 6581] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14849 (wd V2 :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14925 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) :: wd V2 :: wd V1 :: wd V0 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 187 := by
  opt65_reach [6582, 6583, 6584, 6585, 6586, 6587, 6588, 6589, 6590, 6591, 6592, 6593, 6594, 6595, 6596, 6597, 6598, 6599, 6600, 6601, 6602, 6603, 6604, 6605, 6606, 6607, 6608, 6609, 6610, 6611, 6612, 6613, 6614, 6615, 6616, 6617, 6618, 6619, 6620, 6621, 6622, 6623, 6624, 6625, 6626, 6627, 6628, 6629, 6630, 6631, 6632, 6633, 6634, 6635, 6636, 6637, 6638, 6639, 6640, 6641, 6642, 6643, 6644, 6645] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_A (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {sh V0 V1 V2 V3 pa off : Nat}
    (hsh : sh ≤ 200) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 14925 (wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15183 (wd (tbW sh V0 V1 V2 V3) :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 214 := by
  opt65_reach [6646, 6647, 6648, 6649, 6650, 6651, 6652, 6653, 6654, 6655, 6656, 6657, 6658, 6659, 6660, 6661, 6662, 6663, 6664, 6665, 6666, 6667, 6668, 6669, 6670, 6671, 6672, 6673, 6674, 6675, 6676, 6677, 6678, 6679, 6680, 6681, 6682, 6683, 6684, 6685, 6686, 6687, 6688, 6689, 6690, 6691, 6692, 6693, 6694, 6695, 6696, 6697, 6698, 6699, 6700, 6701, 6702, 6703, 6704, 6705, 6706, 6707, 6708, 6709, 6710, 6711, 6712, 6713, 6714, 6715, 6716, 6717] with [tbW, tdsw, ts2, ts1, tgW]

theorem tb_B (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X sh V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hsh : sh + 40 < 240) (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 90656) :
    Reach (callState s 15183 (wd X :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14925 (wd (40 + sh) :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [6718, 6719, 6720, 6721, 6722, 6723, 6724, 6725, 6726, 6727, 6728, 6729, 6730, 6731, 6732, 6733, 6734, 6735, 6736, 6737, 6738, 6739, 6740, 6741, 6742, 6743, 6744] with [TB.st3, tbN]

theorem tb_Bx (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 90656) :
    Reach (callState s 15183 (wd X :: wd 200 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15251 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [6718, 6719, 6720, 6721, 6722, 6723, 6724, 6725, 6726, 6727, 6728, 6729, 6730, 6731, 6732, 6733, 6734, 6735, 6736, 6737, 6738, 6739, 6740, 6741, 6742, 6743, 6744] with [TB.st3, tbN]

theorem tb_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 pa off : Nat}
    (_hne : pa ≠ E - 192) (hle : E ≤ pa) (hpa : pa < 2 ^ 64) (_hoff : off < 2 ^ 64) (hE : 192 ≤ E) :
    Reach (callState s 15251 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14534 (wd pa :: wd T :: wd (30 + off) :: wd E :: wd ret :: tail) M) 90 := by
  opt65_reach [6745, 6746, 6747, 6748, 6749, 6750, 6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766, 6767, 6774, 6775, 6776]

theorem tb_cl (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 off : Nat}
    (hE : 192 ≤ E) (hE2 : E < 2 ^ 64) (_hoff : off < 2 ^ 64) :
    Reach (callState s 15251 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 64) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 14534 (wd E :: wd T :: wd (20 + off) :: wd E :: wd ret :: tail) M) 107 := by
  opt65_reach [6745, 6746, 6747, 6748, 6749, 6750, 6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773, 6774, 6775, 6776]
  exact ofNat_eq_ofNat_iff.mpr (by omega)  -- port: symbolic `off`

set_option maxRecDepth 100000 in
theorem tb_exit (hs : Ctx s) (htl : tail.length ≤ 960) (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) {V0 V1 V2 V3 off : Nat} (hE : 192 ≤ E) (hE2 : E < 2 ^ 64)
    (_hoff : off < 2 ^ 64) :
    Reach (callState s 15251 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 192) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s ret tail M) 58 := by
  opt65_reach [6745, 6746, 6747, 6748, 6749, 6750, 6751, 6752, 6753, 6754, 6755, 6756, 6757, 6777, 6778, 6779, 6780, 6781, 6782] with [hj]

end

end MlDsaOpt65.Proofs.TB
