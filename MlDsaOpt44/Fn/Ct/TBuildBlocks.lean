import MlDsaOpt44.Fn.Decode.Bswap
import MlDsaOpt44.Budget
set_option linter.unusedSimpArgs false
/-!
# `tbuild` (WP10): straight-line blocks

Loop heads: `13937` (chunk loop, stack `pa, TT, off, end, ret` with `TT = 20480`,
`end = TT + 2208 = 22688`) and `14328` (word loop, stack `sh, V3, V2, V1, V0, pa, …`).
The windows `V_r` enter as `leNat cd (off + 320 r) 32` (`bsw_word`); the word loop
body is cut after the cell/transpose network (`tbW`, kept abstract in the store block).
-/

namespace MlDsaOpt44.Proofs.TB

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ

/-! ## Shapes `opt44_block` leaves -/

/-- Gather: 40 bits of `V_r` from bit `sh` into lane `r`. -/
def tgW (sh V0 V1 V2 V3 : Nat) : Nat :=
  (1099511627775 &&& V3 / 2 ^ sh) * 6277101735386680763835789423207666416102355444464034512896 |||
    ((1099511627775 &&& V2 / 2 ^ sh) * 340282366920938463463374607431768211456 |||
      ((1099511627775 &&& V1 / 2 ^ sh) * 18446744073709551616 ||| 1099511627775 &&& V0 / 2 ^ sh))

/-- First spreading stage: 20-bit halves of each lane to 32-bit units. -/
def ts1 (x : Nat) : Nat :=
  6582011952183088782295924477334101861609978183833731334774194175 &&& x |||
    (6901739764772334502984731304745083193639544484091638668092185431244800 &&& x) * 4096

/-- Second spreading stage: 10-bit fields to 16-bit cells. -/
def ts2 (x : Nat) : Nat :=
  27580025446916579586740047030762717305835781530194468456916412547466239 &&& x |||
    (28241946057642577496821808159501022521175840286919135699882406448605428736 &&& x) * 64

/-- Delta swap of the bits selected by `m` with the bits `d` above them. -/
def tdsw (m d x : Nat) : Nat :=
  (m &&& (x ^^^ x % 2 ^ 256 / 2 ^ d)) * 2 ^ d ^^^ m &&& (x ^^^ x % 2 ^ 256 / 2 ^ d) ^^^ x

/-- The word stored at `pa`. -/
def tbW (sh V0 V1 V2 V3 : Nat) : Nat :=
  tdsw 6277005955876855982367846414099012818794836107166352343040 48
    (tdsw 340282366841710300967557013907638845440 96 (ts2 (ts1 (tgW sh V0 V1 V2 V3))))

/-- The word stored at `pa ± 2048`. -/
def tbN (X : Nat) : Nat :=
  (1807512127714571876376182462255096204072559614144354879260930929123294905343 ^^^ X) % 2 ^ 256

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem tb_pro (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 13924 (wd 20480 :: wd 32 :: wd ret :: tail) M)
      (callState s 13937 (wd 24544 :: wd 20480 :: wd 32 :: wd 22688 :: wd ret :: tail) M) 25 := by
  opt44_reach [6182, 6183, 6184, 6185, 6186, 6187, 6188, 6189, 6190]

theorem tb_l0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 13937 (wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14118 (wd (leNat s.executionEnv.calldata off 32) ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 172 := by
  opt44_reach [6191, 6192, 6193, 6194, 6195, 6196, 6197, 6198, 6199, 6200, 6201, 6202, 6203, 6204, 6205, 6206, 6207, 6208, 6209, 6210, 6211, 6212, 6213, 6214, 6215, 6216, 6217, 6218, 6219, 6220, 6221, 6222, 6223, 6224, 6225, 6226, 6227, 6228, 6229, 6230, 6231, 6232, 6233, 6234, 6235, 6236, 6237, 6238, 6239, 6240, 6241, 6242, 6243, 6244, 6245, 6246, 6247, 6248] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14118 (wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14185 (wd (leNat s.executionEnv.calldata (320 + off) 32) :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 165 := by
  opt44_reach [6249, 6250, 6251, 6252, 6253, 6254, 6255, 6256, 6257, 6258, 6259, 6260, 6261, 6262, 6263, 6264, 6265, 6266, 6267, 6268, 6269, 6270, 6271, 6272, 6273, 6274, 6275, 6276, 6277, 6278, 6279, 6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288, 6289, 6290, 6291, 6292, 6293, 6294, 6295, 6296, 6297, 6298, 6299, 6300, 6301, 6302, 6303] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14185 (wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14252 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 165 := by
  opt44_reach [6304, 6305, 6306, 6307, 6308, 6309, 6310, 6311, 6312, 6313, 6314, 6315, 6316, 6317, 6318, 6319, 6320, 6321, 6322, 6323, 6324, 6325, 6326, 6327, 6328, 6329, 6330, 6331, 6332, 6333, 6334, 6335, 6336, 6337, 6338, 6339, 6340, 6341, 6342, 6343, 6344, 6345, 6346, 6347, 6348, 6349, 6350, 6351, 6352, 6353, 6354, 6355, 6356, 6357, 6358] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 14252 (wd V2 :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14328 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) :: wd V2 :: wd V1 :: wd V0 ::
        wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 187 := by
  opt44_reach [6359, 6360, 6361, 6362, 6363, 6364, 6365, 6366, 6367, 6368, 6369, 6370, 6371, 6372, 6373, 6374, 6375, 6376, 6377, 6378, 6379, 6380, 6381, 6382, 6383, 6384, 6385, 6386, 6387, 6388, 6389, 6390, 6391, 6392, 6393, 6394, 6395, 6396, 6397, 6398, 6399, 6400, 6401, 6402, 6403, 6404, 6405, 6406, 6407, 6408, 6409, 6410, 6411, 6412, 6413, 6414, 6415, 6416, 6417, 6418, 6419, 6420, 6421, 6422] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_A (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {sh V0 V1 V2 V3 pa off : Nat}
    (hsh : sh ≤ 200) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 14328 (wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14586 (wd (tbW sh V0 V1 V2 V3) :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M) 214 := by
  opt44_reach [6423, 6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431, 6432, 6433, 6434, 6435, 6436, 6437, 6438, 6439, 6440, 6441, 6442, 6443, 6444, 6445, 6446, 6447, 6448, 6449, 6450, 6451, 6452, 6453, 6454, 6455, 6456, 6457, 6458, 6459, 6460, 6461, 6462, 6463, 6464, 6465, 6466, 6467, 6468, 6469, 6470, 6471, 6472, 6473, 6474, 6475, 6476, 6477, 6478, 6479, 6480, 6481, 6482, 6483, 6484, 6485, 6486, 6487, 6488, 6489, 6490, 6491, 6492, 6493, 6494] with [tbW, tdsw, ts2, ts1, tgW]

/-- Memory after the three stores of one word-loop visit. -/
def st3 (M : ByteArray) (pa X : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
    (Data.Bytes.natToBytesPadded X 32) pa) (Data.Bytes.natToBytesPadded (tbN X) 32) (2048 + pa))
    (Data.Bytes.natToBytesPadded (tbN X) 32) (pa - 2048)

theorem tb_B (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X sh V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hsh : sh + 40 < 240) (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 66080) :
    Reach (callState s 14586 (wd X :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14328 (wd (40 + sh) :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail)
        (st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6495, 6496, 6497, 6498, 6499, 6500, 6501, 6502, 6503, 6504, 6505, 6506, 6507, 6508, 6509, 6510, 6511, 6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519, 6520, 6521] with [st3, tbN]

theorem tb_Bx (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 66080) :
    Reach (callState s 14586 (wd X :: wd 200 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 14654 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail)
        (st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6495, 6496, 6497, 6498, 6499, 6500, 6501, 6502, 6503, 6504, 6505, 6506, 6507, 6508, 6509, 6510, 6511, 6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519, 6520, 6521] with [st3, tbN]

theorem tb_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 pa off : Nat}
    (_hne : pa ≠ 22496) (hle : 22688 ≤ pa) (hpa : pa < 2 ^ 64) (_hoff : off < 2 ^ 64) :
    Reach (callState s 14654 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
      (callState s 13937 (wd pa :: wd 20480 :: wd (30 + off) :: wd 22688 :: wd ret :: tail) M) 90 := by
  opt44_reach [6522, 6523, 6524, 6525, 6526, 6527, 6528, 6529, 6530, 6531, 6532, 6533, 6534, 6535, 6536, 6537, 6538, 6539, 6540, 6541, 6542, 6543, 6544, 6551, 6552, 6553]

theorem tb_cl (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 : Nat} :
    Reach (callState s 14654 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd 22624 :: wd 20480 :: wd 302 :: wd 22688 :: wd ret :: tail) M)
      (callState s 13937 (wd 22688 :: wd 20480 :: wd 322 :: wd 22688 :: wd ret :: tail) M) 107 := by
  have h : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129640258 =
      UInt256.ofNat 322 := ofNat_eq_ofNat_iff.mpr (by norm_num)
  opt44_reach [6522, 6523, 6524, 6525, 6526, 6527, 6528, 6529, 6530, 6531, 6532, 6533, 6534, 6535, 6536, 6537, 6538, 6539, 6540, 6541, 6542, 6543, 6544, 6545, 6546, 6547, 6548, 6549, 6550, 6551, 6552, 6553] with [h]

set_option maxRecDepth 100000 in
theorem tb_exit (hs : Ctx s) (htl : tail.length ≤ 960) (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) {V0 V1 V2 V3 : Nat} :
    Reach (callState s 14654 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd 22496 :: wd 20480 :: wd 322 :: wd 22688 :: wd ret :: tail) M)
      (callState s ret tail M) 58 := by
  opt44_reach [6522, 6523, 6524, 6525, 6526, 6527, 6528, 6529, 6530, 6531, 6532, 6533, 6534, 6554, 6555, 6556, 6557, 6558, 6559] with [hj]

end

end MlDsaOpt44.Proofs.TB
