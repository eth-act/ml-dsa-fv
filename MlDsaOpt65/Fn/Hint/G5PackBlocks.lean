import MlDsaOpt65.Fn.Hint.G5Pure
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
set_option warningAsError true
/-!
# `pack` (ML-DSA-65): block lemmas and one loop iteration

`pack [nr, F, B, ret]` (`F = FIN + 256 + 2048 g`, `B = ACC + 0x2000 g`, `nr ∈ {2, 4}`): entry
`[nr, F, B, B + 0x2000]` (19 gas), 16 iterations `i` (`pk_A`: `x = OR_k word(B + 512 i + 32 k) << 4k`,
327 gas; `pk_B4` / `pk_B2`: lane `r < nr` of `x`, replicated, to `F + 32 i + 512 r`, 249 / 185 gas),
exit (16 gas): `19 + 16 · 576 + 16 = 9251`, `19 + 16 · 512 + 16 = 8227` (`Gas.pack nr`).
-/

namespace MlDsaOpt65.Proofs.G5PK

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs
open MlDsaOpt65.Proofs.Infra
open MlDsaOpt65.Proofs.G5H
open MlDsaOpt44.Proofs.PK (Xl)

/-- The stores of one iteration for `nr = 2`. -/
def wr2 (M : ByteArray) (x : UInt256) (fp : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (pw0 x).toNat 32) fp)
    (Data.Bytes.natToBytesPadded (pw1 x).toNat 32) (512 + fp)

/-- The stores of one iteration for `nr = 4`. -/
def wr4 (M : ByteArray) (x : UInt256) (fp : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (wr2 M x fp)
    (Data.Bytes.natToBytesPadded (pw2 x).toNat 32) (1024 + fp))
    (Data.Bytes.natToBytesPadded (pw3 x).toNat 32) (1536 + fp)

def wrN (nr : Nat) (M : ByteArray) (x : UInt256) (fp : Nat) : ByteArray :=
  if nr ≤ 2 then wr2 M x fp else wr4 M x fp

/-- Gas of one iteration. -/
def cI (nr : Nat) : Nat := if nr ≤ 2 then 512 else 576

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem pk_entry (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr F B : Nat) :
    Reach (callState s 16776 (wd nr :: wd F :: wd B :: wd ret :: tail) M)
      (callState s 16785 (wd nr :: wd F :: wd B :: wd (8192 + B) :: wd ret :: tail) M) 19 := by
  opt65_reach [7454, 7455, 7456, 7457, 7458, 7459, 7460]

theorem pk_A (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr wp fp e : Nat)
    (hwp : wp + 512 ≤ 90656) :
    Reach (callState s 16785 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16933 (pkA M wp :: wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M) 327 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [7461, 7462, 7463, 7464, 7465, 7466, 7467, 7468, 7469, 7470, 7471, 7472, 7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7482, 7483, 7484, 7485, 7486, 7487, 7488, 7489, 7490, 7491, 7492, 7493, 7494, 7495, 7496, 7497, 7498, 7499, 7500, 7501, 7502, 7503, 7504, 7505, 7506, 7507, 7508, 7509, 7510, 7511, 7512, 7513, 7514, 7515, 7516, 7517, 7518, 7519, 7520, 7521, 7522, 7523, 7524, 7525, 7526, 7527, 7528, 7529, 7530, 7531, 7532, 7533, 7534, 7535, 7536, 7537, 7538, 7539, 7540, 7541, 7542, 7543, 7544, 7545, 7546, 7547, 7548, 7549, 7550, 7551, 7552, 7553, 7554, 7555, 7556, 7557, 7558, 7559, 7560, 7561, 7562, 7563, 7564, 7565, 7566, 7567, 7568, 7569, 7570] with [pkA]

theorem pk_B4 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 16933 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16785 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7603, 7604, 7605, 7606, 7607, 7608, 7609, 7610, 7611, 7612, 7613, 7614, 7615, 7616, 7617, 7618, 7619, 7620, 7621, 7622, 7623, 7624, 7625, 7626, 7627, 7628, 7629, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B4x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 16933 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17154 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt65_reach [7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7603, 7604, 7605, 7606, 7607, 7608, 7609, 7610, 7611, 7612, 7613, 7614, 7615, 7616, 7617, 7618, 7619, 7620, 7621, 7622, 7623, 7624, 7625, 7626, 7627, 7628, 7629, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B2 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 16933 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16785 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7614, 7615, 7616, 7617, 7618, 7619, 7620, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644] with [wr2, pw0, pw1, REPc]

theorem pk_B2x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 16933 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17154 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt65_reach [7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7614, 7615, 7616, 7617, 7618, 7619, 7620, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644] with [wr2, pw0, pw1, REPc]

set_option maxRecDepth 100000 in
theorem pk_exit (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (nr a b e : Nat) :
    Reach (callState s 17154 (wd nr :: wd a :: wd b :: wd e :: wd ret :: tail) M)
      (callState s ret tail M) 16 := by
  opt65_reach [7645, 7646, 7647, 7648, 7649] with [hj]

/-- One iteration, loop continues. -/
theorem pk_iter (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 16785 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16785 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2 hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4 hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

/-- The last iteration. -/
theorem pk_iterx (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 16785 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17154 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

end

end MlDsaOpt65.Proofs.G5PK
