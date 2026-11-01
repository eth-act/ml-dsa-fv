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
    Reach (callState s 16473 (wd nr :: wd F :: wd B :: wd ret :: tail) M)
      (callState s 16482 (wd nr :: wd F :: wd B :: wd (8192 + B) :: wd ret :: tail) M) 19 := by
  opt65_reach [7295, 7296, 7297, 7298, 7299, 7300, 7301]

theorem pk_A (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr wp fp e : Nat)
    (hwp : wp + 512 ≤ 90656) :
    Reach (callState s 16482 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16630 (pkA M wp :: wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M) 327 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [7302, 7303, 7304, 7305, 7306, 7307, 7308, 7309, 7310, 7311, 7312, 7313, 7314, 7315, 7316, 7317, 7318, 7319, 7320, 7321, 7322, 7323, 7324, 7325, 7326, 7327, 7328, 7329, 7330, 7331, 7332, 7333, 7334, 7335, 7336, 7337, 7338, 7339, 7340, 7341, 7342, 7343, 7344, 7345, 7346, 7347, 7348, 7349, 7350, 7351, 7352, 7353, 7354, 7355, 7356, 7357, 7358, 7359, 7360, 7361, 7362, 7363, 7364, 7365, 7366, 7367, 7368, 7369, 7370, 7371, 7372, 7373, 7374, 7375, 7376, 7377, 7378, 7379, 7380, 7381, 7382, 7383, 7384, 7385, 7386, 7387, 7388, 7389, 7390, 7391, 7392, 7393, 7394, 7395, 7396, 7397, 7398, 7399, 7400, 7401, 7402, 7403, 7404, 7405, 7406, 7407, 7408, 7409, 7410, 7411] with [pkA]

theorem pk_B4 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 16630 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16482 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [7412, 7413, 7414, 7415, 7416, 7417, 7418, 7419, 7420, 7421, 7422, 7423, 7424, 7425, 7426, 7427, 7428, 7429, 7430, 7431, 7432, 7433, 7434, 7435, 7436, 7437, 7438, 7439, 7440, 7441, 7442, 7443, 7444, 7445, 7446, 7447, 7448, 7449, 7450, 7451, 7452, 7453, 7454, 7455, 7456, 7457, 7458, 7459, 7460, 7461, 7462, 7463, 7464, 7465, 7466, 7467, 7468, 7469, 7470, 7471, 7472, 7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7482, 7483, 7484, 7485] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B4x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 16630 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16851 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt65_reach [7412, 7413, 7414, 7415, 7416, 7417, 7418, 7419, 7420, 7421, 7422, 7423, 7424, 7425, 7426, 7427, 7428, 7429, 7430, 7431, 7432, 7433, 7434, 7435, 7436, 7437, 7438, 7439, 7440, 7441, 7442, 7443, 7444, 7445, 7446, 7447, 7448, 7449, 7450, 7451, 7452, 7453, 7454, 7455, 7456, 7457, 7458, 7459, 7460, 7461, 7462, 7463, 7464, 7465, 7466, 7467, 7468, 7469, 7470, 7471, 7472, 7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7482, 7483, 7484, 7485] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B2 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 16630 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16482 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt65_reach [7412, 7413, 7414, 7415, 7416, 7417, 7418, 7419, 7420, 7421, 7422, 7423, 7424, 7425, 7426, 7427, 7428, 7429, 7430, 7431, 7432, 7433, 7434, 7435, 7436, 7437, 7438, 7439, 7440, 7441, 7442, 7443, 7455, 7456, 7457, 7458, 7459, 7460, 7461, 7471, 7472, 7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7482, 7483, 7484, 7485] with [wr2, pw0, pw1, REPc]

theorem pk_B2x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 16630 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16851 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt65_reach [7412, 7413, 7414, 7415, 7416, 7417, 7418, 7419, 7420, 7421, 7422, 7423, 7424, 7425, 7426, 7427, 7428, 7429, 7430, 7431, 7432, 7433, 7434, 7435, 7436, 7437, 7438, 7439, 7440, 7441, 7442, 7443, 7455, 7456, 7457, 7458, 7459, 7460, 7461, 7471, 7472, 7473, 7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481, 7482, 7483, 7484, 7485] with [wr2, pw0, pw1, REPc]

set_option maxRecDepth 100000 in
theorem pk_exit (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (nr a b e : Nat) :
    Reach (callState s 16851 (wd nr :: wd a :: wd b :: wd e :: wd ret :: tail) M)
      (callState s ret tail M) 16 := by
  opt65_reach [7486, 7487, 7488, 7489, 7490] with [hj]

/-- One iteration, loop continues. -/
theorem pk_iter (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 16482 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16482 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
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
    Reach (callState s 16482 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 16851 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

end

end MlDsaOpt65.Proofs.G5PK
