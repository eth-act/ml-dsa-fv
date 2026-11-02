import MlDsaOpt65.Fn.Group.Seed
import MlDsaOpt65.Fn.Group.Squeeze
set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-65): prologue up to the `ginit` call (WP G1)
-/

namespace MlDsaOpt65.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

theorem g1_b0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (ha : amask < 16) (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 14460 (gB amask col rb ret tail) M)
      (callState s 11987 (wd (gL4 amask col rb) :: wd 0 :: wd 15 :: wd 0 :: wd 14563 ::
        gB amask col rb ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have ha' : amask % 2 ^ 256 = amask := Nat.mod_eq_of_lt (by omega)
  have hc' : col % 2 ^ 256 = col := Nat.mod_eq_of_lt (by omega)
  have hr' : rb % 2 ^ 256 = rb := Nat.mod_eq_of_lt (by omega)
  opt65_reach [6515, 6516, 6517, 6518, 6519, 6520, 6521, 6522, 6523, 6524, 6525, 6526, 6527, 6528,
    6529, 6530, 6531, 6532, 6533, 6534, 6535, 6536, 6537, 6538, 6539, 6540, 6541, 6542, 6543, 6544,
    6545, 6546, 6547, 6548, 6549, 6550, 6551, 6552, 6553, 6554, 6555, 6556, 6557, 6558, 6559, 6560,
    6561, 6562, 6563, 6564, 6565, 6566, 6567, 6568, 6569, 6570, 6571] with [HAVE6]

end MlDsaOpt65.Proofs.GroupP
