import MlDsaOpt87.Fn.Group.Seed
import MlDsaOpt87.Fn.Group.Squeeze
set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-87): prologue up to the `ginit` call (WP G1)
-/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

theorem g1_b0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (ha : amask < 16) (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 15188 (gB amask col rb ret tail) M)
      (callState s 13376 (wd (gL4 amask col rb) :: wd 0 :: wd 15 :: wd 0 :: wd 15291 ::
        gB amask col rb ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have ha' : amask % 2 ^ 256 = amask := Nat.mod_eq_of_lt (by omega)
  have hc' : col % 2 ^ 256 = col := Nat.mod_eq_of_lt (by omega)
  have hr' : rb % 2 ^ 256 = rb := Nat.mod_eq_of_lt (by omega)
  opt87_reach [6813, 6814, 6815, 6816, 6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826,
    6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842,
    6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858,
    6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869] with [HAVE6]

end MlDsaOpt87.Proofs.GroupP
