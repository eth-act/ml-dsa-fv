import MlDsaOpt44.Main.Mu.Lemmas
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
/-! # Shared block vocabulary of the μ and final-hash segments -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The byte-swap masks and `REP` below the swapped word. -/
def muK (b : Bool) : List UInt256 :=
  [wd 6277101735386680764176071790128604879584176795969512275969, wd 18446744073709551615, wd 26959946660873538060741835960174461801791452538186943042387869433855, wd 1766820105243087041267848467410591083712559083657179364930612997358944255, wd 450552876409790643671482431940419874915447411150352389258589821042463539455, flag b]

/-- Close the facts of a block whose memory is a chain of `MSTORE`s. -/
macro "chain_facts" : tactic => `(tactic| (
  simp (disch := first | omega | exact word_lt _ _) only [word_mstore_disjoint, word_mstore]))

end MlDsaOpt44.Proofs
