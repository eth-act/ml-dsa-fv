import MlDsa44.Proofs.Gas

/-! Prints `n<TAB>MlDsa44.Proofs.Gas.schedule n` for every calldata size `n`
given on the command line, evaluating the proved schedule itself.

    lake env lean --run scripts/xcheck_schedule.lean 0 3731 3732 ... -/

def main (args : List String) : IO Unit :=
  for a in args do
    let n := a.toNat!
    IO.println s!"{n}\t{MlDsa44.Proofs.Gas.schedule n}"
