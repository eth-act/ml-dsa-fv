import EvmProof.Amsterdam
import EvmSemantics.EVM.StepF
/-! EIP-8024 test cases on the patched semantics
(`lake env lean EvmProof/checks/Eip8024.lean`).

The cases are those of eips.ethereum.org/EIPS/eip-8024 (the same list
`scripts/opt_selftest_glam.py` runs on `opt_evm.py`), executed with `stepF` on
an `Amsterdam` frame; the last ones check that 0xe6..0xe8 stay invalid on
Osaka. A stack is listed top first. -/

open EvmSemantics EvmSemantics.EVM

namespace EvmProof.Eip8024Check

def hexByte (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def ofHex (s : String) : ByteArray :=
  let cs := s.toList
  ByteArray.mk ((List.range (cs.length / 2)).map fun i =>
    UInt8.ofNat (16 * hexByte cs[2 * i]! + hexByte cs[2 * i + 1]!)).toArray

def frame (fork : Fork) (code : ByteArray) : State :=
  let addr := AccountAddress.ofNat 0x8212
  let env : ExecutionEnv :=
    { (default : ExecutionEnv) with
      address := addr, codeAddr := addr, code, fork, permitStateMutation := true }
  { (default : State) with
    gasAvailable := 1000000
    accountMap := AccountMap.empty.set addr { Account.empty with code }
    executionEnv := env }

def run : Nat → State → State
  | 0, s => s
  | n + 1, s => if s.isDone then s else run n (stepF s)

/-- `(halted normally, stack as naturals, gas used)`. -/
def exec (fork : Fork) (hex : String) : Bool × List Nat × Nat :=
  let s := run 3000 (frame fork (ofHex hex))
  (match s.halt with | .Success => true | _ => false,
    s.stack.map UInt256.toNat, 1000000 - s.gasAvailable)

def ok (hex : String) : Bool := (exec .Amsterdam hex).1
def stk (hex : String) : List Nat := (exec .Amsterdam hex).2.1

-- DUPN 0x80 = decode_single 17: duplicate the 17th item (the 1 at the bottom)
#guard ok "60016000808080808080808080808080808080e680"
#guard stk "60016000808080808080808080808080808080e680" = [1] ++ List.replicate 16 0 ++ [1]
-- SWAPN 0x80: swap the top (2) with the 18th item (1)
#guard stk "600160008080808080808080808080808080806002e780" =
  [1] ++ List.replicate 16 0 ++ [2]
-- EXCHANGE 0x8e: (n, m) = (1, 2)
#guard stk "600060016002e88e" = [2, 0, 1]
-- EXCHANGE 0x8f: (n, m) = (1, 29)
#guard stk "600080808080808080808080808080808080808080808080808080808060016002e88f" =
  [2] ++ List.replicate 28 0 ++ [1]
-- EXCHANGE 0x8e, then ISZERO: pc advances past the immediate
#guard stk "60008080e88e15" = [1, 0, 0]
-- SWAPN 0x5b: forbidden immediate halts exceptionally
#guard !(ok "e75b")
-- JUMP to the 0x5b immediate of a DUPN: it is a JUMPDEST
#guard ok "600456e65b"
-- EXCHANGE 0x52: forbidden immediate
#guard !(ok "e852")
-- DUPN 0x80 with only 16 items: underflow
#guard !(ok "6000808080808080808080808080808080e680")
-- 3 gas, like DUP1: 2 PUSH1 + 15 DUP1 + DUPN = 18 instructions of 3 gas
#guard (exec .Amsterdam "60016000808080808080808080808080808080e680").2.2 = 18 * 3
-- boundaries
def rep (n : Nat) (h : String) : String := String.join (List.replicate n h)
-- DUPN with 1024 items: overflow; with 1023 it pushes the 1024th
#guard !(ok (rep 1024 "5f" ++ "e680"))
#guard ok (rep 1023 "5f" ++ "e680")
-- SWAPN 0x80 (item 18) with exactly 18 items succeeds, with 17 it underflows
#guard ok (rep 18 "5f" ++ "e780")
#guard !(ok (rep 17 "5f" ++ "e780"))
-- EXCHANGE 0x8f = (1, 29) needs 30 items
#guard ok (rep 30 "5f" ++ "e88f")
#guard !(ok (rep 29 "5f" ++ "e88f"))
-- DUPN 0x5a is item 235 (valid with 235 items); 0x5b is forbidden
#guard ok (rep 235 "5f" ++ "e65a")
#guard !(ok (rep 234 "5f" ++ "e65a"))
#guard !(ok (rep 235 "5f" ++ "e65b"))
-- DUPN as the last byte of the code: the missing immediate reads as 0, item 145
#guard ok (rep 145 "5f" ++ "e6")
#guard !(ok (rep 144 "5f" ++ "e6"))
-- not defined before Amsterdam, whatever the immediate
#guard !((exec .Osaka "e680").1)
#guard !((exec .Osaka "60016002e780").1)
#guard !((exec .Osaka "600060016002e88e").1)

end EvmProof.Eip8024Check
