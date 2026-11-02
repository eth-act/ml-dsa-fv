module

public import Batteries.Tactic.Lint.Misc
public import Batteries.Tactic.Lint.Simp
public import EvmSemantics.EVM.Fork

/-!
`Operation` — the EVM instruction set, mirrored from `EvmYul.Operations`.

We use the same hierarchical grouping but drop the `OperationType` parameter
(`τ`) since we only handle `.EVM`. Group names are spelled out (`BlockOps`
rather than `BOp`) — only the standard mnemonic opcode names (`ADD`, `STOP`,
…) remain short.
-/

@[expose] public section

namespace EvmSemantics

namespace Operation

/-- Stop and arithmetic operations. -/
inductive StopArithOps where
  | STOP | ADD | MUL | SUB | DIV | SDIV | MOD | SMOD
  | ADDMOD | MULMOD | EXP | SIGNEXTEND
  deriving DecidableEq, Repr, Inhabited

/-- Comparison and bitwise-logic operations. -/
inductive CompareBitwiseOps where
  | LT | GT | SLT | SGT | EQ | ISZERO
  | AND | OR | XOR | NOT | BYTE | SHL | SHR | SAR
  | CLZ
  deriving DecidableEq, Repr, Inhabited

/-- Keccak hashing. -/
inductive KeccakOps where | KECCAK256
  deriving DecidableEq, Repr, Inhabited

/-- Environment information. -/
inductive EnvOps where
  | ADDRESS | BALANCE | ORIGIN | CALLER | CALLVALUE
  | CALLDATALOAD | CALLDATASIZE | CALLDATACOPY
  | CODESIZE | CODECOPY
  | GASPRICE | EXTCODESIZE | EXTCODECOPY
  | RETURNDATASIZE | RETURNDATACOPY
  | EXTCODEHASH
  deriving DecidableEq, Repr, Inhabited

/-- Block information. -/
inductive BlockOps where
  | BLOCKHASH | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO
  | GASLIMIT | CHAINID | SELFBALANCE | BASEFEE
  | BLOBHASH | BLOBBASEFEE
  deriving DecidableEq, Repr, Inhabited

/-- Stack, memory, storage, and control-flow. -/
inductive StackMemFlowOps where
  | POP
  | MLOAD | MSTORE | MSTORE8
  | SLOAD | SSTORE
  | JUMP | JUMPI | PC | JUMPDEST
  | MSIZE | GAS
  | TLOAD | TSTORE | MCOPY
  deriving DecidableEq, Repr, Inhabited

/-- PUSH0–PUSH32. The constructor index `width : Fin 33` is the # of bytes
    pushed (PUSH0 = 0 bytes, PUSH32 = 32 bytes). -/
structure PushOp where
  /-- Number of immediate bytes pushed (0 for `PUSH0`, …, 32 for `PUSH32`). -/
  width : Fin 33
  deriving DecidableEq, Repr, Inhabited

/-- DUP1–DUP16. The constructor index `idx : Fin 16` plus one is the
    stack position to copy (DUP1 copies stack[0], DUP16 copies stack[15]). -/
structure DupOp where
  /-- Zero-indexed stack position to duplicate (0 for `DUP1`, …, 15 for `DUP16`). -/
  idx : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- SWAP1–SWAP16. -/
structure SwapOp where
  /-- Zero-indexed depth of the element to swap with the top
      (0 for `SWAP1`, …, 15 for `SWAP16`). -/
  idx : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- EIP-8024 `decode_single` (execution-specs, Amsterdam): the stack item
    number `n` (1-based from the top) named by a DUPN / SWAPN immediate byte
    `x`, `(x + 145) mod 256`. For the valid immediates (`validSingle`) it
    ranges over `[17, 235]`. -/
def decodeSingle (x : Nat) : Nat := (x + 145) % 256

/-- EIP-8024: the DUPN / SWAPN immediates that decode. Bytes `91..127`
    halt exceptionally (they cover `0x5b` and the PUSH opcodes, so JUMPDEST
    analysis is unaffected). -/
def validSingle (x : Nat) : Bool := x ≤ 90 || 128 ≤ x

/-- EIP-8024 `decode_pair` (execution-specs, Amsterdam): the two stack item
    numbers `(n, m)` (1-based from the top, *below* the top item) named by
    an EXCHANGE immediate byte `x`. With `k = x xor 143`, `q = k / 16`,
    `r = k mod 16`: `(q + 1, r + 1)` if `q < r`, else `(r + 1, 29 - q)`.
    For every byte, `1 ≤ n` and `1 ≤ m ≤ 29`. -/
def decodePair (x : Nat) : Nat × Nat :=
  let k := x ^^^ 143
  let q := k / 16
  let r := k % 16
  if q < r then (q + 1, r + 1) else (r + 1, 29 - q)

/-- EIP-8024: the EXCHANGE immediates that decode. Bytes `82..127` halt
    exceptionally. -/
def validPair (x : Nat) : Bool := x ≤ 81 || 128 ≤ x

/-- DUPN (EIP-8024, opcode `0xe6`) — duplicates a stack item named by the
    immediate byte that follows the opcode in the code (read at decode
    time). The item is `decodeSingle imm` (1-based), i.e. the zero-indexed
    stack position `DupNOp.n`. An immediate outside `validSingle` makes the
    instruction invalid (`Operation.availableInFork`). -/
structure DupNOp where
  /-- Raw immediate byte (the encoded operand). -/
  imm : Fin 256
  deriving DecidableEq, Repr, Inhabited

/-- SWAPN (EIP-8024, opcode `0xe7`) — swaps the top with the stack item
    named by the immediate byte: item `decodeSingle imm + 1` (1-based), i.e.
    the zero-indexed position `SwapNOp.n + 1`. An immediate outside
    `validSingle` makes the instruction invalid
    (`Operation.availableInFork`). -/
structure SwapNOp where
  /-- Raw immediate byte (the encoded operand). -/
  imm : Fin 256
  deriving DecidableEq, Repr, Inhabited

/-- EXCHANGE (EIP-8024, opcode `0xe8`) — swaps two stack items below the
    top, named by the immediate byte through `decodePair`: zero-indexed
    positions `ExchangeOp.n + 1` and `ExchangeOp.m + 1`. An immediate
    outside `validPair` makes the instruction invalid
    (`Operation.availableInFork`). -/
structure ExchangeOp where
  /-- Packed immediate byte (the encoded operand pair). -/
  packed : Fin 256
  deriving DecidableEq, Repr, Inhabited

namespace DupNOp
/-- Zero-indexed stack position that DUPN duplicates:
    `decodeSingle imm - 1` (EELS: `stack[-decode_single(imm)]`). -/
def n (op : DupNOp) : Fin 256 :=
  ⟨decodeSingle op.imm.val - 1, by unfold decodeSingle; omega⟩
end DupNOp

namespace SwapNOp
/-- SWAPN swaps the top with zero-indexed position `n + 1`, where
    `n = decodeSingle imm - 1`. For a valid immediate `decodeSingle imm ≥ 17`,
    so `n + 1 = decodeSingle imm` (EELS: `stack[-(decode_single(imm) + 1)]`). -/
def n (op : SwapNOp) : Fin 256 :=
  ⟨decodeSingle op.imm.val - 1, by unfold decodeSingle; omega⟩
end SwapNOp

namespace ExchangeOp
/-- EXCHANGE's first operand minus one: it swaps zero-indexed positions
    `n + 1` and `m + 1`, and `n + 1 = (decodePair packed).1` (always `≥ 1`). -/
def n (op : ExchangeOp) : Nat := (decodePair op.packed.val).1 - 1
/-- EXCHANGE's second operand minus one: `m + 1 = (decodePair packed).2`
    (always `≥ 1`). -/
def m (op : ExchangeOp) : Nat := (decodePair op.packed.val).2 - 1
end ExchangeOp

/-- LOG0–LOG4. `topics : Fin 5` is the number of topics. -/
structure LogOp where
  /-- Number of indexed topics (0 for `LOG0`, …, 4 for `LOG4`). -/
  topics : Fin 5
  deriving DecidableEq, Repr, Inhabited

/-- System operations (calls, creates, halts, etc.). -/
inductive SystemOps where
  | CREATE | CALL | CALLCODE | RETURN | DELEGATECALL | CREATE2 | STATICCALL
  | REVERT | INVALID | SELFDESTRUCT
  deriving DecidableEq, Repr, Inhabited

end Operation

/-- The EVM instruction set as a tagged sum over per-category sub-inductives. -/
inductive Operation where
  | StopArith    : Operation.StopArithOps      → Operation
  | CompBit      : Operation.CompareBitwiseOps → Operation
  | Keccak       : Operation.KeccakOps         → Operation
  | Env          : Operation.EnvOps            → Operation
  | Block        : Operation.BlockOps          → Operation
  | StackMemFlow : Operation.StackMemFlowOps   → Operation
  | Push         : Operation.PushOp            → Operation
  | Dup          : Operation.DupOp             → Operation
  | Swap         : Operation.SwapOp            → Operation
  | DupN         : Operation.DupNOp            → Operation
  | SwapN        : Operation.SwapNOp           → Operation
  | Exchange     : Operation.ExchangeOp        → Operation
  | Log          : Operation.LogOp             → Operation
  | System       : Operation.SystemOps         → Operation
  deriving DecidableEq, Repr, Inhabited

namespace Operation

/-- Opcode `STOP`. -/
@[match_pattern] abbrev STOP       : Operation := .StopArith .STOP
/-- Opcode `ADD`. -/
@[match_pattern] abbrev ADD        : Operation := .StopArith .ADD
/-- Opcode `MUL`. -/
@[match_pattern] abbrev MUL        : Operation := .StopArith .MUL
/-- Opcode `SUB`. -/
@[match_pattern] abbrev SUB        : Operation := .StopArith .SUB
/-- Opcode `DIV`. -/
@[match_pattern] abbrev DIV        : Operation := .StopArith .DIV
/-- Opcode `SDIV`. -/
@[match_pattern] abbrev SDIV       : Operation := .StopArith .SDIV
/-- Opcode `MOD`. -/
@[match_pattern] abbrev MOD        : Operation := .StopArith .MOD
/-- Opcode `SMOD`. -/
@[match_pattern] abbrev SMOD       : Operation := .StopArith .SMOD
/-- Opcode `ADDMOD`. -/
@[match_pattern] abbrev ADDMOD     : Operation := .StopArith .ADDMOD
/-- Opcode `MULMOD`. -/
@[match_pattern] abbrev MULMOD     : Operation := .StopArith .MULMOD
/-- Opcode `EXP`. -/
@[match_pattern] abbrev EXP        : Operation := .StopArith .EXP
/-- Opcode `SIGNEXTEND`. -/
@[match_pattern] abbrev SIGNEXTEND : Operation := .StopArith .SIGNEXTEND

/-- Opcode `LT`. -/
@[match_pattern] abbrev LT     : Operation := .CompBit .LT
/-- Opcode `GT`. -/
@[match_pattern] abbrev GT     : Operation := .CompBit .GT
/-- Opcode `SLT`. -/
@[match_pattern] abbrev SLT    : Operation := .CompBit .SLT
/-- Opcode `SGT`. -/
@[match_pattern] abbrev SGT    : Operation := .CompBit .SGT
/-- Opcode `EQ`. -/
@[match_pattern] abbrev EQ     : Operation := .CompBit .EQ
/-- Opcode `ISZERO`. -/
@[match_pattern] abbrev ISZERO : Operation := .CompBit .ISZERO
/-- Opcode `AND`. -/
@[match_pattern] abbrev AND    : Operation := .CompBit .AND
/-- Opcode `OR`. -/
@[match_pattern] abbrev OR     : Operation := .CompBit .OR
/-- Opcode `XOR`. -/
@[match_pattern] abbrev XOR    : Operation := .CompBit .XOR
/-- Opcode `NOT`. -/
@[match_pattern] abbrev NOT    : Operation := .CompBit .NOT
/-- Opcode `CLZ` (EIP-7939, Osaka). -/
@[match_pattern] abbrev CLZ    : Operation := .CompBit .CLZ
/-- Opcode `BYTE`. -/
@[match_pattern] abbrev BYTE   : Operation := .CompBit .BYTE
/-- Opcode `SHL`. -/
@[match_pattern] abbrev SHL    : Operation := .CompBit .SHL
/-- Opcode `SHR`. -/
@[match_pattern] abbrev SHR    : Operation := .CompBit .SHR
/-- Opcode `SAR`. -/
@[match_pattern] abbrev SAR    : Operation := .CompBit .SAR

/-- Opcode `KECCAK256`. -/
@[match_pattern] abbrev KECCAK256 : Operation := .Keccak .KECCAK256

/-- Opcode `ADDRESS`. -/
@[match_pattern] abbrev ADDRESS        : Operation := .Env .ADDRESS
/-- Opcode `BALANCE`. -/
@[match_pattern] abbrev BALANCE        : Operation := .Env .BALANCE
/-- Opcode `ORIGIN`. -/
@[match_pattern] abbrev ORIGIN         : Operation := .Env .ORIGIN
/-- Opcode `CALLER`. -/
@[match_pattern] abbrev CALLER         : Operation := .Env .CALLER
/-- Opcode `CALLVALUE`. -/
@[match_pattern] abbrev CALLVALUE      : Operation := .Env .CALLVALUE
/-- Opcode `CALLDATALOAD`. -/
@[match_pattern] abbrev CALLDATALOAD   : Operation := .Env .CALLDATALOAD
/-- Opcode `CALLDATASIZE`. -/
@[match_pattern] abbrev CALLDATASIZE   : Operation := .Env .CALLDATASIZE
/-- Opcode `CALLDATACOPY`. -/
@[match_pattern] abbrev CALLDATACOPY   : Operation := .Env .CALLDATACOPY
/-- Opcode `CODESIZE`. -/
@[match_pattern] abbrev CODESIZE       : Operation := .Env .CODESIZE
/-- Opcode `CODECOPY`. -/
@[match_pattern] abbrev CODECOPY       : Operation := .Env .CODECOPY
/-- Opcode `GASPRICE`. -/
@[match_pattern] abbrev GASPRICE       : Operation := .Env .GASPRICE
/-- Opcode `EXTCODESIZE`. -/
@[match_pattern] abbrev EXTCODESIZE    : Operation := .Env .EXTCODESIZE
/-- Opcode `EXTCODECOPY`. -/
@[match_pattern] abbrev EXTCODECOPY    : Operation := .Env .EXTCODECOPY
/-- Opcode `RETURNDATASIZE`. -/
@[match_pattern] abbrev RETURNDATASIZE : Operation := .Env .RETURNDATASIZE
/-- Opcode `RETURNDATACOPY`. -/
@[match_pattern] abbrev RETURNDATACOPY : Operation := .Env .RETURNDATACOPY
/-- Opcode `EXTCODEHASH`. -/
@[match_pattern] abbrev EXTCODEHASH    : Operation := .Env .EXTCODEHASH

/-- Opcode `BLOCKHASH`. -/
@[match_pattern] abbrev BLOCKHASH   : Operation := .Block .BLOCKHASH
/-- Opcode `COINBASE`. -/
@[match_pattern] abbrev COINBASE    : Operation := .Block .COINBASE
/-- Opcode `TIMESTAMP`. -/
@[match_pattern] abbrev TIMESTAMP   : Operation := .Block .TIMESTAMP
/-- Opcode `NUMBER`. -/
@[match_pattern] abbrev NUMBER      : Operation := .Block .NUMBER
/-- Opcode `PREVRANDAO`. -/
@[match_pattern] abbrev PREVRANDAO  : Operation := .Block .PREVRANDAO
/-- Opcode `GASLIMIT`. -/
@[match_pattern] abbrev GASLIMIT    : Operation := .Block .GASLIMIT
/-- Opcode `CHAINID`. -/
@[match_pattern] abbrev CHAINID     : Operation := .Block .CHAINID
/-- Opcode `SELFBALANCE`. -/
@[match_pattern] abbrev SELFBALANCE : Operation := .Block .SELFBALANCE
/-- Opcode `BASEFEE`. -/
@[match_pattern] abbrev BASEFEE     : Operation := .Block .BASEFEE
/-- Opcode `BLOBHASH`. -/
@[match_pattern] abbrev BLOBHASH    : Operation := .Block .BLOBHASH
/-- Opcode `BLOBBASEFEE`. -/
@[match_pattern] abbrev BLOBBASEFEE : Operation := .Block .BLOBBASEFEE

/-- Opcode `POP`. -/
@[match_pattern] abbrev POP      : Operation := .StackMemFlow .POP
/-- Opcode `MLOAD`. -/
@[match_pattern] abbrev MLOAD    : Operation := .StackMemFlow .MLOAD
/-- Opcode `MSTORE`. -/
@[match_pattern] abbrev MSTORE   : Operation := .StackMemFlow .MSTORE
/-- Opcode `MSTORE8`. -/
@[match_pattern] abbrev MSTORE8  : Operation := .StackMemFlow .MSTORE8
/-- Opcode `SLOAD`. -/
@[match_pattern] abbrev SLOAD    : Operation := .StackMemFlow .SLOAD
/-- Opcode `SSTORE`. -/
@[match_pattern] abbrev SSTORE   : Operation := .StackMemFlow .SSTORE
/-- Opcode `JUMP`. -/
@[match_pattern] abbrev JUMP     : Operation := .StackMemFlow .JUMP
/-- Opcode `JUMPI`. -/
@[match_pattern] abbrev JUMPI    : Operation := .StackMemFlow .JUMPI
/-- Opcode `PC`. -/
@[match_pattern] abbrev PC       : Operation := .StackMemFlow .PC
/-- Opcode `JUMPDEST`. -/
@[match_pattern] abbrev JUMPDEST : Operation := .StackMemFlow .JUMPDEST
/-- Opcode `MSIZE`. -/
@[match_pattern] abbrev MSIZE    : Operation := .StackMemFlow .MSIZE
/-- Opcode `GAS`. -/
@[match_pattern] abbrev GAS      : Operation := .StackMemFlow .GAS
/-- Opcode `TLOAD`. -/
@[match_pattern] abbrev TLOAD    : Operation := .StackMemFlow .TLOAD
/-- Opcode `TSTORE`. -/
@[match_pattern] abbrev TSTORE   : Operation := .StackMemFlow .TSTORE
/-- Opcode `MCOPY`. -/
@[match_pattern] abbrev MCOPY    : Operation := .StackMemFlow .MCOPY

/-- EIP-8024 `DUPN` with raw immediate byte `n`. -/
@[match_pattern] abbrev DUPN (n : Fin 256) : Operation := .DupN ⟨n⟩
/-- EIP-8024 `SWAPN` with raw immediate byte `n`. -/
@[match_pattern] abbrev SWAPN (n : Fin 256) : Operation := .SwapN ⟨n⟩
/-- EIP-8024 `EXCHANGE` with raw (pair-encoded) immediate byte `b`. -/
@[match_pattern] abbrev EXCHANGE (b : Fin 256) : Operation := .Exchange ⟨b⟩

/-- Opcode `CREATE`. -/
@[match_pattern] abbrev CREATE       : Operation := .System .CREATE
/-- Opcode `CALL`. -/
@[match_pattern] abbrev CALL         : Operation := .System .CALL
/-- Opcode `CALLCODE`. -/
@[match_pattern] abbrev CALLCODE     : Operation := .System .CALLCODE
/-- Opcode `RETURN`. -/
@[match_pattern] abbrev RETURN       : Operation := .System .RETURN
/-- Opcode `DELEGATECALL`. -/
@[match_pattern] abbrev DELEGATECALL : Operation := .System .DELEGATECALL
/-- Opcode `CREATE2`. -/
@[match_pattern] abbrev CREATE2      : Operation := .System .CREATE2
/-- Opcode `STATICCALL`. -/
@[match_pattern] abbrev STATICCALL   : Operation := .System .STATICCALL
/-- Opcode `REVERT`. -/
@[match_pattern] abbrev REVERT       : Operation := .System .REVERT
/-- Opcode `INVALID`. -/
@[match_pattern] abbrev INVALID      : Operation := .System .INVALID
/-- Opcode `SELFDESTRUCT`. -/
@[match_pattern] abbrev SELFDESTRUCT : Operation := .System .SELFDESTRUCT

end Operation

/-- Is `op` part of the instruction set activated at fork `f`? The
    activation table follows the Yellow Paper:

    * Frontier: everything except the opcodes listed below.
    * Homestead (EIP-2): `DELEGATECALL`.
    * Byzantium (EIP-140 / -211 / -214): `REVERT`, `RETURNDATASIZE`,
      `RETURNDATACOPY`, `STATICCALL`.
    * Constantinople (EIP-145 / -1014 / -1052): `SHL`, `SHR`, `SAR`,
      `CREATE2`, `EXTCODEHASH`.
    * Istanbul (EIP-1344 / -1884): `CHAINID`, `SELFBALANCE`.
    * London (EIP-3198): `BASEFEE`.
    * Shanghai (EIP-3855): `PUSH0`.
    * Cancun (EIP-1153 / -4844 / -5656 / -7516): `TLOAD`, `TSTORE`,
      `MCOPY`, `BLOBHASH`, `BLOBBASEFEE`.

    * Amsterdam (EIP-8024): `DUPN`, `SWAPN`, `EXCHANGE` (bytes
      `0xe6..0xe8`), each only with an immediate that decodes
      (`validSingle` / `validPair`). Before Amsterdam they are unavailable
      with every immediate, so bytes `0xe6..0xe8` raise
      `InvalidInstruction` on Frontier through Osaka.

    EIP-8024's exceptional halt on a forbidden immediate (EELS raises
    `InvalidParameter` after charging the base gas) is modelled here, as
    an unavailable instruction: `State.decoded` is `none` and the step
    halts with `InvalidInstruction`. Both are exceptional halts that
    consume all remaining gas, so only the exception's name differs.

    Decoders gate on this to reject opcodes that haven't been activated
    yet — an unactivated byte must trigger `InvalidInstruction` per the
    YP, *not* execute as the future opcode. -/
def Operation.availableInFork : Operation → Fork → Bool
  | .CompBit .SHL,            f => f ≥ .Constantinople
  | .CompBit .SHR,            f => f ≥ .Constantinople
  | .CompBit .SAR,            f => f ≥ .Constantinople
  | .CompBit .CLZ,            f => f ≥ .Osaka
  | .Env .RETURNDATASIZE,     f => f ≥ .Byzantium
  | .Env .RETURNDATACOPY,     f => f ≥ .Byzantium
  | .Env .EXTCODEHASH,        f => f ≥ .Constantinople
  | .Block .CHAINID,          f => f ≥ .Istanbul
  | .Block .SELFBALANCE,      f => f ≥ .Istanbul
  | .Block .BASEFEE,          f => f ≥ .London
  | .Block .BLOBHASH,         f => f ≥ .Cancun
  | .Block .BLOBBASEFEE,      f => f ≥ .Cancun
  | .StackMemFlow .TLOAD,     f => f ≥ .Cancun
  | .StackMemFlow .TSTORE,    f => f ≥ .Cancun
  | .StackMemFlow .MCOPY,     f => f ≥ .Cancun
  | .System .DELEGATECALL,    f => f ≥ .Homestead
  | .System .REVERT,          f => f ≥ .Byzantium
  | .System .STATICCALL,      f => f ≥ .Byzantium
  | .System .CREATE2,         f => f ≥ .Constantinople
  | .Push p,                  f => if p.width.val = 0 then f ≥ .Shanghai else true
  -- EIP-8024 (`DUPN` / `SWAPN` / `EXCHANGE`): Amsterdam, and only with a
  -- valid immediate; anything else halts with `InvalidInstruction`.
  | .DupN d,                  f => f ≥ .Amsterdam && validSingle d.imm.val
  | .SwapN d,                 f => f ≥ .Amsterdam && validSingle d.imm.val
  | .Exchange e,              f => f ≥ .Amsterdam && validPair e.packed.val
  | _,                        _ => true

/-- # of immediate-argument bytes following the opcode in the bytecode.
    Non-zero for PUSH1..PUSH32 and the EIP-8024 ops DUPN/SWAPN/EXCHANGE. -/
def Operation.argBytes : Operation → Nat
  | .Push p  => p.width.val
  | .DupN _  => 1
  | .SwapN _ => 1
  | .Exchange _ => 1
  | _        => 0

/-- The Yellow Paper `δ` — stack-pop arity. -/
def Operation.popArity : Operation → Nat
  | .StopArith op =>
    match op with
    | .STOP => 0 | .ADD | .MUL | .SUB | .DIV | .SDIV | .MOD | .SMOD | .EXP | .SIGNEXTEND => 2
    | .ADDMOD | .MULMOD => 3
  | .CompBit op =>
    match op with
    | .ISZERO | .NOT | .CLZ => 1
    | _ => 2
  | .Keccak _ => 2
  | .Env op =>
    match op with
    | .ADDRESS | .ORIGIN | .CALLER | .CALLVALUE | .CALLDATASIZE | .CODESIZE
    | .GASPRICE | .RETURNDATASIZE => 0
    | .BALANCE | .CALLDATALOAD | .EXTCODESIZE | .EXTCODEHASH => 1
    | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY => 3
    | .EXTCODECOPY => 4
  | .Block op =>
    match op with
    | .BLOCKHASH | .BLOBHASH => 1
    | _ => 0
  | .StackMemFlow op =>
    match op with
    | .POP | .MLOAD | .SLOAD | .JUMP | .TLOAD => 1
    | .MSTORE | .MSTORE8 | .SSTORE | .JUMPI | .TSTORE => 2
    | .PC | .JUMPDEST | .MSIZE | .GAS => 0
    | .MCOPY => 3
  | .Push _ => 0
  | .Dup d => d.idx.val + 1
  | .Swap e => e.idx.val + 2
  | .DupN d => d.n.val + 1
  | .SwapN s => s.n.val + 2
  | .Exchange e => Nat.max (e.n + 1) (e.m + 1) + 1
  | .Log l => l.topics.val + 2
  | .System op =>
    match op with
    | .CREATE => 3 | .CREATE2 => 4
    | .CALL | .CALLCODE => 7
    | .DELEGATECALL | .STATICCALL => 6
    | .RETURN | .REVERT => 2
    | .SELFDESTRUCT => 1
    | .INVALID => 0

/-- Operations whose execution mutates persistent or transient state and
    must therefore be rejected when `executionEnv.permitStateMutation = false` (static
    mode). Mirrors the reference's `W` predicate. -/
def Operation.isStateMutating : Operation → Bool
  | .SSTORE     => true
  | .TSTORE     => true
  | .Log _      => true
  -- Not yet implemented but listed for forward compatibility:
  | .CREATE     => true
  | .CREATE2    => true
  | .SELFDESTRUCT => true
  | _           => false

/-- The Yellow Paper `α` — # of items pushed back. -/
def Operation.pushArity : Operation → Nat
  | .StopArith op => match op with | .STOP => 0 | _ => 1
  | .CompBit _ => 1
  | .Keccak _ => 1
  | .Env op =>
    match op with
    | .CALLDATACOPY | .CODECOPY | .EXTCODECOPY | .RETURNDATACOPY => 0
    | _ => 1
  | .Block _ => 1
  | .StackMemFlow op =>
    match op with
    | .POP | .MSTORE | .MSTORE8 | .SSTORE | .JUMP | .JUMPI | .JUMPDEST
    | .TSTORE | .MCOPY => 0
    | .MLOAD | .SLOAD | .PC | .MSIZE | .GAS | .TLOAD => 1
  | .Push _ => 1
  | .Dup d => d.idx.val + 2
  | .Swap e => e.idx.val + 2
  | .DupN d => d.n.val + 2
  | .SwapN s => s.n.val + 2
  | .Exchange e => Nat.max (e.n + 1) (e.m + 1) + 1
  | .Log _ => 0
  | .System op =>
    match op with
    | .CREATE | .CREATE2 | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL => 1
    | .RETURN | .REVERT | .INVALID | .SELFDESTRUCT => 0

-- The auto-derived `Repr` instances for the seven single-`Fin` op structs
-- all have an unused `prec : ℕ` argument inherited from `Repr.reprPrec`.
-- That's intrinsic to the `Repr` typeclass shape; we explicitly silence the
-- `unusedArguments` linter on each.
attribute [nolint unusedArguments]
  Operation.instReprPushOp.repr
  Operation.instReprDupOp.repr
  Operation.instReprSwapOp.repr
  Operation.instReprDupNOp.repr
  Operation.instReprSwapNOp.repr
  Operation.instReprExchangeOp.repr
  Operation.instReprLogOp.repr

-- `KeccakOps` has a single constructor (`KECCAK256`), so its auto-derived
-- `injEq` lemma is `KECCAK256 = KECCAK256 ↔ True`, which `simp` can already
-- prove. The lemma is harmless — silence `simpNF`.
attribute [nolint simpNF] Operation.Keccak.injEq

end EvmSemantics
