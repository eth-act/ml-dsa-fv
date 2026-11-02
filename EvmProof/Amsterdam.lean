import EvmSemantics.EVM.Step
set_option warningAsError true
set_option maxRecDepth 100000
/-!
# The `Amsterdam` patch to the semantics

The vendored semantics (`deps/evm-semantics`, powdr-labs/evm-semantics 2f8714d
plus a patch) adds a fork `Amsterdam` with EIP-8024 (`DUPN` / `SWAPN` /
`EXCHANGE`) and EIP-7954 (code size limit). This module states what the patch
changes and what it does not:

1. **The forks up to Osaka are unchanged.** The patch edits the bodies of
   `Operation.availableInFork`, `State.maxCodeSize`, `Gas.maxInitCodeSize`
   and the `StepRunning.dupN` / `swapN` / `exchange` rules (plus the
   accessors those rules read). On every fork before `Amsterdam`:
   * `availableInFork` equals its 2f8714d definition, copied verbatim below
     (`availableInFork_eq_2f8714d`), so `State.decoded` (whose own definition
     and `Decode.decodeAt` are untouched) is unchanged;
   * the three EIP-8024 operations never decode, so the edited `StepRunning`
     rules, whose `h_op` premise is such a decode, never apply
     (`decodedOp_ne_dupN` and the two below);
   * the code size limits are 24,576 and 49,152 bytes, as before;
   * `Fork.toOrd`, which every `fork ≥ X` test compares, is unchanged
     (`toOrd_eq_2f8714d`).
2. **EIP-8024's immediate decoding is the execution specs'.**
   `decodeSingle` / `validSingle` and `decodePair` / `validPair` agree with
   `decode_single` and `decode_pair` of ethereum/execution-specs `fd92984`
   (`forks/amsterdam/vm/stack.py`) on all 256 bytes, including which bytes
   raise `InvalidParameter` (`decodeSingle_eels`, `decodePair_eels`; the
   tables were produced by running those two Python functions).
-/

namespace EvmProof.Amsterdam

open EvmSemantics
open EvmSemantics.EVM

/-! ## Forks before Amsterdam -/

/-- `Fork.toOrd` as defined at powdr-labs/evm-semantics 2f8714d. -/
def toOrd2f8714d : Fork → Option Nat
  | .Frontier => some 0 | .Homestead => some 1 | .TangerineWhistle => some 2
  | .SpuriousDragon => some 3 | .Byzantium => some 4 | .Constantinople => some 5
  | .Petersburg => some 6 | .Istanbul => some 7 | .MuirGlacier => some 8
  | .Berlin => some 9 | .London => some 10 | .ArrowGlacier => some 11
  | .GrayGlacier => some 12 | .Paris => some 13 | .Shanghai => some 14
  | .Cancun => some 15 | .Prague => some 16 | .Osaka => some 17
  | .Amsterdam => none

/-- Every fork other than `Amsterdam` keeps its position (`none` marks the
fork 2f8714d does not have). -/
theorem toOrd_eq_2f8714d (f : Fork) (hf : f ≠ .Amsterdam) :
    toOrd2f8714d f = some f.toOrd := by
  cases f <;> simp_all [toOrd2f8714d, Fork.toOrd]

theorem lt_amsterdam_iff (f : Fork) : f < .Amsterdam ↔ f ≠ .Amsterdam := by
  cases f <;> decide

/-- `Operation.availableInFork` as defined at powdr-labs/evm-semantics
2f8714d, verbatim. -/
def availableInFork2f8714d : Operation → Fork → Bool
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
  | .DupN _,                  _ => false
  | .SwapN _,                 _ => false
  | .Exchange _,              _ => false
  | _,                        _ => true

/-- Before Amsterdam, opcode availability is exactly 2f8714d's. -/
theorem availableInFork_eq_2f8714d (op : Operation) (f : Fork) (hf : f < .Amsterdam) :
    op.availableInFork f = availableInFork2f8714d op f := by
  have hge : ¬ f ≥ .Amsterdam := by
    change ¬ Fork.Amsterdam.toOrd ≤ f.toOrd
    change f.toOrd < Fork.Amsterdam.toOrd at hf
    omega
  cases op with
  | StopArith o => cases o <;> rfl
  | CompBit o => cases o <;> rfl
  | Keccak o => cases o; rfl
  | Env o => cases o <;> rfl
  | Block o => cases o <;> rfl
  | StackMemFlow o => cases o <;> rfl
  | Push p => rfl
  | Dup d => rfl
  | Swap d => rfl
  | DupN d => simp [Operation.availableInFork, availableInFork2f8714d, hge]
  | SwapN d => simp [Operation.availableInFork, availableInFork2f8714d, hge]
  | Exchange e => simp [Operation.availableInFork, availableInFork2f8714d, hge]
  | Log l => rfl
  | System o => cases o <;> rfl

theorem available_of_decodedOp {s : State} {op : Operation}
    (h : s.decodedOp = some op) : op.availableInFork s.fork = true := by
  unfold State.decodedOp State.decoded at h
  cases hd : Decode.decodeAt s.executionEnv.code s.pc.toNat with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨op', imm⟩ := p
    by_cases ha : op'.availableInFork s.fork = true
    · simp_all
    · simp_all

/-- Before Amsterdam no state decodes `DUPN`, so `StepRunning.dupN` never
applies. -/
theorem decodedOp_ne_dupN {s : State} (hf : s.fork < .Amsterdam)
    (d : Operation.DupNOp) : s.decodedOp ≠ some (.DupN d) := fun h => by
  have := available_of_decodedOp h
  rw [availableInFork_eq_2f8714d _ _ hf] at this
  simp [availableInFork2f8714d] at this

theorem decodedOp_ne_swapN {s : State} (hf : s.fork < .Amsterdam)
    (d : Operation.SwapNOp) : s.decodedOp ≠ some (.SwapN d) := fun h => by
  have := available_of_decodedOp h
  rw [availableInFork_eq_2f8714d _ _ hf] at this
  simp [availableInFork2f8714d] at this

theorem decodedOp_ne_exchange {s : State} (hf : s.fork < .Amsterdam)
    (e : Operation.ExchangeOp) : s.decodedOp ≠ some (.Exchange e) := fun h => by
  have := available_of_decodedOp h
  rw [availableInFork_eq_2f8714d _ _ hf] at this
  simp [availableInFork2f8714d] at this

/-- EIP-170's limit before Amsterdam is 2f8714d's constant. -/
theorem maxCodeSize_eq (f : Fork) (hf : f < .Amsterdam) :
    State.maxCodeSize f = 24576 := by
  have hge : ¬ f ≥ .Amsterdam := by
    change ¬ Fork.Amsterdam.toOrd ≤ f.toOrd
    change f.toOrd < Fork.Amsterdam.toOrd at hf
    omega
  simp [State.maxCodeSize, hge]

/-- EIP-3860's limit before Amsterdam is 2f8714d's constant. -/
theorem maxInitCodeSize_eq (f : Fork) (hf : f < .Amsterdam) :
    Gas.maxInitCodeSize f = 49152 := by
  have hge : ¬ f ≥ .Amsterdam := by
    change ¬ Fork.Amsterdam.toOrd ≤ f.toOrd
    change f.toOrd < Fork.Amsterdam.toOrd at hf
    omega
  simp [Gas.maxInitCodeSize, hge]

/-! ## Amsterdam: EIP-8024 and EIP-7954 -/

theorem maxCodeSize_amsterdam : State.maxCodeSize .Amsterdam = 65536 := rfl
theorem maxInitCodeSize_amsterdam : Gas.maxInitCodeSize .Amsterdam = 131072 := rfl

/-- `decode_single(x)` of execution-specs `fd92984` for `x = 0..255`; `none`
where it raises `InvalidParameter`. -/
def eelsDecodeSingle : List (Option Nat) :=
  [some 145, some 146, some 147, some 148, some 149, some 150, some 151, some 152, some 153, some 154, some 155, some 156,
   some 157, some 158, some 159, some 160, some 161, some 162, some 163, some 164, some 165, some 166, some 167, some 168,
   some 169, some 170, some 171, some 172, some 173, some 174, some 175, some 176, some 177, some 178, some 179, some 180,
   some 181, some 182, some 183, some 184, some 185, some 186, some 187, some 188, some 189, some 190, some 191, some 192,
   some 193, some 194, some 195, some 196, some 197, some 198, some 199, some 200, some 201, some 202, some 203, some 204,
   some 205, some 206, some 207, some 208, some 209, some 210, some 211, some 212, some 213, some 214, some 215, some 216,
   some 217, some 218, some 219, some 220, some 221, some 222, some 223, some 224, some 225, some 226, some 227, some 228,
   some 229, some 230, some 231, some 232, some 233, some 234, some 235, none, none, none, none, none,
   none, none, none, none, none, none, none, none, none, none, none, none,
   none, none, none, none, none, none, none, none, none, none, none, none,
   none, none, none, none, none, none, none, none, some 17, some 18, some 19, some 20,
   some 21, some 22, some 23, some 24, some 25, some 26, some 27, some 28, some 29, some 30, some 31, some 32,
   some 33, some 34, some 35, some 36, some 37, some 38, some 39, some 40, some 41, some 42, some 43, some 44,
   some 45, some 46, some 47, some 48, some 49, some 50, some 51, some 52, some 53, some 54, some 55, some 56,
   some 57, some 58, some 59, some 60, some 61, some 62, some 63, some 64, some 65, some 66, some 67, some 68,
   some 69, some 70, some 71, some 72, some 73, some 74, some 75, some 76, some 77, some 78, some 79, some 80,
   some 81, some 82, some 83, some 84, some 85, some 86, some 87, some 88, some 89, some 90, some 91, some 92,
   some 93, some 94, some 95, some 96, some 97, some 98, some 99, some 100, some 101, some 102, some 103, some 104,
   some 105, some 106, some 107, some 108, some 109, some 110, some 111, some 112, some 113, some 114, some 115, some 116,
   some 117, some 118, some 119, some 120, some 121, some 122, some 123, some 124, some 125, some 126, some 127, some 128,
   some 129, some 130, some 131, some 132, some 133, some 134, some 135, some 136, some 137, some 138, some 139, some 140,
   some 141, some 142, some 143, some 144]

/-- `decode_pair(x)` of execution-specs `fd92984` for `x = 0..255`; `none`
where it raises `InvalidParameter`. -/
def eelsDecodePair : List (Option (Nat × Nat)) :=
  [some (9, 16), some (9, 15), some (9, 14), some (9, 13), some (9, 12), some (9, 11),
   some (9, 10), some (9, 21), some (8, 21), some (7, 21), some (6, 21), some (5, 21),
   some (4, 21), some (3, 21), some (2, 21), some (1, 21), some (10, 16), some (10, 15),
   some (10, 14), some (10, 13), some (10, 12), some (10, 11), some (10, 20), some (9, 20),
   some (8, 20), some (7, 20), some (6, 20), some (5, 20), some (4, 20), some (3, 20),
   some (2, 20), some (1, 20), some (11, 16), some (11, 15), some (11, 14), some (11, 13),
   some (11, 12), some (11, 19), some (10, 19), some (9, 19), some (8, 19), some (7, 19),
   some (6, 19), some (5, 19), some (4, 19), some (3, 19), some (2, 19), some (1, 19),
   some (12, 16), some (12, 15), some (12, 14), some (12, 13), some (12, 18), some (11, 18),
   some (10, 18), some (9, 18), some (8, 18), some (7, 18), some (6, 18), some (5, 18),
   some (4, 18), some (3, 18), some (2, 18), some (1, 18), some (13, 16), some (13, 15),
   some (13, 14), some (13, 17), some (12, 17), some (11, 17), some (10, 17), some (9, 17),
   some (8, 17), some (7, 17), some (6, 17), some (5, 17), some (4, 17), some (3, 17),
   some (2, 17), some (1, 17), some (14, 16), some (14, 15), none, none,
   none, none, none, none, none, none,
   none, none, none, none, none, none,
   none, none, none, none, none, none,
   none, none, none, none, none, none,
   none, none, none, none, none, none,
   none, none, none, none, none, none,
   none, none, none, none, none, none,
   none, none, some (1, 16), some (1, 15), some (1, 14), some (1, 13),
   some (1, 12), some (1, 11), some (1, 10), some (1, 9), some (1, 8), some (1, 7),
   some (1, 6), some (1, 5), some (1, 4), some (1, 3), some (1, 2), some (1, 29),
   some (2, 16), some (2, 15), some (2, 14), some (2, 13), some (2, 12), some (2, 11),
   some (2, 10), some (2, 9), some (2, 8), some (2, 7), some (2, 6), some (2, 5),
   some (2, 4), some (2, 3), some (2, 28), some (1, 28), some (3, 16), some (3, 15),
   some (3, 14), some (3, 13), some (3, 12), some (3, 11), some (3, 10), some (3, 9),
   some (3, 8), some (3, 7), some (3, 6), some (3, 5), some (3, 4), some (3, 27),
   some (2, 27), some (1, 27), some (4, 16), some (4, 15), some (4, 14), some (4, 13),
   some (4, 12), some (4, 11), some (4, 10), some (4, 9), some (4, 8), some (4, 7),
   some (4, 6), some (4, 5), some (4, 26), some (3, 26), some (2, 26), some (1, 26),
   some (5, 16), some (5, 15), some (5, 14), some (5, 13), some (5, 12), some (5, 11),
   some (5, 10), some (5, 9), some (5, 8), some (5, 7), some (5, 6), some (5, 25),
   some (4, 25), some (3, 25), some (2, 25), some (1, 25), some (6, 16), some (6, 15),
   some (6, 14), some (6, 13), some (6, 12), some (6, 11), some (6, 10), some (6, 9),
   some (6, 8), some (6, 7), some (6, 24), some (5, 24), some (4, 24), some (3, 24),
   some (2, 24), some (1, 24), some (7, 16), some (7, 15), some (7, 14), some (7, 13),
   some (7, 12), some (7, 11), some (7, 10), some (7, 9), some (7, 8), some (7, 23),
   some (6, 23), some (5, 23), some (4, 23), some (3, 23), some (2, 23), some (1, 23),
   some (8, 16), some (8, 15), some (8, 14), some (8, 13), some (8, 12), some (8, 11),
   some (8, 10), some (8, 9), some (8, 22), some (7, 22), some (6, 22), some (5, 22),
   some (4, 22), some (3, 22), some (2, 22), some (1, 22)]

theorem decodeSingle_eels :
    (List.range 256).map (fun x =>
      if Operation.validSingle x then some (Operation.decodeSingle x) else none)
      = eelsDecodeSingle := by decide

theorem decodePair_eels :
    (List.range 256).map (fun x =>
      if Operation.validPair x then some (Operation.decodePair x) else none)
      = eelsDecodePair := by decide

/-- A valid DUPN / SWAPN immediate names an item in `[17, 235]`; in particular
`SwapNOp.n + 1 = decodeSingle imm` for the immediates that decode. -/
theorem decodeSingle_range (x : Fin 256) (h : Operation.validSingle x.val = true) :
    17 ≤ Operation.decodeSingle x.val ∧ Operation.decodeSingle x.val ≤ 235 := by
  revert x; decide

/-- A valid EXCHANGE immediate names `1 ≤ n < m ≤ 30 - n`. -/
theorem decodePair_range (x : Fin 256) (h : Operation.validPair x.val = true) :
    1 ≤ (Operation.decodePair x.val).1 ∧
      (Operation.decodePair x.val).1 < (Operation.decodePair x.val).2 ∧
      (Operation.decodePair x.val).2 ≤ 30 - (Operation.decodePair x.val).1 := by
  revert x; decide

/-- On Amsterdam, a decoded `DUPN` carries a valid immediate. -/
theorem valid_of_decodedOp_dupN {s : State} {d : Operation.DupNOp}
    (h : s.decodedOp = some (.DupN d)) : Operation.validSingle d.imm.val = true := by
  have := available_of_decodedOp h
  simp only [Operation.availableInFork, Bool.and_eq_true] at this
  exact this.2

theorem valid_of_decodedOp_swapN {s : State} {d : Operation.SwapNOp}
    (h : s.decodedOp = some (.SwapN d)) : Operation.validSingle d.imm.val = true := by
  have := available_of_decodedOp h
  simp only [Operation.availableInFork, Bool.and_eq_true] at this
  exact this.2

theorem valid_of_decodedOp_exchange {s : State} {e : Operation.ExchangeOp}
    (h : s.decodedOp = some (.Exchange e)) : Operation.validPair e.packed.val = true := by
  have := available_of_decodedOp h
  simp only [Operation.availableInFork, Bool.and_eq_true] at this
  exact this.2

end EvmProof.Amsterdam
