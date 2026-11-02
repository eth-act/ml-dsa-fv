import EvmProof.Program
set_option warningAsError true
/-!
# Instruction-boundary artifacts with EIP-8024 instructions

The compiler IR `YulEvmCompiler.Instr` has only `PUSHk` and one-byte
operations, so `ProgramArtifact` cannot describe bytecode that uses EIP-8024's
two-byte `DUPN` / `SWAPN` / `EXCHANGE` (opcode, then one immediate byte).
`XInstr` adds them; `XArtifact` is `ProgramArtifact` over `XInstr`. Both are new
names: `Instr`, `ProgramArtifact` and everything stated with them are unchanged.

As for `ProgramArtifact`, one byte equation (`assembly_eq`) yields decoder facts
by instruction index (`decodeAt_base_op`, `decodeAt_base_push`,
`decodeAt_dupN`, ...) and the JUMPDEST facts (`isValidJumpDest_index`).

JUMPDEST analysis does not skip EIP-8024 immediates: the walk visits the
immediate byte as an instruction of its own. That is harmless exactly because
the immediates that decode are never PUSH opcodes (`validSingle`, `validPair`
exclude `0x5b..0x7f`), which `isValidJumpDest_index` requires of every
instruction before the target (`XInstr.ImmOK`).
-/

namespace EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-- `Instr` plus the EIP-8024 instructions, each with its raw immediate byte. -/
inductive XInstr where
  | base (i : Instr)
  | dupN (x : Fin 256)
  | swapN (x : Fin 256)
  | exchange (x : Fin 256)
  deriving Repr

namespace XInstr

/-- The bytes an instruction assembles to. -/
def bytes : XInstr → List UInt8
  | base i => i.bytes
  | dupN x => [0xe6, UInt8.ofNat x.val]
  | swapN x => [0xe7, UInt8.ofNat x.val]
  | exchange x => [0xe8, UInt8.ofNat x.val]

/-- An EIP-8024 immediate is valid (so it is not a PUSH opcode, and JUMPDEST
analysis steps over it as a one-byte instruction). -/
def ImmOK : XInstr → Prop
  | base _ => True
  | dupN x => Operation.validSingle x.val = true
  | swapN x => Operation.validSingle x.val = true
  | exchange x => Operation.validPair x.val = true

instance (i : XInstr) : Decidable i.ImmOK := by
  cases i <;> simp only [ImmOK] <;> infer_instance

theorem bytes_pos (i : XInstr) : 1 ≤ i.bytes.length := by
  cases i with
  | base i => cases i <;> simp [bytes]
  | _ => simp [bytes]

end XInstr

/-- Bytes of an instruction list. -/
def xassembleBytes (is : List XInstr) : List UInt8 := is.flatMap XInstr.bytes

@[simp] theorem xassembleBytes_nil : xassembleBytes [] = [] := rfl

@[simp] theorem xassembleBytes_cons (i : XInstr) (is : List XInstr) :
    xassembleBytes (i :: is) = i.bytes ++ xassembleBytes is := rfl

theorem xassembleBytes_append (is js : List XInstr) :
    xassembleBytes (is ++ js) = xassembleBytes is ++ xassembleBytes js := by
  simp [xassembleBytes]

/-- Assemble to the `ByteArray` the EVM semantics executes. -/
def xassemble (is : List XInstr) : ByteArray := mkCode (xassembleBytes is)

/-- A byte array with an instruction-boundary view that may use EIP-8024. -/
structure XArtifact where
  code : ByteArray
  instructions : List XInstr
  assembly_eq : xassemble instructions = code

/-! ### Byte-level decoding of the EIP-8024 instructions -/

private theorem getElem_at (pre post : List UInt8) (b : UInt8) (rest : List UInt8)
    (h : pre.length < (mkCode (pre ++ (b :: rest) ++ post)).size) :
    (mkCode (pre ++ (b :: rest) ++ post))[pre.length] = b := by
  rw [getElem_mkCode]
  simp [List.getElem_append_right]

private theorem getElem_at_succ (pre post : List UInt8) (b c : UInt8)
    (h : pre.length + 1 < (mkCode (pre ++ [b, c] ++ post)).size) :
    (mkCode (pre ++ [b, c] ++ post))[pre.length + 1] = c := by
  rw [getElem_mkCode]
  simp [List.getElem_append_right]

private theorem fin_ofNat_toNat (x : Fin 256) :
    (⟨(UInt8.ofNat x.val).toNat, by have := (UInt8.ofNat x.val).toNat_lt; omega⟩ : Fin 256)
      = x := by
  apply Fin.ext
  simp

theorem decodeAt_dupN_bytes (pre post : List UInt8) (x : Fin 256) :
    Decode.decodeAt (mkCode (pre ++ (XInstr.dupN x).bytes ++ post)) pre.length
      = some (.DupN ⟨x⟩, none) := by
  have hsz : pre.length < (mkCode (pre ++ [0xe6, UInt8.ofNat x.val] ++ post)).size := by
    simp
  have hsz1 : pre.length + 1 < (mkCode (pre ++ [0xe6, UInt8.ofNat x.val] ++ post)).size := by
    simp
  show Decode.decodeAt (mkCode (pre ++ [0xe6, UInt8.ofNat x.val] ++ post)) pre.length = _
  unfold Decode.decodeAt
  rw [dif_pos hsz, getElem_at pre post 0xe6 [UInt8.ofNat x.val] hsz]
  simp only [show Decode.opcodeOf 0xe6 = some (.DupN ⟨0, by decide⟩) from rfl,
    dif_pos hsz1, getElem_at_succ pre post 0xe6 (UInt8.ofNat x.val) hsz1]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [fin_ofNat_toNat]

theorem decodeAt_swapN_bytes (pre post : List UInt8) (x : Fin 256) :
    Decode.decodeAt (mkCode (pre ++ (XInstr.swapN x).bytes ++ post)) pre.length
      = some (.SwapN ⟨x⟩, none) := by
  have hsz : pre.length < (mkCode (pre ++ [0xe7, UInt8.ofNat x.val] ++ post)).size := by
    simp
  have hsz1 : pre.length + 1 < (mkCode (pre ++ [0xe7, UInt8.ofNat x.val] ++ post)).size := by
    simp
  show Decode.decodeAt (mkCode (pre ++ [0xe7, UInt8.ofNat x.val] ++ post)) pre.length = _
  unfold Decode.decodeAt
  rw [dif_pos hsz, getElem_at pre post 0xe7 [UInt8.ofNat x.val] hsz]
  simp only [show Decode.opcodeOf 0xe7 = some (.SwapN ⟨0, by decide⟩) from rfl,
    dif_pos hsz1, getElem_at_succ pre post 0xe7 (UInt8.ofNat x.val) hsz1]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [fin_ofNat_toNat]

theorem decodeAt_exchange_bytes (pre post : List UInt8) (x : Fin 256) :
    Decode.decodeAt (mkCode (pre ++ (XInstr.exchange x).bytes ++ post)) pre.length
      = some (.Exchange ⟨x⟩, none) := by
  have hsz : pre.length < (mkCode (pre ++ [0xe8, UInt8.ofNat x.val] ++ post)).size := by
    simp
  have hsz1 : pre.length + 1 < (mkCode (pre ++ [0xe8, UInt8.ofNat x.val] ++ post)).size := by
    simp
  show Decode.decodeAt (mkCode (pre ++ [0xe8, UInt8.ofNat x.val] ++ post)) pre.length = _
  unfold Decode.decodeAt
  rw [dif_pos hsz, getElem_at pre post 0xe8 [UInt8.ofNat x.val] hsz]
  simp only [show Decode.opcodeOf 0xe8 = some (.Exchange ⟨0, by decide⟩) from rfl,
    dif_pos hsz1, getElem_at_succ pre post 0xe8 (UInt8.ofNat x.val) hsz1]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [fin_ofNat_toNat]

/-! ### JUMPDEST analysis -/

/-- The immediate-width rule of `Decode.pushDataSize`, as a function of the
opcode byte. -/
private def pushWidth (b : UInt8) : Nat :=
  match Decode.opcodeOf b with
  | some (.Push p) => p.width.val
  | _ => 0

private theorem pushDataSize_eq (code : ByteArray) (pc : Nat) (h : pc < code.size) :
    Decode.pushDataSize code pc = pushWidth code[pc] := by
  unfold Decode.pushDataSize pushWidth
  rw [dif_pos h]
  rfl

set_option maxRecDepth 10000 in
private theorem pushWidth_single (x : Fin 256) (h : Operation.validSingle x.val = true) :
    pushWidth (UInt8.ofNat x.val) = 0 := by
  revert x; decide

set_option maxRecDepth 10000 in
private theorem pushWidth_pair (x : Fin 256) (h : Operation.validPair x.val = true) :
    pushWidth (UInt8.ofNat x.val) = 0 := by
  revert x; decide

private theorem pushWidth_opByte (o : Operation) : pushWidth (Instr.opByte o) = 0 := by
  unfold pushWidth
  cases o with
  | StopArith op => cases op <;> rfl
  | CompBit op => cases op <;> rfl
  | Keccak op =>
    cases op
    rfl
  | Env op => cases op <;> rfl
  | Block op => cases op <;> rfl
  | StackMemFlow op => cases op <;> rfl
  | Push p => rfl
  | Dup d =>
    obtain ⟨⟨n, hn⟩⟩ := d
    rw [(dup_roundtrip ⟨n, hn⟩).1]
  | Swap s =>
    obtain ⟨⟨n, hn⟩⟩ := s
    rw [(swap_roundtrip ⟨n, hn⟩).1]
  | DupN d => rfl
  | SwapN s => rfl
  | Exchange e => rfl
  | Log l =>
    obtain ⟨⟨n, hn⟩⟩ := l
    match n, hn with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  | System op => cases op <;> rfl

/-- One step of the walk over a byte that is not the target. -/
private theorem walk_step (code : ByteArray) (target pc fuel : Nat)
    (hlt : pc < target) (hsz : pc < code.size) :
    Decode.validJumpDestFrom code target pc (fuel + 1) =
      Decode.validJumpDestFrom code target (pc + 1 + pushWidth code[pc]) fuel := by
  conv => lhs; unfold Decode.validJumpDestFrom
  rw [if_neg (by omega), if_neg (by omega), pushDataSize_eq code pc hsz]

/-- The walk's step at the first byte `b` of a chunk. -/
private theorem walk_one (pre post : List UInt8) (b : UInt8) (rest : List UInt8)
    (target f : Nat) (htarget : pre.length < target) :
    Decode.validJumpDestFrom (mkCode (pre ++ (b :: rest) ++ post)) target pre.length (f + 1) =
      Decode.validJumpDestFrom (mkCode (pre ++ (b :: rest) ++ post)) target
        (pre.length + 1 + pushWidth b) f := by
  have hsz : pre.length < (mkCode (pre ++ (b :: rest) ++ post)).size := by simp
  rw [walk_step _ _ _ _ htarget hsz, getElem_at pre post b rest hsz]

/-- Bytes the walk visits as instruction starts: one for `Instr`, two for an
EIP-8024 instruction (its immediate is visited too). -/
private def XInstr.steps : XInstr → Nat
  | .base _ => 1
  | _ => 2

private theorem steps_le (i : XInstr) : i.steps ≤ i.bytes.length := by
  have := XInstr.bytes_pos i
  cases i <;> simp_all [XInstr.steps, XInstr.bytes]

/-- Two-byte chunk whose bytes are both stepped over. -/
private theorem walk_two (pre post : List UInt8) (b c : UInt8)
    (hb : pushWidth b = 0) (hc : pushWidth c = 0) (target f : Nat)
    (htarget : pre.length + 2 ≤ target) :
    Decode.validJumpDestFrom (mkCode (pre ++ [b, c] ++ post)) target pre.length (f + 2) =
      Decode.validJumpDestFrom (mkCode (pre ++ [b, c] ++ post)) target
        (pre.length + 2) f := by
  rw [show f + 2 = (f + 1) + 1 by omega, walk_one pre post b [c] _ _ (by omega), hb]
  rw [show pre ++ [b, c] ++ post = (pre ++ [b]) ++ (c :: []) ++ post by simp]
  have := walk_one (pre ++ [b]) post c [] target f (by simp; omega)
  simp only [List.length_append, List.length_cons, List.length_nil, hc] at this ⊢
  rw [Nat.add_zero, this]

/-- The walk passes over one instruction, from its first byte to the next
instruction's. -/
private theorem walk_instr (i : XInstr) (hi : i.ImmOK) (pre post : List UInt8)
    (target f : Nat) (htarget : (pre ++ i.bytes).length ≤ target) :
    Decode.validJumpDestFrom (mkCode (pre ++ i.bytes ++ post)) target pre.length
        (f + i.steps) =
      Decode.validJumpDestFrom (mkCode (pre ++ i.bytes ++ post)) target
        (pre ++ i.bytes).length f := by
  have hlen := XInstr.bytes_pos i
  cases i with
  | base i =>
    cases i with
    | push w v =>
      have := walk_one pre post (UInt8.ofNat (0x5f + w.val)) (natToBE v.toNat w.val) target f
        (by simp [XInstr.bytes] at htarget ⊢; omega)
      have hw : pushWidth (UInt8.ofNat (0x5f + w.val)) = w.val := by
        unfold pushWidth
        rw [opcodeOf_push w]
      simp only [XInstr.steps, XInstr.bytes, Instr.bytes]
      rw [this, hw]
      congr 1
      simp only [List.length_append, List.length_cons, length_natToBE]
      omega
    | op o =>
      have := walk_one pre post (Instr.opByte o) [] target f
        (by simp [XInstr.bytes, Instr.bytes] at htarget ⊢; omega)
      simp only [XInstr.steps, XInstr.bytes, Instr.bytes]
      rw [this, pushWidth_opByte]
      simp
  | dupN x =>
    simp only [XInstr.steps, XInstr.bytes] at htarget ⊢
    rw [walk_two pre post _ _ rfl (pushWidth_single x hi) target f (by simp at htarget; omega)]
    simp
  | swapN x =>
    simp only [XInstr.steps, XInstr.bytes] at htarget ⊢
    rw [walk_two pre post _ _ rfl (pushWidth_single x hi) target f (by simp at htarget; omega)]
    simp
  | exchange x =>
    simp only [XInstr.steps, XInstr.bytes] at htarget ⊢
    rw [walk_two pre post _ _ rfl (pushWidth_pair x hi) target f (by simp at htarget; omega)]
    simp

private theorem walk_through :
    ∀ (is : List XInstr) (pre rest : List UInt8) (fuel : Nat),
      (∀ i ∈ is, i.ImmOK) → (xassembleBytes is).length + 1 ≤ fuel →
      Decode.validJumpDestFrom (mkCode (pre ++ xassembleBytes is ++ 0x5b :: rest))
        (pre.length + (xassembleBytes is).length) pre.length fuel = true := by
  intro is
  induction is with
  | nil =>
    intro pre rest fuel _ hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    simp only [xassembleBytes_nil, List.append_nil, List.length_nil, Nat.add_zero]
    unfold Decode.validJumpDestFrom
    have hsz : pre.length < (mkCode (pre ++ 0x5b :: rest)).size := by simp
    rw [if_pos rfl, dif_pos hsz]
    have hb := getElem_at pre [] 0x5b rest (by simp)
    simp only [List.append_nil] at hb
    simp [hb]
  | cons i is ih =>
    intro pre rest fuel hok hfuel
    have hpos := XInstr.bytes_pos i
    have hst := steps_le i
    simp only [xassembleBytes_cons, List.length_append] at hfuel ⊢
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + i.steps := ⟨fuel - i.steps, by omega⟩
    rw [show pre ++ (i.bytes ++ xassembleBytes is) ++ 0x5b :: rest
        = pre ++ i.bytes ++ (xassembleBytes is ++ 0x5b :: rest) by simp]
    rw [walk_instr i (hok i (by simp)) pre _ _ f (by simp)]
    rw [show pre ++ i.bytes ++ (xassembleBytes is ++ 0x5b :: rest)
        = (pre ++ i.bytes) ++ xassembleBytes is ++ 0x5b :: rest by simp]
    have := ih (pre ++ i.bytes) rest f (fun j hj => hok j (by simp [hj])) (by omega)
    simpa [Nat.add_assoc] using this

namespace XArtifact

/-- Byte offset of an instruction index. -/
def instructionPC (p : XArtifact) (index : Nat) : Nat :=
  (xassembleBytes (p.instructions.take index)).length

private theorem split_at_get {α : Type} {xs : List α} {index : Nat} {x : α}
    (hget : xs[index]? = some x) :
    xs = xs.take index ++ x :: xs.drop (index + 1) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hget
  calc
    xs = xs.take index ++ xs.drop index := (List.take_append_drop index xs).symm
    _ = xs.take index ++ x :: xs.drop (index + 1) := by
      rw [List.drop_eq_getElem_cons hi, hx]

/-- The code around the instruction at an index. -/
theorem code_split (p : XArtifact) {index : Nat} {i : XInstr}
    (hget : p.instructions[index]? = some i) :
    p.code = mkCode (xassembleBytes (p.instructions.take index) ++ i.bytes ++
      xassembleBytes (p.instructions.drop (index + 1))) := by
  rw [← p.assembly_eq]
  unfold xassemble
  congr 1
  conv => lhs; rw [split_at_get hget]
  rw [xassembleBytes_append, xassembleBytes_cons]
  simp [List.append_assoc]

theorem decodeAt_base_op (p : XArtifact) (index : Nat) (o : Operation)
    (hget : p.instructions[index]? = some (.base (.op o)))
    (hopcode : Decode.opcodeOf (Instr.opByte o) = some o)
    (hplain : YulEvmCompiler.plainOp o) :
    Decode.decodeAt p.code (p.instructionPC index) = some (o, none) := by
  rw [p.code_split hget]
  exact YulEvmCompiler.decodeAt_op _ _ o hopcode hplain

theorem decodeAt_base_push (p : XArtifact) (index : Nat)
    (width : Fin 33) (value : UInt256)
    (hget : p.instructions[index]? = some (.base (.push width value)))
    (hfit : value.toNat < 256 ^ width.val) :
    Decode.decodeAt p.code (p.instructionPC index) =
      some (.Push ⟨width⟩, some (value, width.val)) := by
  rw [p.code_split hget]
  exact YulEvmCompiler.decodeAt_push _ _ width value hfit

theorem decodeAt_dupN (p : XArtifact) (index : Nat) (x : Fin 256)
    (hget : p.instructions[index]? = some (.dupN x)) :
    Decode.decodeAt p.code (p.instructionPC index) = some (.DupN ⟨x⟩, none) := by
  rw [p.code_split hget]
  exact decodeAt_dupN_bytes _ _ x

theorem decodeAt_swapN (p : XArtifact) (index : Nat) (x : Fin 256)
    (hget : p.instructions[index]? = some (.swapN x)) :
    Decode.decodeAt p.code (p.instructionPC index) = some (.SwapN ⟨x⟩, none) := by
  rw [p.code_split hget]
  exact decodeAt_swapN_bytes _ _ x

theorem decodeAt_exchange (p : XArtifact) (index : Nat) (x : Fin 256)
    (hget : p.instructions[index]? = some (.exchange x)) :
    Decode.decodeAt p.code (p.instructionPC index) = some (.Exchange ⟨x⟩, none) := by
  rw [p.code_split hget]
  exact decodeAt_exchange_bytes _ _ x

/-- A `JUMPDEST` at an instruction boundary passes the jumpdest analysis,
provided every EIP-8024 immediate before it is valid. -/
theorem isValidJumpDest_index (p : XArtifact) (index : Nat)
    (hget : p.instructions[index]? = some (.base (.op .JUMPDEST)))
    (hok : ∀ i ∈ p.instructions.take index, i.ImmOK) :
    Decode.isValidJumpDest p.code (p.instructionPC index) = true := by
  rw [p.code_split hget]
  unfold Decode.isValidJumpDest instructionPC
  have h := walk_through (p.instructions.take index) []
    (xassembleBytes (p.instructions.drop (index + 1)))
    ((mkCode (xassembleBytes (p.instructions.take index) ++
      (XInstr.base (.op .JUMPDEST)).bytes ++
      xassembleBytes (p.instructions.drop (index + 1)))).size + 1)
    hok (by simp)
  simpa [XInstr.bytes, Instr.bytes, Instr.opByte] using h

end XArtifact
end EvmProof
