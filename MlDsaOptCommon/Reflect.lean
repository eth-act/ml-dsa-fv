import MlDsaOptCommon.Word
import MlDsaOptCommon.Memory
namespace MlDsaOptCommon.Reflect
open EvmSemantics EvmSemantics.EVM EvmProof.Stepper YulEvmCompiler
open MlDsaOptCommon
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private theorem push0_eq : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := rfl

inductive Bin where
  | add | mul | sub | lt | gt | eq | xor | land | lor | shl | shr
  deriving DecidableEq
def Bin.eval : Bin → UInt256 → UInt256 → UInt256
  | .add => (· + ·)
  | .mul => (· * ·)
  | .sub => (· - ·)
  | .lt => UInt256.lt
  | .gt => UInt256.gt
  | .eq => UInt256.eq
  | .xor => UInt256.xor
  | .land => UInt256.land
  | .lor => UInt256.lor
  | .shl => fun a b => UInt256.shiftLeft b a
  | .shr => fun a b => UInt256.shiftRight b a
def Bin.instr : Bin → Instr
  | .add => .op .ADD
  | .mul => .op .MUL
  | .sub => .op .SUB
  | .lt => .op .LT
  | .gt => .op .GT
  | .eq => .op .EQ
  | .xor => .op .XOR
  | .land => .op .AND
  | .lor => .op .OR
  | .shl => .op .SHL
  | .shr => .op .SHR

inductive Un where
  | iszero | not
  deriving DecidableEq
def Un.eval : Un → UInt256 → UInt256
  | .iszero => UInt256.isZero
  | .not => UInt256.lnot
def Un.instr : Un → Instr
  | .iszero => .op .ISZERO
  | .not => .op .NOT

mutual
inductive Term where
  | var (n : Nat)
  | lit (n : Nat)
  | bin (b : Bin) (a c : Term)
  | un (u : Un) (a : Term)
  | load (m : Mem) (a : Term)
  deriving DecidableEq
inductive Mem where
  | initial
  | store (m : Mem) (a v : Term)
  deriving DecidableEq
end
mutual
def Term.eval (ρ : Nat → UInt256) (M : ByteArray) : Term → UInt256
  | .var n => ρ n
  | .lit n => wd n
  | .bin b a c => b.eval (a.eval ρ M) (c.eval ρ M)
  | .un u a => u.eval (a.eval ρ M)
  | .load m a => MachineState.readWord (m.eval ρ M) (a.eval ρ M).toNat
def Mem.eval (ρ : Nat → UInt256) (M : ByteArray) : Mem → ByteArray
  | .initial => M
  | .store m a v => MachineState.writeBytes (m.eval ρ M)
      (Data.Bytes.natToBytesPadded (v.eval ρ M).toNat 32) (a.eval ρ M).toNat
end

inductive Op where
  | push (w : Fin 33) (n : Nat)
  | dup (n : Fin 16)
  | swap (n : Fin 16)
  | bin (b : Bin)
  | un (u : Un)
  | pop
  | jump (target : Nat)
  | jumpi (target : Nat) (taken : Bool)
  | load | store | dest
  deriving DecidableEq
def Op.instr : Op → Instr
  | .push w n => .push w (wd n)
  | .dup n => .op (.Dup ⟨n⟩)
  | .swap n => .op (.Swap ⟨n⟩)
  | .bin b => b.instr
  | .un u => u.instr
  | .pop => .op .POP
  | .jump _ => .op .JUMP
  | .jumpi _ _ => .op .JUMPI
  | .load => .op .MLOAD
  | .store => .op .MSTORE
  | .dest => .op .JUMPDEST
def Op.width : Op → Nat
  | .push w _ => w.val + 1
  | _ => 1

def Op.next (o : Op) (pc : Nat) : Nat :=
  match o with
  | .jump target | .jumpi target true => target
  | _ => pc + o.width

def endPC (os : List Op) (pc : Nat) : Nat := os.foldl (fun pc o => o.next pc) pc

inductive Condition where
  | target (a : Term) (n : Nat)
  | branch (a : Term) (taken : Bool)
  deriving DecidableEq

def Condition.Holds (ρ : Nat → UInt256) (M code : ByteArray) : Condition → Prop
  | .target a n => a.eval ρ M = wd n ∧ Decode.isValidJumpDest code (a.eval ρ M).toNat = true
  | .branch a b => UInt256.isTrue (a.eval ρ M) = b

structure Config where
  stack : List Term
  mem : Mem
  deriving DecidableEq

def step (o : Op) (c : Config) : Option Config :=
  match o, c.stack with
  | .push w n, xs => some ⟨.lit (if w.val = 0 then 0 else n) :: xs, c.mem⟩
  | .dup n, xs => (xs[n.val]?).map fun v => ⟨v :: xs, c.mem⟩
  | .swap n, xs => (xs.exchange 0 (n.val + 1)).map fun ys => ⟨ys, c.mem⟩
  | .bin b, a :: v :: xs => some ⟨.bin b a v :: xs, c.mem⟩
  | .un u, a :: xs => some ⟨.un u a :: xs, c.mem⟩
  | .pop, _ :: xs => some ⟨xs, c.mem⟩
  | .jump _, _ :: xs => some ⟨xs, c.mem⟩
  | .jumpi _ _, _ :: _ :: xs => some ⟨xs, c.mem⟩
  | .load, a :: xs => some ⟨.load c.mem a :: xs, c.mem⟩
  | .store, a :: v :: xs => some ⟨xs, .store c.mem a v⟩
  | .dest, xs => some ⟨xs, c.mem⟩
  | _, _ => none

def accesses (o : Op) (c : Config) : List Term :=
  match o, c.stack with
  | .load, a :: _ | .store, a :: _ => [a]
  | _, _ => []

def conditions (o : Op) (c : Config) : List Condition :=
  match o, c.stack with
  | .jump n, a :: _ => [.target a n]
  | .jumpi n true, a :: b :: _ => [.branch b true, .target a n]
  | .jumpi _ false, _ :: b :: _ => [.branch b false]
  | _, _ => []

def stack (ρ : Nat → UInt256) (M : ByteArray) (tail : List UInt256) (xs : List Term) :=
  xs.map (Term.eval ρ M) ++ tail
def denote (ρ : Nat → UInt256) (M : ByteArray) (tail : List UInt256)
    (s : State) (pc : Nat) (c : Config) :=
  callState s pc (stack ρ M tail c.stack) (c.mem.eval ρ M)

theorem exchange_map_append {α β : Type} (f : α → β) (xs ys : List α)
    (tail : List β) (i j : Nat) (h : xs.exchange i j = some ys) :
    (xs.map f ++ tail).exchange i j = some (ys.map f ++ tail) := by
  simp only [List.exchange, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  have hi := (List.getElem?_eq_some_iff.mp ha).1
  have hj := (List.getElem?_eq_some_iff.mp hb).1
  have ea : (xs.map f ++ tail)[i]? = some (f a) := by
    simp [List.getElem?_append, hi, (List.getElem?_eq_some_iff.mp ha).2]
  have eb : (xs.map f ++ tail)[j]? = some (f b) := by
    simp [List.getElem?_append, hj, (List.getElem?_eq_some_iff.mp hb).2]
  simp [List.exchange, ea, eb, List.map_set, List.set_append_left,
    hi, hj, List.length_set]

theorem step_sound (o : Op) (c d : Config) (ρ : Nat → UInt256) (M : ByteArray)
    (tail : List UInt256) (s : State) (pc : Nat)
    (h : step o c = some d) (hlen : c.stack.length + tail.length < 1024)
    (hm : ∀ a ∈ accesses o c, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat)
    (hj : ∀ a ∈ conditions o c, a.Holds ρ M s.executionEnv.code) :
    runInstr o.instr (denote ρ M tail s pc c) =
      some (denote ρ M tail s (o.next pc) d) := by
  rcases c with ⟨xs, m⟩
  cases o with
  | jump target =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      simp only [step, Option.some.injEq] at h
      subst d
      have hj' := hj (.target a target) (by simp [conditions])
      have hc : xs.length + tail.length < 1023 := by
        simp only [List.length_cons] at hlen; omega
      simp [Op.instr, Op.next, runInstr, denote, callState, stack, hc,
        hj'.1, hj'.2]
      exact ⟨by omega, by simpa [hj'.1, wd, EvmProof.Word.word_toNat_ofNat] using hj'.2⟩
  | jumpi target taken =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      cases xs with
      | nil => simp [step] at h
      | cons b xs =>
        simp only [step, Option.some.injEq] at h
        subst d
        have hc : xs.length + tail.length < 1022 := by
          simp only [List.length_cons] at hlen; omega
        cases taken with
        | false =>
          have hb := hj (.branch b false) (by simp [conditions])
          simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, hc,
            show UInt256.isTrue (b.eval ρ M) = false from hb, EvmProof.Word.succ_ofNat_mod]
        | true =>
          have hb := hj (.branch b true) (by simp [conditions])
          have ht := hj (.target a target) (by simp [conditions])
          simp [Op.instr, Op.next, runInstr, denote, callState, stack, hc,
            show UInt256.isTrue (b.eval ρ M) = true from hb, ht.1, ht.2]
          exact ⟨by omega, by simpa [ht.1, wd, EvmProof.Word.word_toNat_ofNat] using ht.2⟩
  | push w n =>
    simp only [step, Option.some.injEq] at h
    subst d
    by_cases hw : w.val = 0 <;>
      simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, Term.eval, hw,
        hlen, EvmProof.Word.ofNat_add_mod, EvmProof.Word.succ_ofNat_mod, wd, push0_eq]
  | dup n =>
    simp only [step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    have hn : n.val < xs.length := (List.getElem?_eq_some_iff.mp hv).1
    have hv' : (stack ρ M tail xs)[n.val]? = some (v.eval ρ M) := by
      simp [stack, List.getElem?_append, hn, (List.getElem?_eq_some_iff.mp hv).2]
    simp only [stack] at hv'
    simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, hv', hlen,
      EvmProof.Word.succ_ofNat_mod]
  | swap n =>
    simp only [step, Option.map_eq_some_iff] at h
    obtain ⟨ys, hy, rfl⟩ := h
    have he := exchange_map_append (Term.eval ρ M) xs ys tail 0 (n.val + 1) hy
    simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, hlen, he,
      EvmProof.Word.succ_ofNat_mod]
  | dest =>
    simp only [step, Option.some.injEq] at h
    subst d
    simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, hlen,
      EvmProof.Word.succ_ofNat_mod]
  | pop =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      simp only [step, Option.some.injEq] at h
      subst d
      have hc : xs.length + tail.length < 1023 := by
        simp only [List.length_cons] at hlen; omega
      simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, hc,
        EvmProof.Word.succ_ofNat_mod]
  | un u =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      simp only [step, Option.some.injEq] at h
      subst d
      have hc : xs.length + tail.length < 1023 := by
        simp only [List.length_cons] at hlen; omega
      cases u <;> simp [Op.instr, Op.next, Op.width, Un.instr, runInstr, denote, callState,
        stack, Term.eval, Un.eval, hc, EvmProof.Word.succ_ofNat_mod]
  | bin b =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      cases xs with
      | nil => simp [step] at h
      | cons v xs =>
        simp only [step, Option.some.injEq] at h
        subst d
        have hc : xs.length + tail.length < 1022 := by
          simp only [List.length_cons] at hlen; omega
        cases b <;> simp [Op.instr, Op.next, Op.width, Bin.instr, runInstr, denote, callState,
          stack, Term.eval, Bin.eval, hc, EvmProof.Word.succ_ofNat_mod]
  | load =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      simp only [step, Option.some.injEq] at h
      subst d
      have hb := hm a (by simp [accesses])
      have hc : xs.length + tail.length < 1023 := by
        simp only [List.length_cons] at hlen; omega
      simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, Term.eval, hc,
        EvmProof.Word.succ_ofNat_mod, State.activeWordsAfterUInt256,
        activeWordsAfter_of_le hb, ofNat_toNat]
  | store =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      cases xs with
      | nil => simp [step] at h
      | cons v xs =>
        simp only [step, Option.some.injEq] at h
        subst d
        have hb := hm a (by simp [accesses])
        have hc : xs.length + tail.length < 1022 := by
          simp only [List.length_cons] at hlen; omega
        simp [Op.instr, Op.next, Op.width, runInstr, denote, callState, stack, Term.eval,
          Mem.eval, hc, EvmProof.Word.succ_ofNat_mod, State.activeWordsAfterUInt256,
          activeWordsAfter_of_le hb, ofNat_toNat]

structure Result where
  config : Config
  peak : Nat
  reads : List Term
  guards : List Condition
  deriving DecidableEq

def run : List Op → Config → Option Result
  | [], c => some ⟨c, 0, [], []⟩
  | o :: os, c => do
    let d ← step o c
    let r ← run os d
    pure ⟨r.config, max c.stack.length r.peak, accesses o c ++ r.reads, conditions o c ++ r.guards⟩

def Aligned {α : Type} (pcAt : α → Nat) (instrAt : α → Instr) : List α → List Op → Nat → Prop
  | [], [], _ => True
  | i :: path, o :: os, pc =>
    pc < 2 ^ 256 ∧ pcAt i = pc ∧ instrAt i = o.instr ∧
      Aligned pcAt instrAt path os (o.next pc)
  | _, _, _ => False

theorem located_sound {α : Type} (pcAt : α → Nat) (instrAt : α → Instr)
    (stepL : Option State → α → Option State)
    (hstep : ∀ i st, st.halt = .Running → st.pc.toNat = pcAt i →
      stepL (some st) i = runInstr (instrAt i) st)
    (os : List Op) (path : List α)
    (c : Config) (r : Result) (ρ : Nat → UInt256) (M : ByteArray) (tail : List UInt256)
    (s : State) (pc : Nat) (hrunning : s.halt = .Running)
    (h : run os c = some r) (hlen : r.peak + tail.length < 1024)
    (hm : ∀ a ∈ r.reads, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat)
    (hj : ∀ a ∈ r.guards, a.Holds ρ M s.executionEnv.code)
    (ha : Aligned pcAt instrAt path os pc) :
    path.foldl stepL (some (denote ρ M tail s pc c)) =
      some (denote ρ M tail s (endPC os pc) r.config) := by
  induction os generalizing path c r pc with
  | nil =>
    cases path with
    | nil =>
      simp only [run, Option.some.injEq] at h
      subst r
      simp [endPC]
    | cons i path => simp [Aligned] at ha
  | cons o os ih =>
    cases path with
    | nil => simp [Aligned] at ha
    | cons i path =>
      obtain ⟨hpc, hi, hop, ha⟩ := ha
      simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d, hd, t, ht, he⟩ := h
      cases he
      have hc : c.stack.length + tail.length < 1024 := by
        simp only at hlen; omega
      have hl : stepL (some (denote ρ M tail s pc c)) i =
          some (denote ρ M tail s (o.next pc) d) := by
        rw [hstep i (denote ρ M tail s pc c) hrunning
          (by change (UInt256.ofNat pc).toNat = pcAt i; rw [hi]; exact toNat_ofNat_of_lt hpc), hop]
        exact step_sound o c d ρ M tail s pc hd hc (fun a ha => hm a (List.mem_append_left _ ha))
          (fun a ha => hj a (List.mem_append_left _ ha))
      change path.foldl stepL
        (stepL (some (denote ρ M tail s pc c)) i) = _
      rw [hl]
      have htlen : t.peak + tail.length < 1024 := by simp only at hlen; omega
      exact ih path d t (o.next pc) ht htlen
          (fun a ha => hm a (List.mem_append_right _ ha))
          (fun a ha => hj a (List.mem_append_right _ ha)) ha

end MlDsaOptCommon.Reflect
