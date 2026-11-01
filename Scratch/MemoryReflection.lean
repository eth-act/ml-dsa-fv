import MlDsaOpt44.Infra.Reach
namespace MemoryReflection
open EvmSemantics EvmSemantics.EVM EvmProof.Stepper YulEvmCompiler
open MlDsaOptCommon MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.Artifact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

inductive Bin where
  | add | xor | land | lor | shl | shr
  deriving DecidableEq
def Bin.eval : Bin → UInt256 → UInt256 → UInt256
  | .add => (· + ·)
  | .xor => UInt256.xor
  | .land => UInt256.land
  | .lor => UInt256.lor
  | .shl => fun a b => UInt256.shiftLeft b a
  | .shr => fun a b => UInt256.shiftRight b a
def Bin.instr : Bin → Instr
  | .add => .op .ADD
  | .xor => .op .XOR
  | .land => .op .AND
  | .lor => .op .OR
  | .shl => .op .SHL
  | .shr => .op .SHR

mutual
inductive Term where
  | var (n : Nat)
  | lit (n : Nat)
  | bin (b : Bin) (a c : Term)
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
  | .load m a => MachineState.readWord (m.eval ρ M) (a.eval ρ M).toNat
def Mem.eval (ρ : Nat → UInt256) (M : ByteArray) : Mem → ByteArray
  | .initial => M
  | .store m a v => MachineState.writeBytes (m.eval ρ M)
      (Data.Bytes.natToBytesPadded (v.eval ρ M).toNat 32) (a.eval ρ M).toNat
end

inductive Op where
  | push (w : Fin 33) (n : Nat)
  | dup (n : Fin 16)
  | bin (b : Bin)
  | load | store | dest
  deriving DecidableEq
def Op.instr : Op → Instr
  | .push w n => .push w (wd n)
  | .dup n => .op (.Dup ⟨n⟩)
  | .bin b => b.instr
  | .load => .op .MLOAD
  | .store => .op .MSTORE
  | .dest => .op .JUMPDEST
def Op.width : Op → Nat
  | .push w _ => w.val + 1
  | _ => 1

structure Config where
  stack : List Term
  mem : Mem
  deriving DecidableEq

def step (o : Op) (c : Config) : Option Config :=
  match o, c.stack with
  | .push w n, xs => some ⟨.lit (if w.val = 0 then 0 else n) :: xs, c.mem⟩
  | .dup n, xs => (xs[n.val]?).map fun v => ⟨v :: xs, c.mem⟩
  | .bin b, a :: v :: xs => some ⟨.bin b a v :: xs, c.mem⟩
  | .load, a :: xs => some ⟨.load c.mem a :: xs, c.mem⟩
  | .store, a :: v :: xs => some ⟨xs, .store c.mem a v⟩
  | .dest, xs => some ⟨xs, c.mem⟩
  | _, _ => none

def accesses (o : Op) (c : Config) : List Term :=
  match o, c.stack with
  | .load, a :: _ | .store, a :: _ => [a]
  | _, _ => []

def stack (ρ : Nat → UInt256) (M : ByteArray) (tail : List UInt256) (xs : List Term) :=
  xs.map (Term.eval ρ M) ++ tail
def denote (ρ : Nat → UInt256) (M : ByteArray) (tail : List UInt256)
    (s : State) (pc : Nat) (c : Config) :=
  callState s pc (stack ρ M tail c.stack) (c.mem.eval ρ M)

theorem step_sound (o : Op) (c d : Config) (ρ : Nat → UInt256) (M : ByteArray)
    (tail : List UInt256) (s : State) (pc : Nat)
    (h : step o c = some d) (hlen : c.stack.length + tail.length < 1024)
    (hm : ∀ a ∈ accesses o c, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat) :
    runInstr o.instr (denote ρ M tail s pc c) =
      some (denote ρ M tail s (pc + o.width) d) := by
  rcases c with ⟨xs, m⟩
  cases o with
  | push w n =>
    simp only [step, Option.some.injEq] at h
    subst d
    by_cases hw : w.val = 0 <;>
      simp [Op.instr, Op.width, runInstr, denote, callState, stack, Term.eval, hw,
        hlen, EvmProof.Word.ofNat_add_mod, EvmProof.Word.succ_ofNat_mod, wd, push0_eq]
  | dup n =>
    simp only [step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    have hn : n.val < xs.length := (List.getElem?_eq_some_iff.mp hv).1
    have hv' : (stack ρ M tail xs)[n.val]? = some (v.eval ρ M) := by
      simp [stack, List.getElem?_append, hn, (List.getElem?_eq_some_iff.mp hv).2]
    simp only [stack] at hv'
    simp [Op.instr, Op.width, runInstr, denote, callState, stack, hv', hlen,
      EvmProof.Word.succ_ofNat_mod]
  | dest =>
    simp only [step, Option.some.injEq] at h
    subst d
    simp [Op.instr, Op.width, runInstr, denote, callState, stack, hlen,
      EvmProof.Word.succ_ofNat_mod]
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
        cases b <;> simp [Op.instr, Op.width, Bin.instr, runInstr, denote, callState,
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
      simp [Op.instr, Op.width, runInstr, denote, callState, stack, Term.eval, hc,
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
        simp [Op.instr, Op.width, runInstr, denote, callState, stack, Term.eval,
          Mem.eval, hc, EvmProof.Word.succ_ofNat_mod, State.activeWordsAfterUInt256,
          activeWordsAfter_of_le hb, ofNat_toNat]

structure Result where
  config : Config
  peak : Nat
  reads : List Term
  deriving DecidableEq

def run : List Op → Config → Option Result
  | [], c => some ⟨c, 0, []⟩
  | o :: os, c => do
    let d ← step o c
    let r ← run os d
    pure ⟨r.config, max c.stack.length r.peak, accesses o c ++ r.reads⟩

def Aligned : List (Fin 11792) → List Op → Nat → Prop
  | [], [], _ => True
  | i :: path, o :: os, pc =>
    pc < 2 ^ 256 ∧ pcAt i.val = pc ∧ instrAt i.val = o.instr ∧
      Aligned path os (pc + o.width)
  | _, _, _ => False

theorem located_sound (os : List Op) (path : List (Fin 11792))
    (c : Config) (r : Result) (ρ : Nat → UInt256) (M : ByteArray) (tail : List UInt256)
    (s : State) (pc : Nat) (hrunning : s.halt = .Running)
    (h : run os c = some r) (hlen : r.peak + tail.length < 1024)
    (hm : ∀ a ∈ r.reads, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat)
    (ha : Aligned path os pc) :
    (locatedPath path).foldl stepL (some (denote ρ M tail s pc c)) =
      some (denote ρ M tail s (pc + (os.map Op.width).sum) r.config) := by
  induction os generalizing path c r pc with
  | nil =>
    cases path with
    | nil =>
      simp only [run, Option.some.injEq] at h
      subst r
      simp [locatedPath]
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
      have hl : stepL (some (denote ρ M tail s pc c)) (located i) =
          some (denote ρ M tail s (pc + o.width) d) := by
        rw [stepL_located, hi, hop]
        change guardHalt s.halt (if (UInt256.ofNat pc).toNat = pc then _ else _) = _
        rw [hrunning, guardHalt_running, toNat_ofNat_of_lt hpc, if_pos rfl]
        exact step_sound o c d ρ M tail s pc hd hc (fun a ha => hm a (List.mem_append_left _ ha))
      change (locatedPath path).foldl stepL
        (stepL (some (denote ρ M tail s pc c)) (located i)) = _
      rw [hl]
      have htlen : t.peak + tail.length < 1024 := by simp only at hlen; omega
      simpa [List.map_cons, List.sum_cons, Nat.add_assoc] using
        ih path d t (pc + o.width) ht htlen
          (fun a ha => hm a (List.mem_append_right _ ha)) ha

#print axioms located_sound
end MemoryReflection
