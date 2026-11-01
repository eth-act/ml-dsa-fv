import MlDsaOpt44.Infra.Reach

/- A deliberately small, kernel-checked reflection experiment. -/
namespace ReflectPrototype
open EvmSemantics EvmSemantics.EVM EvmProof.Stepper
open MlDsaOptCommon MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.Artifact
open YulEvmCompiler
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

inductive Bin where
  | xor | land | shl | shr
  deriving DecidableEq

def Bin.eval : Bin → UInt256 → UInt256 → UInt256
  | .xor => UInt256.xor
  | .land => UInt256.land
  | .shl => fun a b => UInt256.shiftLeft b a
  | .shr => fun a b => UInt256.shiftRight b a

def Bin.instr : Bin → Instr
  | .xor => .op .XOR
  | .land => .op .AND
  | .shl => .op .SHL
  | .shr => .op .SHR

inductive Term where
  | var (n : Nat)
  | lit (n : Nat)
  | bin (b : Bin) (a c : Term)
  deriving DecidableEq

def Term.eval (ρ : Nat → UInt256) : Term → UInt256
  | .var n => ρ n
  | .lit n => wd n
  | .bin b a c => b.eval (a.eval ρ) (c.eval ρ)

inductive Op where
  | push (n : Nat)
  | dup (n : Fin 16)
  | bin (b : Bin)
  deriving DecidableEq

def Op.instr : Op → Instr
  | .push n => .push 1 (wd n)
  | .dup n => .op (.Dup ⟨n⟩)
  | .bin b => b.instr

def Op.width : Op → Nat
  | .push _ => 2
  | _ => 1

def step : Op → List Term → Option (List Term)
  | .push n, xs => some (.lit n :: xs)
  | .dup n, xs => (xs[n.val]?).map (· :: xs)
  | .bin b, a :: c :: xs => some (.bin b a c :: xs)
  | .bin _, _ => none

def denote (ρ : Nat → UInt256) (tail : List UInt256) (xs : List Term) :=
  xs.map (Term.eval ρ) ++ tail

theorem step_sound (o : Op) (xs ys : List Term) (ρ : Nat → UInt256)
    (tail : List UInt256) (s : State) (pc : Nat) (m : ByteArray)
    (h : step o xs = some ys) (hlen : xs.length + tail.length < 1024) :
    runInstr o.instr (callState s pc (denote ρ tail xs) m) =
      some (callState s (pc + o.width) (denote ρ tail ys) m) := by
  have hc : (denote ρ tail xs).length < 1024 := by
    simpa [denote] using hlen
  cases o with
  | push n =>
    simp only [step, Option.some.injEq] at h
    subst ys
    simp [Op.instr, Op.width, runInstr, callState, hc, denote, Term.eval,
      EvmProof.Word.ofNat_add_mod, wd, hlen]
  | dup n =>
    simp only [step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    have hv' : (denote ρ tail xs)[n.val]? = some (v.eval ρ) := by
      simp only [denote, List.getElem?_append, List.length_map]
      have hn : n.val < xs.length := List.getElem?_eq_some_iff.mp hv |>.1
      simp [hn, (List.getElem?_eq_some_iff.mp hv).2]
    simp only [denote] at hv'
    simp [Op.instr, Op.width, runInstr, callState, hc, hv', denote, Term.eval,
      EvmProof.Word.succ_ofNat_mod, wd, hlen]
  | bin b =>
    cases xs with
    | nil => simp [step] at h
    | cons a xs =>
      cases xs with
      | nil => simp [step] at h
      | cons c xs =>
        simp only [step, Option.some.injEq] at h
        subst ys
        cases b <;>
          simp [Op.instr, Op.width, Bin.instr, runInstr, callState, hc,
            denote, Term.eval, Bin.eval, EvmProof.Word.succ_ofNat_mod, wd] <;>
          (simp only [List.length_cons] at hlen; omega)

def run : List Op → List Term → Option (List Term)
  | [], xs => some xs
  | o :: os, xs => (step o xs).bind (run os)

def Safe (tailLen : Nat) : List Op → List Term → Prop
  | [], _ => True
  | o :: os, xs => xs.length + tailLen < 1024 ∧
      ∀ ys, step o xs = some ys → Safe tailLen os ys

def execute : List Op → State → Option State
  | [], s => some s
  | o :: os, s => (runInstr o.instr s).bind (execute os)

theorem run_sound (os : List Op) (xs ys : List Term) (ρ : Nat → UInt256)
    (tail : List UInt256) (s : State) (pc : Nat) (m : ByteArray)
    (h : run os xs = some ys) (hs : Safe tail.length os xs) :
    execute os (callState s pc (denote ρ tail xs) m) =
      some (callState s (pc + (os.map Op.width).sum) (denote ρ tail ys) m) := by
  induction os generalizing xs pc with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst ys
    simp [execute]
  | cons o os ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨zs, hz, hr⟩ := h
    rw [execute, step_sound o xs zs ρ tail s pc m hz hs.1]
    simpa [List.map_cons, List.sum_cons, Nat.add_assoc] using
      ih zs (pc + o.width) hr (hs.2 zs hz)

-- The real BodyA delta-swap sequence, instructions 3678–3689.
def program : List Op :=
  [.dup 0, .push 63, .bin .shr, .dup 1, .bin .xor, .dup 7,
   .bin .land, .dup 0, .push 63, .bin .shl, .bin .xor, .bin .xor]

def input : List Term := (List.range 10).map Term.var
def delta (x u : Term) : Term :=
  let t := Term.bin .land u (.bin .xor x (.bin .shr (.lit 63) x))
  .bin .xor (.bin .xor (.bin .shl (.lit 63) t) t) x
def output : List Term := delta (.var 0) (.var 6) :: input.tail

theorem certificate : run program input = some output := by decide +kernel

theorem safety (tailLen : Nat) (h : tailLen ≤ 960) : Safe tailLen program input := by
  simp [Safe, program, input, step, List.range_succ]
  omega

def Aligned : List (Fin 11792) → List Op → Nat → Prop
  | [], [], _ => True
  | i :: path, o :: os, pc =>
    pc < 2 ^ 256 ∧ pcAt i.val = pc ∧ instrAt i.val = o.instr ∧
      Aligned path os (pc + o.width)
  | _, _, _ => False

theorem located_sound (os : List Op) (path : List (Fin 11792))
    (xs ys : List Term) (ρ : Nat → UInt256) (tail : List UInt256)
    (s : State) (pc : Nat) (m : ByteArray) (hrunning : s.halt = .Running)
    (h : run os xs = some ys) (hs : Safe tail.length os xs)
    (ha : Aligned path os pc) :
    (locatedPath path).foldl stepL (some (callState s pc (denote ρ tail xs) m)) =
      some (callState s (pc + (os.map Op.width).sum) (denote ρ tail ys) m) := by
  induction os generalizing path xs pc with
  | nil =>
    cases path with
    | nil =>
      simp only [run, Option.some.injEq] at h
      subst ys
      simp [locatedPath]
    | cons i path => simp [Aligned] at ha
  | cons o os ih =>
    cases path with
    | nil => simp [Aligned] at ha
    | cons i path =>
      obtain ⟨hpc, hi, hop, ha⟩ := ha
      simp only [run, Option.bind_eq_some_iff] at h
      obtain ⟨zs, hz, hr⟩ := h
      have hl : stepL (some (callState s pc (denote ρ tail xs) m)) (located i) =
          some (callState s (pc + o.width) (denote ρ tail zs) m) := by
        rw [stepL_located, hi, hop]
        change guardHalt s.halt (if (UInt256.ofNat pc).toNat = pc then _ else _) = _
        rw [hrunning, guardHalt_running, toNat_ofNat_of_lt hpc, if_pos rfl]
        exact step_sound o xs zs ρ tail s pc m hz hs.1
      change (locatedPath path).foldl stepL
        (stepL (some (callState s pc (denote ρ tail xs) m)) (located i)) = _
      rw [hl]
      simpa [List.map_cons, List.sum_cons, Nat.add_assoc] using
        ih path zs (pc + o.width) hr (hs.2 zs hz) ha

def path : List (Fin 11792) :=
  [3678, 3679, 3680, 3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689]

theorem alignment : Aligned path program 9109 := by
  simp only [path, program, Aligned, finVal_lit, instrAt_lit, pcAt_lit,
    Op.instr, Bin.instr, wd, EvmProof.Word.literal_eq_ofNat, eq_self_iff_true, true_and]
  decide +kernel

theorem reflected_block (s : State) (hs : Ctx s) (ρ : Nat → UInt256)
    (tail : List UInt256) (ht : tail.length ≤ 960) (m : ByteArray) :
    runLocatedBlock (locatedPath path) (callState s 9109 (denote ρ tail input) m) =
      some (callState s 9123 (denote ρ tail output) m) := by
  rw [runLocatedBlock_eq_foldl _ _ (show (callState s 9109 (denote ρ tail input) m).halt =
    .Running from hs.running)]
  exact located_sound program path input output ρ tail s 9109 m hs.running
    certificate (safety tail.length ht) alignment

#print axioms run_sound
#print axioms certificate
#print axioms reflected_block
end ReflectPrototype
