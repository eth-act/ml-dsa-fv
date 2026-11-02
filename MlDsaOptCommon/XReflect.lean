import MlDsaOptCommon.Reflect
import EvmProof.StepperX
/-!
# Reflective symbolic execution with EIP-8024 instructions

`Reflect`'s straight-line executor over `XInstr`: `XOp` is an `Op` or a
`DUPN` / `SWAPN` / `EXCHANGE` with its raw immediate. `xstep` uses the patched semantics'
stack positions (`DupNOp.n`, `SwapNOp.n + 1`), `xstep_sound` reduces `XOp.base`
to `Reflect.step_sound`, and `xlocated_sound` is `located_sound` for
`runXInstr`. Nothing in `Reflect` changes.
-/

namespace MlDsaOptCommon.Reflect
open EvmSemantics EvmSemantics.EVM EvmProof EvmProof.Stepper YulEvmCompiler
open MlDsaOptCommon
set_option maxRecDepth 100000

inductive XOp where
  | base (o : Op)
  | dupN (x : Fin 256)
  | swapN (x : Fin 256)
  | exchange (x : Fin 256)
  deriving DecidableEq

def XOp.instr : XOp → XInstr
  | .base o => .base o.instr
  | .dupN x => .dupN x
  | .swapN x => .swapN x
  | .exchange x => .exchange x

def XOp.next : XOp → Nat → Nat
  | .base o, pc => o.next pc
  | _, pc => pc + 2

def xendPC (os : List XOp) (pc : Nat) : Nat := os.foldl (fun pc o => o.next pc) pc

def xstep : XOp → Config → Option Config
  | .base o, c => step o c
  | .dupN x, c => (c.stack[(⟨x⟩ : Operation.DupNOp).n.val]?).map fun v => ⟨v :: c.stack, c.mem⟩
  | .swapN x, c =>
      (c.stack.exchange 0 ((⟨x⟩ : Operation.SwapNOp).n.val + 1)).map fun ys => ⟨ys, c.mem⟩
  | .exchange x, c =>
      (c.stack.exchange ((⟨x⟩ : Operation.ExchangeOp).n + 1)
        ((⟨x⟩ : Operation.ExchangeOp).m + 1)).map fun ys => ⟨ys, c.mem⟩

def xaccesses : XOp → Config → List Term
  | .base o, c => accesses o c
  | _, _ => []

def xconditions : XOp → Config → List Condition
  | .base o, c => conditions o c
  | _, _ => []

theorem xstep_sound (o : XOp) (c d : Config) (ρ : Env) (M : ByteArray)
    (tail : List UInt256) (s : State) (pc : Nat) (hdata : ρ.calldata = s.executionEnv.calldata)
    (h : xstep o c = some d) (hlen : c.stack.length + tail.length < 1024)
    (hm : ∀ a ∈ xaccesses o c, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat)
    (hj : ∀ a ∈ xconditions o c, a.Holds ρ M s.executionEnv.code) :
    runXInstr o.instr (denote ρ M tail s pc c) =
      some (denote ρ M tail s (o.next pc) d) := by
  rcases c with ⟨xs, m⟩
  cases o with
  | base o => exact step_sound o _ d ρ M tail s pc hdata h hlen hm hj
  | dupN x =>
    simp only [xstep, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    have hn := (List.getElem?_eq_some_iff.mp hv).1
    have hv' : (stack ρ M tail xs)[(⟨x⟩ : Operation.DupNOp).n.val]? = some (v.eval ρ M) := by
      simp [stack, List.getElem?_append, hn, (List.getElem?_eq_some_iff.mp hv).2]
    simp only [stack] at hv'
    simp [XOp.instr, XOp.next, runXInstr, denote, callState, stack, hv', hlen,
      EvmProof.Word.ofNat_add_mod]
  | swapN x =>
    simp only [xstep, Option.map_eq_some_iff] at h
    obtain ⟨ys, hy, rfl⟩ := h
    have he := exchange_map_append (Term.eval ρ M) xs ys tail 0 _ hy
    simp [XOp.instr, XOp.next, runXInstr, denote, callState, stack, hlen, he,
      EvmProof.Word.ofNat_add_mod]
  | exchange x =>
    simp only [xstep, Option.map_eq_some_iff] at h
    obtain ⟨ys, hy, rfl⟩ := h
    have he := exchange_map_append (Term.eval ρ M) xs ys tail _ _ hy
    simp [XOp.instr, XOp.next, runXInstr, denote, callState, stack, hlen, he,
      EvmProof.Word.ofNat_add_mod]

def xrun : List XOp → Config → Option Result
  | [], c => some ⟨c, 0, [], []⟩
  | o :: os, c => do
    let d ← xstep o c
    let r ← xrun os d
    pure ⟨r.config, max c.stack.length r.peak, xaccesses o c ++ r.reads,
      xconditions o c ++ r.guards⟩

def XAligned {α : Type} (pcAt : α → Nat) (instrAt : α → XInstr) :
    List α → List XOp → Nat → Prop
  | [], [], _ => True
  | i :: path, o :: os, pc =>
    pc < 2 ^ 256 ∧ pcAt i = pc ∧ instrAt i = o.instr ∧
      XAligned pcAt instrAt path os (o.next pc)
  | _, _, _ => False

theorem xlocated_sound {α : Type} (pcAt : α → Nat) (instrAt : α → XInstr)
    (stepL : Option State → α → Option State)
    (hstep : ∀ i st, st.halt = .Running → st.pc.toNat = pcAt i →
      stepL (some st) i = runXInstr (instrAt i) st)
    (os : List XOp) (path : List α)
    (c : Config) (r : Result) (ρ : Env) (M : ByteArray) (tail : List UInt256)
    (s : State) (pc : Nat) (hdata : ρ.calldata = s.executionEnv.calldata)
    (hrunning : s.halt = .Running)
    (h : xrun os c = some r) (hlen : r.peak + tail.length < 1024)
    (hm : ∀ a ∈ r.reads, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat)
    (hj : ∀ a ∈ r.guards, a.Holds ρ M s.executionEnv.code)
    (ha : XAligned pcAt instrAt path os pc) :
    path.foldl stepL (some (denote ρ M tail s pc c)) =
      some (denote ρ M tail s (xendPC os pc) r.config) := by
  induction os generalizing path c r pc with
  | nil =>
    cases path with
    | nil =>
      simp only [xrun, Option.some.injEq] at h
      subst r
      simp [xendPC]
    | cons i path => simp [XAligned] at ha
  | cons o os ih =>
    cases path with
    | nil => simp [XAligned] at ha
    | cons i path =>
      obtain ⟨hpc, hi, hop, ha⟩ := ha
      simp only [xrun, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d, hd, t, ht, he⟩ := h
      cases he
      have hc : c.stack.length + tail.length < 1024 := by
        simp only at hlen; omega
      have hl : stepL (some (denote ρ M tail s pc c)) i =
          some (denote ρ M tail s (o.next pc) d) := by
        rw [hstep i (denote ρ M tail s pc c) hrunning
          (by change (UInt256.ofNat pc).toNat = pcAt i; rw [hi]; exact toNat_ofNat_of_lt hpc), hop]
        exact xstep_sound o c d ρ M tail s pc hdata hd hc
          (fun a ha => hm a (List.mem_append_left _ ha))
          (fun a ha => hj a (List.mem_append_left _ ha))
      change path.foldl stepL (stepL (some (denote ρ M tail s pc c)) i) = _
      rw [hl]
      have htlen : t.peak + tail.length < 1024 := by simp only at hlen; omega
      exact ih path d t (o.next pc) ht htlen
          (fun a ha => hm a (List.mem_append_right _ ha))
          (fun a ha => hj a (List.mem_append_right _ ha)) ha

end MlDsaOptCommon.Reflect
