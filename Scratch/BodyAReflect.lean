import Scratch.BodyAData
import MlDsaOpt44.Fn.Blk.Bits
import MlDsaOpt44.Layout
namespace MemoryReflection.BodyA
open EvmSemantics EvmSemantics.EVM EvmProof.Stepper
open MlDsaOptCommon MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.Artifact MlDsaOpt44.Proofs.Blk
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def delta (k : Nat) (u x : Term) : Term :=
  let t := Term.bin .land u (.bin .xor x (.bin .shr (.lit k) x))
  .bin .xor (.bin .xor (.bin .shl (.lit k) t) t) x
def unzip (x : Term) : Term :=
  delta 6 (.var 0) (delta 30 (.var 1) (delta 126 (.var 2)
    (delta 3 (.var 3) (delta 15 (.var 4) (delta 63 (.var 5) x)))))
def addr (n : Nat) (base : Term) := if n = 0 then base else Term.bin .add (.lit n) base
def d0 := unzip (.load .initial (.var 6))
def d1 := unzip (.load .initial (addr 32 (.var 6)))
def d2 := unzip (.load .initial (addr 64 (.var 6)))
def mask (n : Nat) (x : Term) := Term.bin .land (.lit n) x
def shr (n : Nat) (x : Term) := Term.bin .shr (.lit n) x
def shl (n : Nat) (x : Term) := Term.bin .shl (.lit n) x
def candidates : List Term :=
  [mask M23 d0, mask M23 (shr 24 d0),
   .bin .lor (shl 16 (mask M7 d1)) (mask M16 (shr 48 d0)),
   mask M23 (shr 8 d1), mask M23 (shr 32 d1),
   .bin .lor (shl 8 (mask M15 d2)) (mask M8 (shr 56 d1)),
   mask M23 (shr 16 d2), mask M23 (shr 40 d2)]
def flags : Term := candidates.foldl (fun f c => .bin .lor (.bin .add (.lit CF) c) f) (.lit 0)
def memory : Mem := (candidates.zipIdx).foldl
  (fun m (c, i) => .store m (addr (32*i) (.var 8)) c) .initial
def input : Config := ⟨(List.range 9).map Term.var, .initial⟩
def output : Config := ⟨flags :: d2 :: d1 :: d0 :: input.stack, memory⟩
def bounds : List Term :=
  [.var 6, addr 32 (.var 6), addr 64 (.var 6),
   .var 8, addr 32 (.var 8), addr 64 (.var 8), addr 96 (.var 8),
   addr 128 (.var 8), addr 160 (.var 8), addr 192 (.var 8), addr 224 (.var 8)]

theorem certificate : run program input = some ⟨output, 17, bounds⟩ := by
  decide +kernel

theorem delta_eval (ρ : Nat → UInt256) (M : ByteArray) (k : Nat) (u x : Term)
    (v n : Nat) (hu : u.eval ρ M = wd v) (hx : x.eval ρ M = wd n)
    (hk : k < 256) (hn : n < 2 ^ 256) :
    (delta k u x).eval ρ M = wd (swm (2 ^ k) v n) := by
  simp only [delta, Term.eval, Bin.eval, hu, hx, wd, ofNat_shr _ hk, ofNat_shl _ hk,
    ofNat_xor, ofNat_land, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, swm, ofNat_mod]

theorem unzip_eval (v : Nat → Nat) (M : ByteArray) (x : Term) (n : Nat)
    (hx : x.eval (fun i => wd (v i)) M = wd n) (hn : n < 2 ^ 256) :
    (unzip x).eval (fun i => wd (v i)) M =
      wd (unz (v 5) (v 4) (v 3) (v 2) (v 1) (v 0) n) := by
  have h0 := delta_eval _ _ 63 (.var 5) x (v 5) n rfl hx (by decide) hn
  have h1 := delta_eval _ _ 15 (.var 4) _ (v 4) _ rfl h0 (by decide) (swm_lt _ _ _)
  have h2 := delta_eval _ _ 3 (.var 3) _ (v 3) _ rfl h1 (by decide) (swm_lt _ _ _)
  have h3 := delta_eval _ _ 126 (.var 2) _ (v 2) _ rfl h2 (by decide) (swm_lt _ _ _)
  have h4 := delta_eval _ _ 30 (.var 1) _ (v 1) _ rfl h3 (by decide) (swm_lt _ _ _)
  exact delta_eval _ _ 6 (.var 0) _ (v 0) _ rfl h4 (by decide) (swm_lt _ _ _)

def env (u5 u4 u3 u2 u1 u0 xp flp abp : Nat) : Nat → Nat
  | 0 => u5 | 1 => u4 | 2 => u3 | 3 => u2 | 4 => u1 | 5 => u0
  | 6 => xp | 7 => flp | _ => abp

theorem addr_eval (ρ : Nat → UInt256) (M : ByteArray) (base : Term)
    (n a : Nat) (h : base.eval ρ M = wd a) :
    (addr n base).eval ρ M = wd (n + a) := by
  by_cases hn : n = 0
  · simp [addr, hn, h]
  · simp [addr, hn, Term.eval, Bin.eval, h, wd, EvmProof.Word.ofNat_add_mod]

theorem d0_eval (v : Nat → Nat) (M : ByteArray) (hx : v 6 < 2 ^ 256) :
    d0.eval (fun i => wd (v i)) M =
      wd (unz (v 5) (v 4) (v 3) (v 2) (v 1) (v 0) (word M (v 6))) := by
  apply unzip_eval
  · simp [Term.eval, Mem.eval, wd, toNat_ofNat_of_lt hx, readWord_eq_word]
  · exact word_lt _ _

theorem d1_eval (v : Nat → Nat) (M : ByteArray) (hx : 32 + v 6 < 2 ^ 256) :
    d1.eval (fun i => wd (v i)) M =
      wd (unz (v 5) (v 4) (v 3) (v 2) (v 1) (v 0) (word M (32 + v 6))) := by
  apply unzip_eval
  · rw [Term.eval, addr_eval _ _ _ _ _ rfl]
    simp [Mem.eval, wd, toNat_ofNat_of_lt hx, readWord_eq_word]
  · exact word_lt _ _

theorem d2_eval (v : Nat → Nat) (M : ByteArray) (hx : 64 + v 6 < 2 ^ 256) :
    d2.eval (fun i => wd (v i)) M =
      wd (unz (v 5) (v 4) (v 3) (v 2) (v 1) (v 0) (word M (64 + v 6))) := by
  apply unzip_eval
  · rw [Term.eval, addr_eval _ _ _ _ _ rfl]
    simp [Mem.eval, wd, toNat_ofNat_of_lt hx, readWord_eq_word]
  · exact word_lt _ _

theorem candidates_eval (ρ : Nat → UInt256) (M : ByteArray) (x y z : Nat)
    (h0 : d0.eval ρ M = wd x) (h1 : d1.eval ρ M = wd y) (h2 : d2.eval ρ M = wd z)
    (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) (hz : z < 2 ^ 256) :
    candidates.map (Term.eval ρ M) =
      [wd (c0 x y z), wd (c1 x y z), wd (c2 x y z), wd (c3 x y z),
       wd (c4 x y z), wd (c5 x y z), wd (c6 x y z), wd (c7 x y z)] := by
  simp (disch := omega) only [candidates, List.map_cons, List.map_nil,
    mask, shr, shl, Term.eval, Bin.eval, h0, h1, h2, wd, ofNat_shr, ofNat_shl,
    ofNat_land, ofNat_lor, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hz,
    c0, c1, c2, c3, c4, c5, c6, c7]

theorem flags_eval (ρ : Nat → UInt256) (M : ByteArray) (x y z : Nat)
    (hc : candidates.map (Term.eval ρ M) =
      [wd (c0 x y z), wd (c1 x y z), wd (c2 x y z), wd (c3 x y z),
       wd (c4 x y z), wd (c5 x y z), wd (c6 x y z), wd (c7 x y z)]) :
    flags.eval ρ M = wd (lfv x y z) := by
  have fold (cs : List Term) (f : Term) :
      (cs.foldl (fun f c => .bin .lor (.bin .add (.lit CF) c) f) f).eval ρ M =
        (cs.map (Term.eval ρ M)).foldl
          (fun f c => UInt256.lor (wd CF + c) f) (f.eval ρ M) := by
    induction cs generalizing f with
    | nil => rfl
    | cons c cs ih => simpa [Term.eval, Bin.eval] using ih (.bin .lor (.bin .add (.lit CF) c) f)
  rw [flags, fold, hc]
  simp only [List.foldl_cons, List.foldl_nil, Term.eval, wd,
    EvmProof.Word.ofNat_add_mod, ofNat_lor, lfv]

theorem memory_eval (ρ : Nat → UInt256) (M : ByteArray) (x y z abp : Nat)
    (ha : ρ 8 = wd abp) (hb : abp + 256 < 2 ^ 256)
    (hc : candidates.map (Term.eval ρ M) =
      [wd (c0 x y z), wd (c1 x y z), wd (c2 x y z), wd (c3 x y z),
       wd (c4 x y z), wd (c5 x y z), wd (c6 x y z), wd (c7 x y z)]) :
    memory.eval ρ M = candMem M abp x y z := by
  simp only [candidates, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hc
  simp (disch := omega) only [memory, candidates, List.zipIdx, List.foldl_cons,
    List.foldl_nil, Mem.eval, addr_eval _ _ _ _ _ (show (Term.var 8).eval ρ M = wd abp from ha),
    h0,h1,h2,h3,h4,h5,h6,h7, wd, EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    candMem, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add]

theorem bodyA {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 961)
    (u5 u4 u3 u2 u1 u0 xp flp abp : Nat) (M : ByteArray) (hxp : xp + 96 ≤ 672)
    (habp : abp + 256 ≤ 32 * 2097) :
    Reach (callState s 9106 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp :: rest) M)
      (callState s 9972
        (wd (lfv (unz u0 u1 u2 u3 u4 u5 (word M xp)) (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp)))
            (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp)))) ::
          wd (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp))) ::
          wd (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp))) ::
          wd (unz u0 u1 u2 u3 u4 u5 (word M xp)) ::
          wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp :: rest)
        (candMem M abp (unz u0 u1 u2 u3 u4 u5 (word M xp)) (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp)))
            (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp))))) 1017 := by
  let v := env u5 u4 u3 u2 u1 u0 xp flp abp
  let ρ := fun i => wd (v i)
  have hsz := hs.sized
  simp only [memWords] at hsz
  have hb : ∀ a ∈ bounds, (a.eval ρ M).toNat + 32 ≤ 32 * s.activeWords.toNat := by
    intro a ha
    simp only [bounds, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [addr, Term.eval, Bin.eval, ρ, v, env, wd,
        Nat.reduceEqDiff, if_false, EvmProof.Word.ofNat_add_mod,
        EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  have h0 := d0_eval v M (by change xp < 2 ^ 256; omega)
  have h1 := d1_eval v M (by change 32 + xp < 2 ^ 256; omega)
  have h2 := d2_eval v M (by change 64 + xp < 2 ^ 256; omega)
  change d0.eval ρ M = wd (unz u0 u1 u2 u3 u4 u5 (word M xp)) at h0
  change d1.eval ρ M = wd (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp))) at h1
  change d2.eval ρ M = wd (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp))) at h2
  have hc := candidates_eval ρ M _ _ _ h0 h1 h2 (unz_lt _ _ _ _ _ _ _)
    (unz_lt _ _ _ _ _ _ _) (unz_lt _ _ _ _ _ _ _)
  have hf := flags_eval ρ M _ _ _ hc
  have hm := memory_eval ρ M _ _ _ abp rfl (by omega) hc
  have hr := located_sound program path input ⟨output, 17, bounds⟩ ρ M rest s 9106
    hs.running certificate (by dsimp; omega) hb alignment
  have hin : denote ρ M rest s 9106 input =
      callState s 9106 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp :: rest) M := rfl
  have hout : denote ρ M rest s 9972 output =
      callState s 9972
        (wd (lfv (unz u0 u1 u2 u3 u4 u5 (word M xp)) (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp)))
            (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp)))) ::
          wd (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp))) ::
          wd (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp))) ::
          wd (unz u0 u1 u2 u3 u4 u5 (word M xp)) ::
          wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp :: rest)
        (candMem M abp (unz u0 u1 u2 u3 u4 u5 (word M xp)) (unz u0 u1 u2 u3 u4 u5 (word M (32 + xp)))
            (unz u0 u1 u2 u3 u4 u5 (word M (64 + xp)))) := by
    simp only [denote, output, stack, List.map_cons, List.cons_append, hf, h0, h1, h2, hm]
    rfl
  change (locatedPath path).foldl stepL (some (denote ρ M rest s 9106 input)) =
    some (denote ρ M rest s 9972 output) at hr
  rw [hin, hout] at hr
  refine reach_block hs path (by decide +kernel) ?_
  rw [runLocatedBlock_eq_foldl _ _ (show (callState s 9106 _ M).halt = .Running from hs.running)]
  exact hr

#print axioms bodyA
end MemoryReflection.BodyA
