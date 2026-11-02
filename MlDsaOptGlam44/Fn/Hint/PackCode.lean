import MlDsaOptGlam44.Fn.Hint.PackIter
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Hint/PackCode.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# `pack` (WP10): the stored words, bit by bit

`Xl V j` is lane `j` of a word; the code stores `rep (Xl V_k j)` for the
three stream words `V_k` of a chunk. `Aw M wp n r` is lane `r` of the `n`-th
coefficient word of the chunk at `wp`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOptGlam44.Proofs.PK

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.L10

/-- Lane `j` of a word. -/
def Xl (V : UInt256) (j : Nat) : Nat := (V.toNat >>> (64 * j)) % 2 ^ 64

/-- Lane `r` of coefficient word `n` of the chunk at `wp`. -/
def Aw (M : ByteArray) (wp n r : Nat) : Nat := lane (word M (32 * n + wp)) r

theorem u_toNat_lt (V : UInt256) : V.toNat < 2 ^ 256 := V.val.isLt

theorem rep_toNat {X : Nat} (hX : X < 2 ^ 64) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 * UInt256.ofNat X).toNat =
      rep X := by
  have e : REP = 6277101735386680764176071790128604879584176795969512275969 := by
    unfold REP pack4; norm_num
  rw [ofNat_mul, toNat_ofNat_of_lt (by omega), rep, e, Nat.mul_comm]

theorem st_lane (V : UInt256) {k j : Nat} (hk : k = 64 * j) (hk' : k < 256) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 *
      (UInt256.ofNat 18446744073709551615).land (V.shiftRight (UInt256.ofNat k))).toNat = rep (Xl V j) := by
  rw [← ofNat_toNat V, ofNat_shr _ hk', Nat.mod_eq_of_lt (u_toNat_lt V), ofNat_land,
    show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    rep_toNat (Nat.mod_lt _ (by positivity)), Xl, toNat_ofNat_of_lt (u_toNat_lt V), hk]

theorem st_lane0 (V : UInt256) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 *
      (UInt256.ofNat 18446744073709551615).land V).toNat = rep (Xl V 0) := by
  rw [← ofNat_toNat V, ofNat_land, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, rep_toNat (Nat.mod_lt _ (by positivity)), Xl,
    toNat_ofNat_of_lt (u_toNat_lt V)]
  simp

theorem st_lane3 (V : UInt256) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 *
      V.shiftRight (UInt256.ofNat 192)).toNat = rep (Xl V 3) := by
  have h := u_toNat_lt V
  have hs : V.toNat >>> 192 < 2 ^ 64 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [← ofNat_toNat V, ofNat_shr _ (by norm_num), Nat.mod_eq_of_lt h, rep_toNat hs, Xl,
    toNat_ofNat_of_lt h, Nat.mod_eq_of_lt hs]

theorem tb_word (M : ByteArray) (wp : Nat) {c : Nat} (q : Nat) (hc : c % 32 = 0) :
    (word M (c + wp)).testBit q = (decide (q < 256) && (Aw M wp (c / 32) (q / 64)).testBit (q % 64)) := by
  have e : 32 * (c / 32) + wp = c + wp := by omega
  unfold Aw; rw [e, ← testBit_pk (lanes_lane _), pk_lanes (word_lt _ _)]

theorem tb_word0 (M : ByteArray) (wp q : Nat) :
    (word M wp).testBit q = (decide (q < 256) && (Aw M wp 0 (q / 64)).testBit (q % 64)) := by
  have := tb_word M wp q (c := 0) (by norm_num)
  simpa using this

theorem tb_hi {a e : Nat} (ha : a < 64) (he : 6 ≤ e) : a.testBit e = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he))

/-! ## Bit reflection

`v0_bits`–`v2_bits` state where each bit of a stored stream word comes from.
The stream words are built by `lor`, `land` and shifts by literals from the
coefficient words, so their bits are computed symbolically: `PE` is that
expression language, `PE.sbit e q` the source of bit `q` of `e` (a constant,
or bits of coefficient lanes), and `PE.sbit_sound` relates it to the value.
One `decide` then checks all 256 bits of a stream word at once, instead of a
`simp` over the whole word per bit. -/

/-- Word expressions of the `pack` code: `atom a` is coefficient word `a % 32`
of memory `a / 32`. -/
inductive PE where
  | atom (a : Nat)
  | lit (v : Nat)
  | or (x y : PE)
  | and (x y : PE)
  | shl (x : PE) (k : Nat)
  | shr (x : PE) (k : Nat)

/-- Spellings matching the `UInt256` operations of the block definitions. -/
def PE.lor (x y : PE) : PE := .or x y
def PE.land (x y : PE) : PE := .and x y
def PE.shiftLeft (x : PE) : PE → PE
  | .lit k => .shl x k
  | _ => .lit 0
def PE.shiftRight (x : PE) : PE → PE
  | .lit k => .shr x k
  | _ => .lit 0

/-- Byte offset of coefficient word `n` of the chunk at `wp`. -/
def coff (wp : Nat) : Nat → Nat
  | 0 => wp
  | n + 1 => 32 * (n + 1) + wp

/-- Atom values: word `a % 32` of memory `ms (a / 32)`. -/
def penv (ms : Nat → ByteArray) (wp a : Nat) : UInt256 :=
  UInt256.ofNat (word (ms (a / 32)) (coff wp (a % 32)))

def PE.eval (env : Nat → UInt256) : PE → UInt256
  | .atom a => env a
  | .lit v => UInt256.ofNat v
  | .or x y => (x.eval env).lor (y.eval env)
  | .and x y => (x.eval env).land (y.eval env)
  | .shl x k => (x.eval env).shiftLeft (UInt256.ofNat k)
  | .shr x k => (x.eval env).shiftRight (UInt256.ofNat k)

/-- A symbolic bit: `some (c, l)` is `c` or any of the lane bits `(n, r, e)` in
`l` (bit `e` of lane `r` of coefficient word `n`); `none` is unknown. -/
abbrev SB := Option (Bool × List (Nat × Nat × Nat))

def SB.or : SB → SB → SB
  | some (c, l), some (d, m) => some (c || d, l ++ m)
  | _, _ => none

def SB.and : SB → SB → SB
  | some (false, []), _ => some (false, [])
  | _, some (false, []) => some (false, [])
  | some (true, []), y => y
  | x, some (true, []) => x
  | _, _ => none

theorem SB.and_cases {u v : SB} {r : Bool × List (Nat × Nat × Nat)} (h : u.and v = some r) :
    (u = some (false, []) ∧ r = (false, [])) ∨ (v = some (false, []) ∧ r = (false, [])) ∨
      (u = some (true, []) ∧ v = some r) ∨ (v = some (true, []) ∧ u = some r) := by
  rcases u with _ | ⟨_ | _, _ | _⟩ <;> rcases v with _ | ⟨_ | _, _ | _⟩ <;>
    simp only [SB.and, reduceCtorEq, Option.some.injEq] at h <;> subst_vars <;> simp

/-- Bit `q` of `e`, symbolically (lanes hold 6-bit values). -/
def PE.sbit : PE → Nat → SB
  | .atom a, q => if q < 256 ∧ q % 64 < 6 then some (false, [(a % 32, q / 64, q % 64)])
      else some (false, [])
  | .lit v, q => some ((v % 2 ^ 256).testBit q, [])
  | .or x y, q => (x.sbit q).or (y.sbit q)
  | .and x y, q => (x.sbit q).and (y.sbit q)
  | .shl x k, q => if k < 256 then (if q < 256 ∧ k ≤ q then x.sbit (q - k) else some (false, []))
      else none
  | .shr x k, q => if k < 256 then x.sbit (k + q) else none

/-- Value of a symbolic bit, with lane values `A n r`. -/
def SB.denote (A : Nat → Nat → Nat) : Bool × List (Nat × Nat × Nat) → Bool
  | (c, l) => c || l.any fun t => (A t.1 t.2.1).testBit t.2.2

theorem PE.sbit_sound (A : Nat → Nat → Nat) (env : Nat → UInt256)
    (hA : ∀ n r e, n < 32 → r < 4 → 6 ≤ e → (A n r).testBit e = false)
    (henv : ∀ a q, (env a).toNat.testBit q = (decide (q < 256) && (A (a % 32) (q / 64)).testBit (q % 64))) :
    ∀ (e : PE) (q : Nat) (r : Bool × List (Nat × Nat × Nat)), e.sbit q = some r →
      (e.eval env).toNat.testBit q = SB.denote A r := by
  intro e
  induction e with
  | atom a =>
    intro q r h
    simp only [PE.sbit] at h
    rw [PE.eval, henv]
    split at h
    · cases h; simp [SB.denote, *]
    · cases h
      by_cases hq : q < 256
      · have : 6 ≤ q % 64 := by omega
        simp [SB.denote, hq, hA (a % 32) (q / 64) (q % 64) (Nat.mod_lt _ (by omega)) (by omega) this]
      · simp [SB.denote, hq]
  | lit v =>
    intro q r h
    simp only [PE.sbit, Option.some.injEq] at h
    subst h
    simp [PE.eval, SB.denote, EvmProof.Word.word_toNat_ofNat]
  | or x y ihx ihy =>
    intro q r h
    simp only [PE.sbit] at h
    rcases hx : x.sbit q with _ | ⟨c, l⟩ <;> rcases hy : y.sbit q with _ | ⟨d, m⟩ <;>
      simp only [hx, hy, SB.or, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [PE.eval, EvmProof.Word.word_toNat_lor, Nat.testBit_or, ihx q _ hx, ihy q _ hy]
    simp only [SB.denote, List.any_append]
    cases c <;> cases d <;> simp
  | and x y ihx ihy =>
    intro q r h
    simp only [PE.sbit] at h
    rw [PE.eval, EvmProof.Word.word_toNat_land, Nat.testBit_and]
    rcases SB.and_cases h with ⟨hx, rfl⟩ | ⟨hy, rfl⟩ | ⟨hx, hy⟩ | ⟨hy, hx⟩
    · rw [ihx q _ hx]; simp [SB.denote]
    · rw [ihy q _ hy]; simp [SB.denote]
    · rw [ihx q _ hx, ihy q _ hy]; simp [SB.denote]
    · rw [ihx q _ hx, ihy q _ hy]; simp [SB.denote]
  | shl x k ih =>
    intro q r h
    simp only [PE.sbit] at h
    split at h
    · rename_i hk
      rw [PE.eval, EvmProof.Word.shiftLeft_toNat _ hk, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
      split at h
      · rename_i hq
        rw [ih _ _ h]; simp [hq]
      · cases h
        rename_i hq
        by_cases h1 : q < 256 <;> simp [SB.denote, h1]; omega
    · cases h
  | shr x k ih =>
    intro q r h
    simp only [PE.sbit] at h
    split at h
    · rename_i hk
      rw [PE.eval, EvmProof.Word.shiftRight_toNat _ hk, Nat.testBit_shiftRight, ih _ _ h]
    · cases h

/-- Coefficient-word bits through `penv`, given that all memories `ms i` hold
the same coefficient lanes as `M`. -/
theorem penv_bit (M : ByteArray) (wp : Nat) (ms : Nat → ByteArray)
    (hms : ∀ i n r, n < 32 → Aw (ms i) wp n r = Aw M wp n r) (a q : Nat) :
    (penv ms wp a).toNat.testBit q =
      (decide (q < 256) && (Aw M wp (a % 32) (q / 64)).testBit (q % 64)) := by
  have hlt : a % 32 < 32 := Nat.mod_lt _ (by omega)
  rw [penv, toNat_ofNat_of_lt (word_lt _ _)]
  rcases h : a % 32 with _ | n
  · rw [coff, tb_word0, hms _ _ _ (by omega)]
  · rw [coff, tb_word (ms (a / 32)) wp q (by omega), Nat.mul_div_cancel_left _ (by omega),
      hms _ _ _ (by omega)]

/-- All positions of a stream word: bit `b` of lane `j` is `src j b`. -/
def PE.check (e : PE) (src : Nat → Nat → Nat × Nat × Nat) : Bool :=
  (List.range 4).all fun j => (List.range 64).all fun b =>
    e.sbit (64 * j + b) == some (false, [src j b])

theorem PE.bit_of_check (M : ByteArray) (wp : Nat) (ms : Nat → ByteArray)
    (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    (hms : ∀ i n r, n < 32 → Aw (ms i) wp n r = Aw M wp n r)
    (e : PE) (src : Nat → Nat → Nat × Nat × Nat) (hc : e.check src = true)
    {j b : Nat} (hj : j < 4) (hb : b < 64) :
    ((e.eval (penv ms wp)).toNat >>> (64 * j) % 2 ^ 64).testBit b =
      (Aw M wp (src j b).1 (src j b).2.1).testBit (src j b).2.2 := by
  simp only [PE.check, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    PE.sbit_sound (Aw M wp) _ (fun n r e hn hr he => tb_hi (hA n r hn hr) he) (penv_bit M wp ms hms)
      _ _ _ (hc j hj b hb)]
  simp [SB.denote, hb]

/-! ### The stream words as `PE` expressions

Mirrors of `pkNoK` (`PackBlocks`) and `qNoK` (`PackIter`): the same text with
`UInt256.ofNat (word M (32 n + wp))` replaced by `PE.atom (b + n)` and the
literals by `PE.lit`, where `b` is `32 i` for memory `i` (`M`, `qm2`, `qm4`).
`PE.eval` of each is the `UInt256` definition by `rfl`. -/

def ek1o0 (b : Nat) : PE :=
  (PE.atom (b + 10))

def ek1o1 (b : Nat) : PE :=
  (((PE.atom (b + 9)).shiftLeft (PE.lit 54)).lor (((PE.atom (b + 8)).shiftLeft (PE.lit 48)).lor (((PE.atom (b + 7)).shiftLeft (PE.lit 42)).lor (((PE.atom (b + 6)).shiftLeft (PE.lit 36)).lor (((PE.atom (b + 5)).shiftLeft (PE.lit 30)).lor (((PE.atom (b + 4)).shiftLeft (PE.lit 24)).lor (((PE.atom (b + 3)).shiftLeft (PE.lit 18)).lor (((PE.atom (b + 2)).shiftLeft (PE.lit 12)).lor (((PE.atom (b + 1)).shiftLeft (PE.lit 6)).lor ((PE.atom b).lor (PE.lit 0)))))))))))

def ek2o0 (b : Nat) (x0 x1 : PE) : PE :=
  (x1.lor ((PE.lit 108555083659983933215482581322569926828855677927283595861601650753639976796160).land (x0.shiftLeft (PE.lit 60))))

def ek2o1 (b : Nat) (x0 x1 : PE) : PE :=
  x0

def ek3o0 (b : Nat) (x0 x1 : PE) : PE :=
  (PE.atom (b + 21))

def ek3o1 (b : Nat) (x0 x1 : PE) : PE :=
  (((PE.atom (b + 20)).shiftLeft (PE.lit 56)).lor (((PE.atom (b + 19)).shiftLeft (PE.lit 50)).lor (((PE.atom (b + 18)).shiftLeft (PE.lit 44)).lor (((PE.atom (b + 17)).shiftLeft (PE.lit 38)).lor (((PE.atom (b + 16)).shiftLeft (PE.lit 32)).lor (((PE.atom (b + 15)).shiftLeft (PE.lit 26)).lor (((PE.atom (b + 14)).shiftLeft (PE.lit 20)).lor (((PE.atom (b + 13)).shiftLeft (PE.lit 14)).lor (((PE.atom (b + 12)).shiftLeft (PE.lit 8)).lor (((PE.atom (b + 11)).shiftLeft (PE.lit 2)).lor ((PE.lit 18831305206160042292528215370385814638752530387908536827907).land (x1.shiftRight (PE.lit 4)))))))))))))

def ek4o0 (b : Nat) (x0 x1 : PE) : PE :=
  (x1.lor ((PE.lit 86844066927987146572386065058055941463084542341826876689281320602911981436928).land (x0.shiftLeft (PE.lit 62))))

def ek4o1 (b : Nat) (x0 x1 : PE) : PE :=
  x0

def ek5o0 (b : Nat) (x0 x1 : PE) : PE :=
  (((PE.atom (b + 31)).shiftLeft (PE.lit 58)).lor (((PE.atom (b + 30)).shiftLeft (PE.lit 52)).lor (((PE.atom (b + 29)).shiftLeft (PE.lit 46)).lor (((PE.atom (b + 28)).shiftLeft (PE.lit 40)).lor (((PE.atom (b + 27)).shiftLeft (PE.lit 34)).lor (((PE.atom (b + 26)).shiftLeft (PE.lit 28)).lor (((PE.atom (b + 25)).shiftLeft (PE.lit 22)).lor (((PE.atom (b + 24)).shiftLeft (PE.lit 16)).lor (((PE.atom (b + 23)).shiftLeft (PE.lit 10)).lor (((PE.atom (b + 22)).shiftLeft (PE.lit 4)).lor ((PE.lit 94156526030800211462641076851929073193762651939542684139535).land (x1.shiftRight (PE.lit 2)))))))))))))

def eq1o0 : PE := ek1o0 0

def eq1o1 : PE := ek1o1 0

def eq2o0 : PE := ek2o0 0 eq1o0 eq1o1

def eq2o1 : PE := ek2o1 0 eq1o0 eq1o1

def eq3o0 : PE := ek3o0 32 eq2o0 eq2o1

def eq3o1 : PE := ek3o1 32 eq2o0 eq2o1

def eq4o0 : PE := ek4o0 32 eq3o0 eq3o1

def eq4o1 : PE := ek4o1 32 eq3o0 eq3o1

def eq5o0 : PE := ek5o0 64 eq4o0 eq4o1

/-- Which coefficient bit each bit of the three stream words is. -/
theorem check_v0 : eq2o0.check (fun j b => (b / 6, j, b % 6)) = true := by decide +kernel
theorem check_v1 : eq4o0.check (fun j b => ((64 + b) / 6, j, (64 + b) % 6)) = true := by decide +kernel
theorem check_v2 : eq5o0.check (fun j b => ((128 + b) / 6, j, (128 + b) % 6)) = true := by
  decide +kernel

/-- Stream word 0 of a chunk. -/
theorem v0_bits (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    {j : Nat} (hj : j < 4) {b : Nat} (hb : b < 64) :
    (Xl (q2o0 M wp fp) j).testBit b = (Aw M wp (b / 6) j).testBit (b % 6) :=
  PE.bit_of_check M wp (fun _ => M) hA (fun _ _ _ _ => rfl) eq2o0 _ check_v0 hj hb

/-- Stream word 1 of a chunk. -/
theorem v1_bits (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    (hq2 : ∀ n r, n < 32 → Aw (qm2 M wp fp) wp n r = Aw M wp n r)
    {j : Nat} (hj : j < 4) {b : Nat} (hb : b < 64) :
    (Xl (q4o0 M wp fp) j).testBit b = (Aw M wp ((64 + b) / 6) j).testBit ((64 + b) % 6) :=
  PE.bit_of_check M wp (fun i => match i with | 0 => M | _ => qm2 M wp fp) hA
    (fun i n r hn => by rcases i with _ | _ <;> simp [hq2 n r hn]) eq4o0 _ check_v1 hj hb

/-- Stream word 2 of a chunk. -/
theorem v2_bits (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    (hq2 : ∀ n r, n < 32 → Aw (qm2 M wp fp) wp n r = Aw M wp n r)
    (hq4 : ∀ n r, n < 32 → Aw (qm4 M wp fp) wp n r = Aw M wp n r)
    {j : Nat} (hj : j < 4) {b : Nat} (hb : b < 64) :
    (Xl (q5o0 M wp fp) j).testBit b = (Aw M wp ((128 + b) / 6) j).testBit ((128 + b) % 6) :=
  PE.bit_of_check M wp (fun i => match i with | 0 => M | 1 => qm2 M wp fp | _ => qm4 M wp fp) hA
    (fun i n r hn => by rcases i with _ | _ | _ <;> simp [hq2 n r hn, hq4 n r hn]) eq5o0 _ check_v2 hj hb

end MlDsaOptGlam44.Proofs.PK
