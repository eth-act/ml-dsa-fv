import MlDsaOpt44.Fn.Group
import MlDsaOpt44.Fn.Ntt
import MlDsaOpt44.Fn.Decode
import MlDsaOpt44.Fn.Ct
import MlDsaOpt44.Fn.Hint
set_option warningAsError true
/-!
# Main-flow invariants

The main flow (regions `main`, `expand_a`, `hash_mu`, `final_hash` of
`MlDsaOpt/44/layout.txt`) is cut into segments at fixed program counters.
`InvK cd m` is what memory holds at boundary `K` for calldata `cd`. Facts
about data that may be invalid (hints, `c`, `A`) are conditional on the
corresponding validity flag; everything needed for termination and gas is
unconditional.

| boundary | pc | stack | invariant |
|---|---|---|---|
| sized, tables | 992 | `[]` | `Inv0` |
| z, hints | 1085 | `[ok1]` | `Inv1` |
| NTT records | 3068 | `[ok1]` | `Inv2` |
| ẑ | 3078 | `[ok1]` | `Inv3` |
| ρ spread | 3439 | `[ok1]` | `Inv4` |
| group 0 | 3452 | `[ok1 ∧ A·0]` | `InvG cd m 1` |
| group 1 | 3466 | `[ok1 ∧ A·0 ∧ A·1]` | `InvG cd m 2` |
| Â ẑ, tr, c̃ stream, μ | 4648 | `[ok2]` | `Inv5` |
| μ | 5926 | `[ok2]` | `Inv6` |
| c | 5936 | `[ok3]` | `Inv7` |
| c · t1 | 5963 | `[ok3]` | `Inv8` |
| w1Encode | 6001 | `[ok3]` | `Inv9` |

with `ok1 = okZ ∧ okH`, `ok2 = ok1 ∧ okA`, `ok3 = ok2 ∧ okC`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

def ok1 (cd : ByteArray) : Bool := okZ cd && okH cd
def ok2 (cd : ByteArray) : Bool := ok1 cd && okA cd
def ok3 (cd : ByteArray) : Bool := ok2 cd && okC cd

/-- Column `s` of `A` exists for every row. -/
def okCol (cd : ByteArray) (s : Nat) : Bool := (List.range 4).all fun r => (aOf cd r s).isSome

/-- `HP` holds bit lanes, and the decoded hint when there is one. -/
def HPAt (m : ByteArray) (cd : ByteArray) : Prop :=
  (∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧ word m (HP + 32 * t) = pack4 b) ∧
  (∀ h, hintOf cd = some h → ∀ t, t < 256 → ∀ r, r < 4 → lane (word m (HP + 32 * t)) r = (h[r]![t]!).toNat)

/-- `ZH` holds the decoded `z` lanes. -/
def ZAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ t, t < 256 → word m (ZH + 32 * t) = pack4 fun k => zLane cd k t

/-- `ZH` holds `ẑ` (bounded representatives mod q). -/
def ZHatAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ZH + 32 * t)) k < 2 ^ 28 ∧
    ((lane (word m (ZH + 32 * t)) k : Int) - (zHat cd k)[t]!) % (Fips204.q : Int) = 0

/-- Columns `0 … n − 1` of `A` exist for every row. -/
def okUpTo (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okUpTo cd n && okCol cd n

/-- Lane `r` of `ACC[t]` after columns `0 … n − 1`: `Σ_s A[r][s][t] · lane s of ZH[t]`
(explicit recursion, no `List.sum`: see the pitfalls in `PLAN.md`). -/
def accSum (cd m : ByteArray) (r t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => accSum cd m r t n + ((aD cd r n)[t]!).toNat * lane (word m (ZH + 32 * t)) n

/-- `ACC` after the columns `s < n` of `Â ẑ` (exact lane sums, valid columns). -/
def AccCols (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  okUpTo cd n = true → ∀ t, t < 256 → word m (ACC + 32 * t) = pack4 fun r => accSum cd m r t n

/-- `ACC` holds `Â ẑ` (bounded representatives mod q) when `A` exists. -/
def AccAt (m : ByteArray) (cd : ByteArray) : Prop :=
  okA cd = true → ∀ r, r < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) r < 2 ^ 58 ∧
    ((lane (word m (ACC + 32 * t)) r : Int) - (azRow cd r)[t]!) % (Fips204.q : Int) = 0

/-- The 104 replicated stream lanes of the final hash input in `FIN`. -/
def FinAt (m : ByteArray) (X : ByteArray) : Prop :=
  ∀ x, x < 104 → word m (FIN + 32 * x) = rep (le64 X (8 * x))

/-- μ's lanes, replicated, in `FIN[0, 8)`. -/
def FinMu (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 8 → word m (FIN + 32 * x) = rep (le64 (muOf cd) (8 * x))

structure Inv0 (m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  zero : ZeroOn m MISC TOP

structure Inv1 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  z : ZAt m cd
  hp : HPAt m cd
  zLow : ZeroOn m MISC ZH
  zHigh : ZeroOn m BASES HP

structure Inv2 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  z : ZAt m cd
  hp : HPAt m cd
  zMisc : ZeroOn m MISC TBL
  zCw : ZeroOn m CW ABUF
  zHigh : ZeroOn m BASES HP

structure Inv3 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  hp : HPAt m cd
  zMisc : ZeroOn m MISC TBL
  zCw : ZeroOn m CW ABUF
  zHigh : ZeroOn m BASES HP

structure Inv4 (cd m : ByteArray) : Prop extends Inv3 cd m where
  rho : Rho1At m cd

/-- Between the ExpandA groups: `n` columns accumulated. -/
structure InvG (cd m : ByteArray) (n : Nat) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  hp : HPAt m cd
  rho : Rho1At m cd
  acc : AccCols m cd n
  zMisc : ZeroOn m MISC (MISC + 0x1e0)
  zCw : ZeroOn m CW ABUF
  zIdx : ZeroOn m IDX ACC

structure Inv5 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  trl : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf cd) (8 * x)
  mu : mlenOf cd ≤ 69 → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)
  cb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)
  fresh : SibFresh m

structure Inv6 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  cb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)
  fresh : SibFresh m
  fmu : FinMu m cd

structure Inv7 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  fmu : FinMu m cd
  crep : okC cd = true → CRep m (cD cd)

structure Inv8 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  fmu : FinMu m cd
  sp : okC cd = true → ∀ t, t < 256 → word m (SP + 32 * t) =
    pack4 fun r => 2 ^ 13 * sPrime (cD cd) cd r t + nNeg (cD cd) t

structure Inv9 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  fin : ok3 cd = true → FinAt m (finBytes cd)

end MlDsaOpt44.Proofs
