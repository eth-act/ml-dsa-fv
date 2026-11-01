import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Fn.Ball.Defs
import MlDsaOpt87.Fn.Csum.Defs
import MlDsaOpt44.Math.SpongeBytes
set_option warningAsError true
/-!
# Main-flow invariants (ML-DSA-87)

The main flow (regions `main`, `expand_a`, `hash_mu`, `final_hash` of
`MlDsaOpt/87/layout.txt`) is cut into segments at fixed program counters
(`scripts/proofgen_gas_param.py`, `SEGMENTS[87]`). The invariants say what
memory holds at each boundary for calldata `cd`. Facts about data that may be
invalid (hints, `c`, `A`) are conditional on the corresponding validity flag;
everything needed for termination and gas is unconditional.

Row groups: polynomials / rows `0 … 3` live in the lanes of one 8 KB table,
`4 … 7` in the lanes of a second table `0x2000` higher: `ZH` / `ZH2 = ZH + 0x2000`
(`ẑ`; lane 3 of `ZH2` is a phantom eighth polynomial), `ACC` / `ACC + 0x2000`
(`Â ẑ`), `HP` / `HP + 0x2000` (hint bits), `SP` / `SP + 0x2000` (`c · t1`).

| boundary | pc | stack | invariant |
|---|---|---|---|
| sized, tables | 992 | `[]` | `Inv0` |
| z, hints | 1126 | `[ok1]` | `Inv1` |
| c (`sib`, own `kf1` sponge) | 1135 | `[ok2]` | `Inv2` |
| NTT records | 3118 | `[ok2]` | `Inv3` |
| ẑ (both tables) | 3140 | `[ok2]` | `Inv4` |
| ρ spread | 3389 | `[ok2]` | `Inv5` |
| group `[15, s, 0]`, `s < 7` | 3402, 3416, …, 3486 | `[ok2 ∧ C₀(0) … C₀(s)]` | `InvA cd m (s + 1)` |
| group `[15, s, 1]`, `s < 3` | 3500, 3515, 3530 | `[… ∧ C₁(0) … C₁(s)]` | `InvB cd m (s + 1)` |
| mixed group `10 + i` (rows 4–6 col `3 + i`, `tr` blocks `5i … 5i + 4`), `i < 3` | 3963, 4430, 4898 | `[… ∧ M(3) … M(3 + i)]` | `InvT cd m (4 + i)` |
| mixed group 13 (col 6, last `tr` blocks, `TRL`) | 5435 | `[… ∧ M(6)]` | `InvTr cd m` |
| Kronecker group 14 (row 7, cols 3–6) | 5593 | `[ok3]` | `Inv6` |
| μ | 6591 | `[ok3]` | `Inv7` |
| c · t1 | 6646 | `[ok3]` | `Inv8` |
| w1Encode | 6724 | `[ok3]` | `Inv9` |

with `ok1 = okZ ∧ okH`, `ok2 = ok1 ∧ okC`, `ok3 = ok2 ∧ okA` (the order of
`optAccepts`); `C₀(s) = okCol cd 0 s 4`, `C₁(s) = okCol cd 1 s 4`,
`M(s) = okCol cd 1 s 3` (rows 4–6 only: slot 3 carries `tr`), and group 14's
flag is `okRow7 cd` (row 7, columns 3–6). The flag after group 14 is `ok3` by
`flags_eq` (`Main/Valid.lean`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

def ok1 (cd : ByteArray) : Bool := okZ cd && okH cd
def ok2 (cd : ByteArray) : Bool := ok1 cd && okC cd
def ok3 (cd : ByteArray) : Bool := ok2 cd && okA cd

/-! ## Flags of the ExpandA groups -/

/-- Rows `4 rb … 4 rb + nr − 1` of column `s` of `A` exist: the flag of
`group [15, s, rb]` (`nr = 4`, `gOk cd 15 s rb`) and of `gfix 7` in the mixed
groups 10–13 (`rb = 1`, `nr = 3`). -/
def okCol (cd : ByteArray) (rb s nr : Nat) : Bool :=
  (List.range nr).all fun r => (aOf cd (4 * rb + r) s).isSome

/-- Row 7, columns 3–6 of `A` exist: the flag of the Kronecker group 14
(slots 3, 2, 1, 0 hold `A[7][3]`, `A[7][4]`, `A[7][5]`, `A[7][6]`). -/
def okRow7 (cd : ByteArray) : Bool := (List.range 4).all fun i => (aOf cd 7 (3 + i)).isSome

/-- Columns `0 … n − 1` of the rows `4 rb … 4 rb + nr − 1` exist. -/
def okUpTo (cd : ByteArray) (rb nr : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => okUpTo cd rb nr n && okCol cd rb n nr

/-- Columns `3 … n − 1` of rows 4–6 exist (the mixed groups done so far). -/
def okMid (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okMid cd n && (decide (n < 3) || okCol cd 1 n 3)

/-! ## Row-group addressing -/

/-- The word holding `ẑ_k[t]` (lane `k % 4`): `ZH` for `k < 4`, `ZH2` for `4 ≤ k < 8`. -/
def zhAddr (k t : Nat) : Nat := ZH + 0x2000 * (k / 4) + 32 * t

/-- `ẑ_k[t]` as stored (lane `k % 4` of `zhAddr k t`). -/
def zhLane (m : ByteArray) (k t : Nat) : Nat := lane (word m (zhAddr k t)) (k % 4)

/-- The word holding row `r` of `Â ẑ` at `t` (lane `r % 4`). -/
def accAddr (r t : Nat) : Nat := ACC + 0x2000 * (r / 4) + 32 * t

/-- The word holding the hint bits of row `r` at `t` (lane `r % 4`). -/
def hpAddr (r t : Nat) : Nat := HP + 0x2000 * (r / 4) + 32 * t

/-! ## Memory predicates -/

/-- `HP` (two 8 KB tables) holds bit lanes, and the decoded hint when there is one
(row `r` in lane `r % 4` of table `r / 4`); the post of `dhint_call`. -/
def HPAt (m : ByteArray) (cd : ByteArray) : Prop :=
  (∀ g, g < 2 → ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
    word m (HP + 0x2000 * g + 32 * t) = pack4 b) ∧
  (∀ h, hintOf cd = some h → ∀ r, r < 8 → ∀ t, t < 256 →
    lane (word m (hpAddr r t)) (r % 4) = (h[r]![t]!).toNat)

/-- `ZH` / `ZH2` hold the lanes the two `dz` calls decode: polynomials `0 … 3`
and `4 … 7` of the 20-bit z stream (polynomial 7 is the phantom read past `z_6`:
hint bytes, message, zeros). -/
def ZAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ t, t < 256 → word m (ZH + 32 * t) = pack4 (fun k => zLane cd k t) ∧
    word m (ZH2 + 32 * t) = pack4 (fun k => zLane cd (4 + k) t)

/-- `ZH` / `ZH2` hold `ẑ_0 … ẑ_6` (bounded representatives mod q). -/
def ZHatAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ k, k < 7 → ∀ t, t < 256 → zhLane m k t < 2 ^ 28 ∧
    ((zhLane m k t : Int) - (zHat cd k)[t]!) % (Fips204.q : Int) = 0

/-- Row `r` of `Â ẑ` at `t` after columns `0 … n − 1`: `Σ_s A[r][s][t] · ẑ_s[t]`
(explicit recursion, no `List.sum`: see the pitfalls in `MlDsaOpt44/PLAN.md`). -/
def accSum (cd m : ByteArray) (r t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => accSum cd m r t n + ((aD cd r n)[t]!).toNat * zhLane m n t

/-- The accumulator table of row group `rb` after the columns `s < n` of all four
rows (exact lane sums, guarded by the groups' flags). -/
def AccCols (m : ByteArray) (cd : ByteArray) (rb n : Nat) : Prop :=
  okUpTo cd rb 4 n = true → ∀ t, t < 256 →
    word m (ACC + 0x2000 * rb + 32 * t) = pack4 fun j => accSum cd m (4 * rb + j) t n

/-- `ACC + 0x2000` during the mixed groups 10–13: rows 4–6 (lanes 0–2) after
the columns `s < n`, row 7 (lane 3, untouched by the masked `pass3m`) after the
columns `s < 3`. -/
def AccMid (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  (okUpTo cd 1 4 3 && okMid cd n) = true → ∀ t, t < 256 →
    word m (ACC + 0x2000 + 32 * t) =
      pack4 fun j => accSum cd m (4 + j) t (if j < 3 then n else 3)

/-- `ACC` / `ACC + 0x2000` hold `Â ẑ` (bounded representatives mod q) when `A`
exists; every lane of both tables is `< 2^58` (the `intt` precondition). -/
def AccAt (m : ByteArray) (cd : ByteArray) : Prop :=
  okA cd = true →
    (∀ g, g < 2 → ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 58) ∧
    ∀ r, r < 8 → ∀ t, t < 256 →
      ((lane (word m (accAddr r t)) (r % 4) : Int) - (azRow cd r)[t]!) % (Fips204.q : Int) = 0

/-- The padded public key (input of `tr = H(pk)`, 20 blocks of 136 bytes). -/
def padPk (cd : ByteArray) : ByteArray := MlDsa44.Fips202.pad 136 0x1F (pkOf cd)

/-- SIMD slot 3 of `KS` holds the `tr` sponge after absorbing (and permuting)
the first `n` blocks of the padded public key (the `tr` rider of groups 10–13). -/
def TrSlot (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 3 = MlDsaOpt44.Proofs.absorbPre 136 (padPk cd) n

/-- `tr` (8 lanes) in `TRL` (group 13's `cext`). -/
def TrlAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf cd) (8 * x)

/-- The 8 + 128 replicated stream lanes of the final hash input (1088 bytes) in `FIN`. -/
def FinAt (m : ByteArray) (X : ByteArray) : Prop :=
  ∀ x, x < 136 → word m (FIN + 32 * x) = rep (le64 X (8 * x))

/-- μ's lanes, replicated, in `FIN[0, 8)`. -/
def FinMu (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 8 → word m (FIN + 32 * x) = rep (le64 (muOf cd) (8 * x))

/-- `c` as `sib` leaves it (when it exists), and the window bases `csum` loads
from (`BASES[i] + TT − 32 u` stays inside the window table) unconditionally. -/
def CAt (m : ByteArray) (cd : ByteArray) : Prop :=
  (okC cd = true → CRep m (cD cd)) ∧ ∀ i, i < P.tau → word m (BASES + 32 * i) ≤ 6112

/-- `SP` / `SP + 0x2000` hold `2^13 S'(t) + n_neg(t)` per row (`csum` of row
group `g` reads the `t1` rows at calldata offset `32 + 1280 g`). -/
def SpAt (m : ByteArray) (cd : ByteArray) : Prop :=
  okC cd = true → ∀ g, g < 2 → ∀ t, t < 256 → word m (SP + 0x2000 * g + 32 * t) =
    pack4 fun r => 2 ^ 13 * sPrime (cD cd) cd (32 + 1280 * g) r t + nNeg (cD cd) t

/-! ## Invariants -/

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
  z : ZAt m cd
  hp : HPAt m cd
  c : CAt m cd
  zAcc : ZeroOn m ACC HP

structure Inv3 (cd m : ByteArray) : Prop extends Inv2 cd m where
  tbl : TblAt m

structure Inv4 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  hp : HPAt m cd
  c : CAt m cd
  zAcc : ZeroOn m ACC HP

structure Inv5 (cd m : ByteArray) : Prop extends Inv4 cd m where
  rho : Rho1At m cd

/-- What every ExpandA boundary keeps. -/
structure InvE (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  hp : HPAt m cd
  c : CAt m cd
  rho : Rho1At m cd

/-- After the row-group-0 groups `[15, s, 0]`, `s < n`. -/
structure InvA (cd m : ByteArray) (n : Nat) : Prop extends InvE cd m where
  acc0 : AccCols m cd 0 n
  zAcc1 : ZeroOn m (ACC + 0x2000) HP

/-- After row group 0 and the row-group-1 groups `[15, s, 1]`, `s < n`. -/
structure InvB (cd m : ByteArray) (n : Nat) : Prop extends InvE cd m where
  acc0 : AccCols m cd 0 7
  acc1 : AccCols m cd 1 n

/-- During the mixed groups 10–13: rows 4–6 after the columns `s < n`. -/
structure InvM (cd m : ByteArray) (n : Nat) : Prop extends InvE cd m where
  acc0 : AccCols m cd 0 7
  acc1 : AccMid m cd n

/-- After mixed group `n − 1` (`n = 4, 5, 6`): the `tr` sponge after `5 (n − 3)`
blocks in slot 3 of `KS`. -/
structure InvT (cd m : ByteArray) (n : Nat) : Prop extends InvM cd m n where
  tr : TrSlot m cd (5 * (n - 3))

/-- After mixed group 13: `tr` in `TRL`. -/
structure InvTr (cd m : ByteArray) : Prop extends InvM cd m 7 where
  trl : TrlAt m cd

structure Inv6 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  c : CAt m cd
  trl : TrlAt m cd

structure Inv7 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  c : CAt m cd
  fmu : FinMu m cd

structure Inv8 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  fmu : FinMu m cd
  sp : SpAt m cd

structure Inv9 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  fin : ok3 cd = true → FinAt m (finBytes cd)

end MlDsaOpt87.Proofs
