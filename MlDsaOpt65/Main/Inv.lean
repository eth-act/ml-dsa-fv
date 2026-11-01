import MlDsaOpt65.Fn.Group.Defs
import MlDsaOpt65.Fn.Ball.Defs
import MlDsaOpt65.Fn.Csum.Defs
import MlDsaOpt44.Math.SpongeBytes
set_option warningAsError true
/-!
# Main-flow invariants (ML-DSA-65)

The main flow (regions `main`, `expand_a`, `hash_mu`, `final_hash` of
`MlDsaOpt/65/layout.txt`) is cut into segments at fixed program counters
(`scripts/proofgen_gas_param.py`, `SEGMENTS[65]`). `InvK cd m` is what memory
holds at boundary `K` for calldata `cd`. Facts about data that may be invalid
(hints, `c`, `A`) are conditional on the corresponding validity flag;
everything needed for termination and gas is unconditional.

Row groups: polynomials / rows `0 … 3` live in the lanes of one 8 KB table,
rows `4, 5` (and `z_4`) in lanes `0, 1` (lane `0`) of a second table `0x2000`
higher: `ZH` / `ZH2 = ZH + 0x2000` (`ẑ`), `ACC` / `ACC + 0x2000` (`Â ẑ`),
`HP` / `HP + 0x2000` (hint bits), `SP` / `SP + 0x2000` (`c · t1`).

| boundary | pc | stack | invariant |
|---|---|---|---|
| sized, tables | 992 | `[]` | `Inv0` |
| z, hints | 1110 | `[ok1]` | `Inv1` |
| NTT records | 3093 | `[ok1]` | `Inv2` |
| ẑ (both tables) | 3115 | `[ok1]` | `Inv3` |
| ρ, c̃ spread | 3565 | `[ok1]` | `Inv4` |
| group `[15, s, 0]`, `s < 5` | 3578, 3592, 3606, 3620, 3634 | `[ok1 ∧ A₀·0 … A₀·s]` | `InvG cd m (s + 1)` |
| group 5 (A rows 4, 5 col 0; c̃ stream; tr blocks 0–4) | 4074 | `[… ∧ A₁·0]` | `InvT cd m 1` |
| group 6 (col 1; tr blocks 5–9) | 4517 | `[… ∧ A₁·1]` | `InvT cd m 2` |
| group 7 (col 2; tr blocks 10–14, `TRL`) | 5029 | `[… ∧ A₁·2]` | `InvTr cd m` |
| group 8 (col 3; μ rider `MU`) | 5221 | `[… ∧ A₁·3]` | `InvMu cd m` |
| group `[3, 4, 1]` (col 4) | 5236 | `[ok2]` | `Inv5` |
| μ | 6545 | `[ok2]` | `Inv6` |
| c | 6555 | `[ok3]` | `Inv7` |
| c · t1 | 6610 | `[ok3]` | `Inv8` |
| w1Encode | 6688 | `[ok3]` | `Inv9` |

with `ok1 = okZ ∧ okH`, `ok2 = ok1 ∧ okA`, `ok3 = ok2 ∧ okC`; `A₀·s` is
`okCol0 cd s` (rows `0 … 3` of column `s`), `A₁·s` is `okCol1 cd s` (rows 4, 5).
The flag after group 9 is `ok2` by `flags_eq` (`Main/Valid.lean`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

def ok1 (cd : ByteArray) : Bool := okZ cd && okH cd
def ok2 (cd : ByteArray) : Bool := ok1 cd && okA cd
def ok3 (cd : ByteArray) : Bool := ok2 cd && okC cd

/-! ## Flags of the ExpandA groups -/

/-- Rows `0 … 3` of column `s` of `A` exist (the flag of `group [15, s, 0]`,
`gOk cd 15 s 0`). -/
def okCol0 (cd : ByteArray) (s : Nat) : Bool :=
  (aOf cd 0 s).isSome && (aOf cd 1 s).isSome && (aOf cd 2 s).isSome && (aOf cd 3 s).isSome

/-- Rows `4, 5` of column `s` of `A` exist (the flag of `gfix 3` in the mixed
groups 5–8 and of `group [3, 4, 1]`). -/
def okCol1 (cd : ByteArray) (s : Nat) : Bool := (aOf cd 4 s).isSome && (aOf cd 5 s).isSome

/-- Columns `0 … n − 1` of row group 0 exist. -/
def okUpTo0 (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okUpTo0 cd n && okCol0 cd n

/-- Columns `0 … n − 1` of row group 1 exist. -/
def okUpTo1 (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okUpTo1 cd n && okCol1 cd n

/-! ## Row-group addressing -/

/-- The word holding `ẑ_k[t]` (lane `k % 4`): `ZH` for `k < 4`, `ZH2` for `k = 4`. -/
def zhAddr (k t : Nat) : Nat := ZH + 0x2000 * (k / 4) + 32 * t

/-- `ẑ_k[t]` as stored (lane `k % 4` of `zhAddr k t`). -/
def zhLane (m : ByteArray) (k t : Nat) : Nat := lane (word m (zhAddr k t)) (k % 4)

/-- The word holding row `r` of `Â ẑ` at `t` (lane `r % 4`). -/
def accAddr (r t : Nat) : Nat := ACC + 0x2000 * (r / 4) + 32 * t

/-- The word holding the hint bits of row `r` at `t` (lane `r % 4`). -/
def hpAddr (r t : Nat) : Nat := HP + 0x2000 * (r / 4) + 32 * t

/-! ## Memory predicates -/

/-- `HP` (two 8 KB tables) holds bit lanes, and the decoded hint when there is one
(row `r` in lane `r % 4` of table `r / 4`). -/
def HPAt (m : ByteArray) (cd : ByteArray) : Prop :=
  (∀ g, g < 2 → ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
    word m (HP + 0x2000 * g + 32 * t) = pack4 b) ∧
  (∀ h, hintOf cd = some h → ∀ r, r < 6 → ∀ t, t < 256 →
    lane (word m (hpAddr r t)) (r % 4) = (h[r]![t]!).toNat)

/-- `ZH` / `ZH2` hold the lanes `dz` decodes: polynomials `0 … 3` and `4 … 7`
of the 20-bit z stream (`4 … 7` past `z_4` read the hint bytes, the message and
zeros; only lane 0 of `ZH2` is `z_4`). -/
def ZAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ t, t < 256 → word m (ZH + 32 * t) = pack4 (fun k => zLane cd k t) ∧
    word m (ZH2 + 32 * t) = pack4 (fun k => zLane cd (4 + k) t)

/-- `ZH` / `ZH2` hold `ẑ_0 … ẑ_4` (bounded representatives mod q). -/
def ZHatAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ k, k < 5 → ∀ t, t < 256 → zhLane m k t < 2 ^ 28 ∧
    ((zhLane m k t : Int) - (zHat cd k)[t]!) % (Fips204.q : Int) = 0

/-- Lane `r` of the accumulator of row `r` at `t` after columns `0 … n − 1`:
`Σ_s A[r][s][t] · ẑ_s[t]` (explicit recursion, no `List.sum`: see the pitfalls in
`MlDsaOpt44/PLAN.md`). -/
def accSum (cd m : ByteArray) (r t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => accSum cd m r t n + ((aD cd r n)[t]!).toNat * zhLane m n t

/-- `ACC` (row group 0) after the columns `s < n` (exact lane sums, valid columns). -/
def AccCols0 (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  okUpTo0 cd n = true → ∀ t, t < 256 → word m (ACC + 32 * t) = pack4 fun r => accSum cd m r t n

/-- `ACC + 0x2000` (row group 1, rows 4 and 5 in lanes 0 and 1) after the columns
`s < n`. Lanes 2 and 3 carry products of the inactive / rider slots (23-bit
candidates times `ẑ` lanes `< 2^28`): only their bound is kept, which `intt`
needs (all four lanes `< 2^58`). -/
def AccCols1 (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  okUpTo1 cd n = true → ∀ t, t < 256 →
    (∀ j, j < 2 → lane (word m (ACC + 0x2000 + 32 * t)) j = accSum cd m (4 + j) t n) ∧
    (∀ j, 2 ≤ j → j < 4 → lane (word m (ACC + 0x2000 + 32 * t)) j ≤ n * 2 ^ 51)

/-- `ACC` / `ACC + 0x2000` hold `Â ẑ` (bounded representatives mod q) when `A`
exists; every lane of both tables is `< 2^58` (the `intt` precondition). -/
def AccAt (m : ByteArray) (cd : ByteArray) : Prop :=
  okA cd = true →
    (∀ g, g < 2 → ∀ k, k < 4 → ∀ t, t < 256 →
      lane (word m (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 58) ∧
    ∀ r, r < 6 → ∀ t, t < 256 →
      ((lane (word m (accAddr r t)) (r % 4) : Int) - (azRow cd r)[t]!) % (Fips204.q : Int) = 0

/-- The padded public key (input of `tr = H(pk)`, 15 blocks of 136 bytes). -/
def padPk (cd : ByteArray) : ByteArray := MlDsa44.Fips202.pad 136 0x1F (pkOf cd)

/-- SIMD slot 3 of `KS` holds the `tr` sponge after absorbing (and permuting)
the first `n` blocks of the padded public key (the `tr` rider of groups 5–7). -/
def TrSlot (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 3 = MlDsaOpt44.Proofs.absorbPre 136 (padPk cd) n

/-- The SampleInBall stream `H(c̃)` (34 lanes) in `CB` (group 5's `c` slot). -/
def CbAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)

/-- `tr` (8 lanes) in `TRL` (group 7's `cext`). -/
def TrlAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf cd) (8 * x)

/-- μ (8 lanes) in `MU` for short messages (group 8's `mu0` rider). -/
def MuAt (m : ByteArray) (cd : ByteArray) : Prop :=
  mlenOf cd ≤ 69 → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)

/-- The 8 + 96 replicated stream lanes of the final hash input in `FIN`. -/
def FinAt (m : ByteArray) (X : ByteArray) : Prop :=
  ∀ x, x < 104 → word m (FIN + 32 * x) = rep (le64 X (8 * x))

/-- μ's lanes, replicated, in `FIN[0, 8)`. -/
def FinMu (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 8 → word m (FIN + 32 * x) = rep (le64 (muOf cd) (8 * x))

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

/-- Between the row-group-0 groups: columns `s < n` accumulated in `ACC`. -/
structure InvG (cd m : ByteArray) (n : Nat) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  hp : HPAt m cd
  rho : Rho1At m cd
  acc : AccCols0 m cd n
  zMisc : ZeroOn m MISC (MISC + 0x1e0)
  zCw : ZeroOn m CW ABUF
  zIdx : ZeroOn m BASES ACC
  zAcc1 : ZeroOn m (ACC + 0x2000) HP

/-- Between the row-group-1 groups: row group 0 complete, columns `s < n` of
rows 4, 5 accumulated in `ACC + 0x2000`, the c̃ stream in `CB`. -/
structure InvR (cd m : ByteArray) (n : Nat) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  hp : HPAt m cd
  rho : Rho1At m cd
  acc0 : AccCols0 m cd 5
  acc1 : AccCols1 m cd n
  cb : CbAt m cd
  zMisc : ZeroOn m MISC (MISC + 0x1e0)
  zCw : ZeroOn m CW ABUF
  zIdx : ZeroOn m BASES ACC

/-- After groups 5 (`n = 1`) and 6 (`n = 2`): the `tr` sponge after `5 n` blocks
in slot 3 of `KS`. -/
structure InvT (cd m : ByteArray) (n : Nat) : Prop extends InvR cd m n where
  tr : TrSlot m cd (5 * n)

/-- After group 7: `tr` in `TRL`. -/
structure InvTr (cd m : ByteArray) : Prop extends InvR cd m 3 where
  trl : TrlAt m cd

/-- After group 8: `tr` in `TRL`, μ in `MU` for short messages. -/
structure InvMu (cd m : ByteArray) : Prop extends InvR cd m 4 where
  trl : TrlAt m cd
  mu : MuAt m cd

structure Inv5 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  trl : TrlAt m cd
  mu : MuAt m cd
  cb : CbAt m cd
  fresh : SibFresh m

structure Inv6 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  cb : CbAt m cd
  fresh : SibFresh m
  fmu : FinMu m cd

structure Inv7 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  fmu : FinMu m cd
  crep : okC cd = true → CRep m (cD cd)
  /-- `csum` loads from `BASES[i] + TT − 32 u`: the bases stay inside the window table. -/
  bases : ∀ i, i < P.tau → word m (BASES + 32 * i) ≤ 6112

/-- `SP` / `SP + 0x2000`: `2^13 S'(t) + n_neg(t)` of rows `4g … 4g + 3` (the
window tables of `t1` rows from calldata offsets `32` and `0x520`). -/
structure Inv8 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  hp : HPAt m cd
  acc : AccAt m cd
  fmu : FinMu m cd
  sp : okC cd = true → ∀ g, g < 2 → ∀ t, t < 256 → word m (SP + 0x2000 * g + 32 * t) =
    pack4 fun r => 2 ^ 13 * sPrime (cD cd) cd (32 + 1280 * g) r t + nNeg (cD cd) t

structure Inv9 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  fin : ok3 cd = true → FinAt m (finBytes cd)

end MlDsaOpt65.Proofs
