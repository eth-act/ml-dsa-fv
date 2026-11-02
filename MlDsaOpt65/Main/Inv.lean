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
| z | 1101 | `[okZ]` | `Inv1` |
| NTT records | 3084 | `[okZ]` | `Inv2` |
| ẑ (both tables) | 3105 | `[okZ]` | `Inv3` |
| ρ, c̃ spread | 3556 | `[okZ]` | `Inv4` |
| ExpandA done (`pass3f8`) | 5242 | `[okZ ∧ okA]` | `InvW` |
| hints | 5356 | `[… ∧ okH]` | `InvH` |
| μ | 6172 | `[ok2]` | `Inv6` |
| c | 6182 | `[ok3]` | `Inv7` |
| c · t1 | 6237 | `[ok3]` | `Inv8` |
| w1Encode | 6293 | `[ok3]` | `Inv9` |

with `ok2 = (okZ ∧ okA) ∧ okH`, `ok3 = ok2 ∧ okC` (v4: hints are decoded
after ExpandA). The ExpandA segment (`Main/SegExp.lean`) is one segment for
now; the v3 group definitions (`okCol0`, `okI`, `AccCols*`, `AccInst1`,
`TrSlot`) are kept for its proof.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

def ok2 (cd : ByteArray) : Bool := (okZ cd && okA cd) && okH cd
def ok3 (cd : ByteArray) : Bool := ok2 cd && okC cd

/-! ## Flags of the ExpandA groups -/

/-- Rows `0 … 3` of column `s` of `A` exist (the flag of `group [15, s, 0]`,
`gOk cd 15 s 0`). -/
def okCol0 (cd : ByteArray) (s : Nat) : Bool :=
  (aOf cd 0 s).isSome && (aOf cd 1 s).isSome && (aOf cd 2 s).isSome && (aOf cd 3 s).isSome

/-- Rows `4, 5` of column `s` of `A` exist. -/
def okCol1 (cd : ByteArray) (s : Nat) : Bool := (aOf cd 4 s).isSome && (aOf cd 5 s).isSome

/-- Columns `0 … n − 1` of row group 0 exist. -/
def okUpTo0 (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okUpTo0 cd n && okCol0 cd n

/-- Columns `0 … n − 1` of row group 1 exist. -/
def okUpTo1 (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okUpTo1 cd n && okCol1 cd n

/-- Row-group-1 instance `i < 10` of the ExpandA schedule exists: row `4 + i % 2`,
column `i / 2`. Groups 5, 6, 7 run instances `3g', 3g' + 1, 3g' + 2` (`g' = g − 5`,
slots 0–2), group 8 instance 9 (slot 0). -/
def okI (cd : ByteArray) (i : Nat) : Bool := (aOf cd (4 + i % 2) (i / 2)).isSome

/-- Instances `0 … n − 1` exist. -/
def okIUpTo (cd : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => okIUpTo cd n && okI cd n

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
`s < n`, lanes 2 and 3 bounded (`intt` needs all four lanes `< 2^58`). The end
of ExpandA (`AccAt`, `S3/Lemmas.lean`) is stated with this form. -/
def AccCols1 (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  okUpTo1 cd n = true → ∀ t, t < 256 →
    (∀ j, j < 2 → lane (word m (ACC + 0x2000 + 32 * t)) j = accSum cd m (4 + j) t n) ∧
    (∀ j, 2 ≤ j → j < 4 → lane (word m (ACC + 0x2000 + 32 * t)) j ≤ n * 2 ^ 51)

/-- `ACC + 0x2000` after the row-group-1 instances `i < n` (`pass3x5 … pass3x8`):
row 4 (instances `0, 2, 4, …`, columns `< (n + 1) / 2`) in lane 0, row 5
(instances `1, 3, …`, columns `< n / 2`) in lane 1; lanes 2 and 3 are never
written (zero). -/
def AccInst1 (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  okIUpTo cd n = true → ∀ t, t < 256 →
    lane (word m (ACC + 0x2000 + 32 * t)) 0 = accSum cd m 4 t ((n + 1) / 2) ∧
    lane (word m (ACC + 0x2000 + 32 * t)) 1 = accSum cd m 5 t (n / 2) ∧
    lane (word m (ACC + 0x2000 + 32 * t)) 2 = 0 ∧ lane (word m (ACC + 0x2000 + 32 * t)) 3 = 0

/-- `ACC` / `ACC + 0x2000` hold `Â ẑ` (bounded representatives mod q) when `A`
exists; every lane of both tables is `< 2^58` (the `intt` precondition). -/
def AccAt (m : ByteArray) (cd : ByteArray) : Prop :=
  okA cd = true →
    (∀ g, g < 2 → ∀ k, k < 4 → ∀ t, t < 256 →
      lane (word m (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) ∧
    ∀ r, r < 6 → ∀ t, t < 256 →
      ((lane (word m (accAddr r t)) (r % 4) : Int) - (azRow cd r)[t]!) % (Fips204.q : Int) = 0

/-- The padded public key (input of `tr = H(pk)`, 15 blocks of 136 bytes). -/
def padPk (cd : ByteArray) : ByteArray := MlDsa44.Fips202.pad 136 0x1F (pkOf cd)

/-- SIMD slot 3 of `KS` holds the `tr` sponge after absorbing (and permuting)
the first `n` blocks of the padded public key (the `tr` rider of groups 5–7). -/
def TrSlot (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 3 = MlDsaOpt44.Proofs.absorbPre 136 (padPk cd) n

/-- The SampleInBall stream `H(c̃)` (34 lanes) in `CB` (group 8's `c̃` slot). -/
def CbAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)

/-- `tr` (8 lanes) in `TRL` (group 7's `cext`). -/
def TrlAt (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf cd) (8 * x)

/-- μ (8 lanes) in `MU` for messages of at most five blocks (v4: group 8's μ
slot, `mub`). -/
def MuAt (m : ByteArray) (cd : ByteArray) : Prop :=
  mlenOf cd ≤ 613 → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)

/-- μ's padded sponge input `tr ‖ 0 ‖ 0 ‖ M`. -/
def padMu (cd : ByteArray) : ByteArray :=
  MlDsa44.Fips202.pad 136 0x1F (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd))

/-- For longer messages μ's sponge after blocks `0 … 4` is slot 2 of `KS`. -/
def MuKs (m : ByteArray) (cd : ByteArray) : Prop :=
  613 < mlenOf cd → ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 2 = MlDsaOpt44.Proofs.absorbPre 136 (padMu cd) 5

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
  zLow : ZeroOn m MISC ZH
  zHigh : ZeroOn m BASES FIN

structure Inv2 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  z : ZAt m cd
  zMisc : ZeroOn m MISC TBL
  zCw : ZeroOn m CW ABUF
  zHigh : ZeroOn m BASES FIN

structure Inv3 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  zMisc : ZeroOn m MISC TBL
  zCw : ZeroOn m CW ABUF
  zHigh : ZeroOn m BASES FIN

structure Inv4 (cd m : ByteArray) : Prop extends Inv3 cd m where
  rho : Rho1At m cd

/-- After ExpandA (`pass3f8`). -/
structure InvW (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  tbl : TblAt m
  acc : AccAt m cd
  mu : MuAt m cd
  muks : MuKs m cd
  cb : CbAt m cd
  zBases : ZeroOn m BASES (BASES + 2048)
  zIdx : ZeroOn m IDX (IDX + 256)
  zNeg : ZeroOn m NNEG (NNEG + 64)

/-- After the side buffers are zeroed and the hints decoded. -/
structure InvH (cd m : ByteArray) : Prop extends InvW cd m where
  hp : HPAt m cd
  zCw : ZeroOn m CW (CW + 8192)

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
    pack4 fun r => spOff - (2 ^ 13 * sPrime (cD cd) cd (32 + 1280 * g) r t + nNeg (cD cd) t)

structure Inv9 (cd m : ByteArray) : Prop where
  rc1 : RC1Table m
  fin : ok3 cd = true → FinAt m (finBytes cd)

end MlDsaOpt65.Proofs
