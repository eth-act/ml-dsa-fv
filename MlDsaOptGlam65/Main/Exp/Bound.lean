import MlDsaOptGlam65.Main.Exp.Round
import MlDsaOptGlam65.Main.Frame
import MlDsaOptGlam65.Fn.Group
import MlDsaOptGlam65.Fn.Pack65
set_option warningAsError true
/-!
# Boundaries inside ExpandA, the 42-call schedule (glam ML-DSA-65)

`seg_exp` (`2515 … 4903`) is composed from four sub-segments:

| pc | stack | invariant | code |
|---|---|---|---|
| 2515 | `[okZ]` | `Inv4` | |
| 2588 | `[… ∧ okCol0 0, 1, 2]` | `Exp.G3In` | calls 0–14: `group [15, s, 0]`, `s < 3`, copies to `CW`, `HP`, `HP + 0x2000` (`G02.lean`) |
| 2909 | `[… ∧ okRow 4 ∧ okRow 5]` | `Exp.G5In` | calls 15–24: rows 4, 5 (columns 3, 2, 1, 0 in slots 0 … 3), copies to `ACC + 0x2000`, `SB` (`G34.lean`) |
| 3739 | `[… ∧ okCol3 3 ∧ okCol3 4]` | `Exp.WinIn` | calls 25–34: `tr` blocks 0 … 9 in slot 0, rows 0 … 2 of columns 3, 4 in slots 1 … 3, copies to `ACC`, `SB + 0x2000` (`G56.lean`) |
| 4903 | `[… ∧ okP ∧ okKX]` | `InvW` | calls 35–41: the window (`Win*.lean`), `pass3f7`, `pass3f8` |
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Exp

/-- Column `col` of rows `0 … 3` of `A` as a row-packed word. -/
def colBuf (cd : ByteArray) (col t : Nat) : Nat := pack4 fun r => ((aD cd r col)[t]!).toNat

/-- The side buffer at `dst` holds column `col` of rows `0 … 3` (when it exists). -/
def BufCol (m : ByteArray) (dst : Nat) (cd : ByteArray) (col : Nat) : Prop :=
  okCol0 cd col = true → ∀ t, t < 256 → word m (dst + 32 * t) = colBuf cd col t

/-- Columns `0 … 3` of row `r` exist, in the slot order of the Kronecker groups
(slot `k` runs column `3 − k`; the flag of `gfix 15`). -/
def okRow (cd : ByteArray) (r : Nat) : Bool := (List.range 4).all fun k => (aOf cd r (3 - k)).isSome

/-- The side buffer at `dst` holds row `r`, columns `3, 2, 1, 0` in lanes `0 … 3`
(when they exist). -/
def RowBuf (m : ByteArray) (dst : Nat) (cd : ByteArray) (r : Nat) : Prop :=
  okRow cd r = true → ∀ t, t < 256 → ∀ k, k < 4 →
    lane (word m (dst + 32 * t)) k = ((aD cd r (3 - k))[t]!).toNat

/-- Rows `0 … 2` of column `col` exist. -/
def okCol3 (cd : ByteArray) (col : Nat) : Bool := (List.range 3).all fun r => (aOf cd r col).isSome

/-- The side buffer at `dst` holds rows `0 … 2` of column `col` in lanes `1 … 3`
(lane 0: the `tr` slot's candidates, unconstrained). -/
def Col3Hi (m : ByteArray) (dst : Nat) (cd : ByteArray) (col : Nat) : Prop :=
  okCol3 cd col = true → ∀ t, t < 256 → ∀ r, r < 3 →
    lane (word m (dst + 32 * t)) (r + 1) = ((aD cd r col)[t]!).toNat

/-- `P = (A[3][4], A[3][3])` exist (the window's `gfix 12`). -/
def okP (cd : ByteArray) : Bool := (aOf cd 3 4).isSome && (aOf cd 3 3).isSome

/-- `KX = (A[4][4], A[5][4])` exist (the window's `gfix 3`). -/
def okKX (cd : ByteArray) : Bool := (aOf cd 4 4).isSome && (aOf cd 5 4).isSome

theorem BufCol.frame {m m' : ByteArray} {dst : Nat} {cd : ByteArray} {col : Nat} {rs : List (Nat × Nat)}
    (h : BufCol m dst cd col) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    BufCol m' dst cd col := fun hok t ht => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht

theorem RowBuf.frame {m m' : ByteArray} {dst : Nat} {cd : ByteArray} {r : Nat} {rs : List (Nat × Nat)}
    (h : RowBuf m dst cd r) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    RowBuf m' dst cd r := fun hok t ht k hk => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht k hk

theorem Col3Hi.frame {m m' : ByteArray} {dst : Nat} {cd : ByteArray} {col : Nat} {rs : List (Nat × Nat)}
    (h : Col3Hi m dst cd col) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    Col3Hi m' dst cd col := fun hok t ht r hr => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht r hr

/-- After calls 0–14 (pc 2588): columns 0, 1, 2 of rows 0 … 3 in `CW`, `HP`, `HP + 0x2000`. -/
structure G3In (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  rho : Rho1At m cd
  c0 : BufCol m CW cd 0
  c1 : BufCol m HP cd 1
  c2 : BufCol m (HP + 8192) cd 2
  zNeg : ZeroOn m NNEG (NNEG + 64)
  zBases : ZeroOn m BASES (BASES + 2048)
  zIdx : ZeroOn m IDX (IDX + 256)

/-- After calls 15–24 (pc 2909): rows 4, 5 (columns 0 … 3) in `ACC + 0x2000`, `SB`. -/
structure G5In (cd m : ByteArray) : Prop extends G3In cd m where
  r4 : RowBuf m (ACC + 8192) cd 4
  r5 : RowBuf m SB cd 5

/-- After calls 25–34 (pc 3739): rows 0 … 2 of columns 3, 4 in lanes 1 … 3 of
`ACC`, `SB + 0x2000`; `tr`'s sponge after blocks 0 … 9 in slot 0. -/
structure WinIn (cd m : ByteArray) : Prop extends G5In cd m where
  c3 : Col3Hi m ACC cd 3
  c4 : Col3Hi m (SB + 8192) cd 4
  tr : ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 0 = MlDsaOpt44.Proofs.absorbPre 136 (padPk cd) 10

end Exp

end MlDsaOptGlam65.Proofs
