import MlDsaOpt65.Main.Exp.Acc
set_option warningAsError true
/-!
# Boundary invariants inside ExpandA (ML-DSA-65, v4)

`seg_exp` (`3556 … 5242`) is composed from sub-segments:

| pc | stack | invariant |
|---|---|---|
| 3556 | `[okZ]` | `Inv4` |
| 3674 | `[… ∧ okUpTo0 5]` | `Exp.PureOut` (`Main/Exp/Pure.lean`) |
| 5022 | `[… ∧ okIUpTo 9]` | `Exp.InvG8` (after group 7's copy to `HP + 0x2000`; `Main/Exp/G57.lean`) |
| 5242 | `[… ∧ okI 9]` | `InvW` (group 8, `pass3f8`; `Main/Exp/G8.lean`) |

Row-group-1 instance `i` (`okI`) is `A[4 + i % 2][i / 2]`; groups 5, 6, 7 run
instances `3 g', 3 g' + 1, 3 g' + 2` in slots 0 … 2 (`g' = g − 5`) and copy
`ABUF[0, 256)` to `CW`, `HP`, `HP + 0x2000`; group 8 runs instance 9 in slot 0.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Exp

/-- What row group 0 leaves for the rest of ExpandA (pc 3674, after `pass3f4`). -/
structure PureOut (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  rho : Rho1At m cd
  acc0 : AccCols0 m cd 5
  zNeg : ZeroOn m NNEG (NNEG + 64)
  zBases : ZeroOn m BASES (BASES + 2048)
  zIdx : ZeroOn m IDX (IDX + 256)

/-- The side buffer at `dst` holds the row-group-1 instances `i0, i0 + 1,
i0 + 2` in lanes `0, 1, 2` (when `A` exists). -/
def MixBuf (m : ByteArray) (dst : Nat) (cd : ByteArray) (i0 : Nat) : Prop :=
  okA cd = true → ∀ t, t < 256 → ∀ k, k < 3 →
    lane (word m (dst + 32 * t)) k = ((aD cd (4 + (i0 + k) % 2) ((i0 + k) / 2))[t]!).toNat

theorem MixBuf.frame {m m' : ByteArray} {dst : Nat} {cd : ByteArray} {i0 : Nat} {rs : List (Nat × Nat)}
    (h : MixBuf m dst cd i0) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    MixBuf m' dst cd i0 := fun hok t ht k hk => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht k hk

/-- Before group 8 (pc 5022): row group 0 complete in `ACC`, the nine
row-group-1 instances of groups 5–7 in `CW`, `HP`, `HP + 0x2000`, `tr` in `TRL`. -/
structure InvG8 (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  rho : Rho1At m cd
  acc0 : AccCols0 m cd 5
  b5 : MixBuf m CW cd 0
  b6 : MixBuf m HP cd 3
  b7 : MixBuf m (HP + 8192) cd 6
  trl : TrlAt m cd
  zNeg : ZeroOn m NNEG (NNEG + 64)
  zBases : ZeroOn m BASES (BASES + 2048)
  zIdx : ZeroOn m IDX (IDX + 256)

end Exp

end MlDsaOpt65.Proofs
