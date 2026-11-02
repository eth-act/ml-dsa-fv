import MlDsaOptGlam65.Fn.Pack65.Kmove
import MlDsaOptGlam65.Fn.Pack65.Lmerge
import MlDsaOptGlam65.Fn.Pack65.P3f8
import MlDsaOptGlam65.Fn.Pass3f.Defs
import MlDsaOptGlam65.Fn.Group
import MlDsaOptGlam65.Budget
set_option warningAsError true
/-!
# Routines of 65's `PACK65` 42-call schedule (glam only)

`kmove` and `lmerge` move and merge Keccak states between the side buffers;
`pass3f7` / `pass3f8` are the two row groups of the interleaved fused pass.
The proofs (`Fn/Pack65/*`) state addresses, entry pcs and costs as literals;
these wrappers restate them with the layout names.
-/

namespace MlDsaOptGlam65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs (KS Call)

/-- **kmove**: `KS[x] := (((src[x] << sl) >> sr) & msk) | (KS[x] & keep)` for the
25 lanes (`src` may be `KS`). -/
theorem kmove_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kmove ret tail) (m : ByteArray) {src sl sr msk keep : Nat}
    (hsrc : src = KS ∨ KS + 800 ≤ src) (hsrc' : src + 800 ≤ TOP) (hsl : sl < 256) (hsr : sr < 256)
    (hmsk : msk < 2 ^ 256) (hkeep : keep < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        (word m (src + 32 * x) * 2 ^ sl % 2 ^ 256 / 2 ^ sr &&& msk) ||| (word m (KS + 32 * x) &&& keep)) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.kmove [wd keep, wd msk, wd sr, wd sl, wd src] ret tail m [] m' Gas.kmove := by
  simp only [KS, TOP, Nat.zero_add] at hsrc hsrc' ⊢
  exact Pack65.kmove_call_aux hs hr m hsrc hsrc' hsl hsr hmsk hkeep

/-- **lmerge**: `[a, a + 32 n, sl, b − a, ma, dst − a, ret]` (offsets mod
`2^256`), `n = 14 k`; for `w < n`, `dst[w] :=` the lanes `ma` of `a[w]`, the
others of `b[w] << sl`. -/
theorem lmerge_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (m : ByteArray) {dst a b ma sl k : Nat}
    (hk : 1 ≤ k) (hdst : dst + 448 * k ≤ TOP) (ha : a + 448 * k ≤ TOP) (hb : b + 448 * k ≤ TOP)
    (hda : dst = a ∨ dst + 448 * k ≤ a ∨ a + 448 * k ≤ dst)
    (hdb : dst + 448 * k ≤ b ∨ b + 448 * k ≤ dst) (hma : ma < 2 ^ 256) (hsl : sl < 256) :
    ∃ m', (∀ w, w < 14 * k → word m' (dst + 32 * w) =
        let b' := word m (b + 32 * w) * 2 ^ sl % 2 ^ 256
        b' ^^^ ((word m (a + 32 * w) ^^^ b') &&& ma)) ∧
      FrameExcept m m' [(dst, dst + 448 * k)] ∧
      Call s Entry.lmerge [wd a, wd (a + 448 * k), wd sl, wd ((b + 2 ^ 256 - a) % 2 ^ 256), wd ma,
        wd ((dst + 2 ^ 256 - a) % 2 ^ 256)] ret tail m [] m' (Gas.lmerge k) :=
  Pack65.lmerge_call_aux hs hr m hk hdst ha hb hda hdb hma hsl

/-- **pass3f7**: row group 0 of the interleaved fused pass, into `ACC`. -/
theorem pass3f7_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f7 ret tail m ACC Gas.pass3f7 p3f7Word :=
  Pack65.pass3f7_call_aux hs hr m

/-- **pass3f8**: row group 1 of the interleaved fused pass, into `ACC + 8192`. -/
theorem pass3f8_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f8 ret tail m (ACC + 8192) Gas.pass3f8 p3f8Word :=
  Pack65.pass3f8_call_aux hs hr m

end MlDsaOptGlam65.Proofs
