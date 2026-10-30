import MlDsa44.Proofs.Fn.Keccak.Blocks1
import MlDsa44.Proofs.Fn.Keccak.Blocks2
/-!
# One iteration of the `keccakF` loop as a trace

The fifteen straight-line blocks of `Blocks1`/`Blocks2` composed: from the loop
head (pc 6) with counter `r` back to the loop head with counter `r + 2`,
turning memory `M` into `iterY M r`, for exactly 4524 gas.
-/

namespace MlDsa44.Proofs.KeccakBlocks

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.KeccakModel

theorem iter_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htl : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsz : 2535 ≤ s.activeWords.toNat) (M : ByteArray) (r : Nat) (hr : r < 24) :
    Infra.Reach (callState s 6 (wd r :: wd ret :: tail) M)
      (callState s 6 (wd (r + 2) :: wd ret :: tail) (iterY M r)) 4524 := by
  have h := ((((((((((((((blk_theta1 (ret := ret) hs htl haw hsz M r hr).trans
    (blk_d1 hs htl haw hsz _ r)).trans
    (blk_row1_0 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row1_1 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row1_2 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row1_3 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row1_4 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_iotaTheta2 hs htl haw hsz _ r hr)).trans
    (blk_d2 hs htl haw hsz _ r)).trans
    (blk_row2_0 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row2_1 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row2_2 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row2_3 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_row2_4 hs htl haw hsz _ r _ _ _ _ _)).trans
    (blk_iotaLoop hs htl haw hsz _ r hr)
  exact h

end MlDsa44.Proofs.KeccakBlocks
