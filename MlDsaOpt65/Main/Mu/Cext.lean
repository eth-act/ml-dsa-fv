import MlDsaOpt44.Fn.Sponge.Cext
import MlDsaOpt65.Fn.Sponge.Cext  -- port: the 65 `cext` blocks
/- Ported from `MlDsaOpt44/Main/Mu/Cext.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
/-!
# `cext` in place (`dst = KS`)

`hash_mu` extracts slot 2 of the kf4 state in `KS` into `KS` itself
(`cext 25, 2, 0`). The contract `cext_call` asks `KS + 800 ≤ dst`; in place,
lane `x` is read before it is written and the later lanes are untouched, so
the same loop gives the same lane values. The block lemmas are those of
`Fn/Sponge/Cext.lean` without the (unused) bound on `dst`.
-/

namespace MlDsaOpt65.Proofs.S6Mu

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra
open MlDsaOpt65.Proofs.WP4
open MlDsaOpt44.Proofs.WP4 hiding cextOut cextOut_eq cext_entry  -- port: the 65 `cextOut`

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cextIP_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 < n) (hn : n ≤ 25) (hsh : sh < 4) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 12878 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s 12878 (wd (x + 1) :: wd n :: wd sh :: wd dst :: wd ret :: tail)
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      205 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  opt65_reach [5708, 5709, 5710, 5711, 5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719, 5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727, 5728, 5729, 5730, 5731, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5739, 5740, 5741, 5742, 5743, 5744, 5745, 5746, 5747, 5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755, 5756, 5757, 5758, 5759, 5760, 5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773] with []
  exact ⟨rfl, by rw [Nat.add_comm]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cextIP_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 = n) (hn : n ≤ 25) (hsh : sh < 4) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 12878 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      221 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [5708, 5709, 5710, 5711, 5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719, 5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727, 5728, 5729, 5730, 5731, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5739, 5740, 5741, 5742, 5743, 5744, 5745, 5746, 5747, 5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755, 5756, 5757, 5758, 5759, 5760, 5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773, 5774, 5775, 5776, 5777, 5778] with [hj]
  rfl

/-- `cext` with `dst = KS`: lane `x` of slot `sh`, de-interleaved and
un-complemented, replaces the state word `x`, `x < n`. -/
theorem cext_inplace_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (m : ByteArray) {sh n : Nat}
    (hsh : sh < 4) (hn : 1 ≤ n) (hn' : n ≤ 25) :
    ∃ m', (∀ x, x < n → word m' (KS + 32 * x) =
        cpl x (compress (word m (KS + 32 * x) / 2 ^ sh &&& spread M64))) ∧
      FrameExcept m m' [(KS, KS + 32 * n)] ∧
      Call s Entry.cext [wd n, wd sh, wd KS] ret tail m [] m' (Gas.cext n) := by
  have hdm : 0 + 32 * n ≤ TOP := by unfold TOP; omega
  simp only [KS, Nat.zero_add] at hdm ⊢
  let g : Nat → Nat := fun x => cpl x (compress (word m (32 * x) / 2 ^ sh &&& spread M64))
  have hg : ∀ x, g x < 2 ^ 256 := by
    intro x
    have := compress_lt (word m (32 * x) / 2 ^ sh &&& spread M64)
    simp only [g, cpl]; split <;> omega
  refine ⟨storeWords m 0 g n, fun x hx => by
      have := word_storeWords_get (m := m) (base := 0) (hg x) hx
      rwa [Nat.zero_add] at this,
    by have := FrameExcept.storeWords m 0 g n; rwa [Nat.zero_add] at this, ?_⟩
  let I : Nat → State := fun k =>
    callState s 12878 (wd k :: wd n :: wd sh :: wd 0 :: wd ret :: tail) (storeWords m 0 g k)
  have hstep : ∀ k, k < 25 → MachineState.writeBytes (storeWords m 0 g k)
      (Data.Bytes.natToBytesPadded (cextOut k (word (storeWords m 0 g k) (k * 32) / 2 ^ sh)) 32)
      (0 + k * 32) = storeWords m 0 g (k + 1) := by
    intro k hk
    rw [storeWords_succ, word_storeWords_out (Or.inr (by omega)), cextOut_eq hk,
      show k * 32 = 32 * k by omega]
  have hbody : ∀ k, k < n - 1 → Reach (I k) (I (k + 1)) 205 := by
    intro k hk
    have h := cextIP_body hs hr (storeWords m 0 g k) (x := k) (n := n) (sh := sh) (dst := 0)
      (by omega) hn' hsh (by omega)
    rwa [hstep k (by omega)] at h
  have hloop := Reach.loop (I := I) (n - 1) hbody
  have hlast := cextIP_last hs hr (storeWords m 0 g (n - 1)) (x := n - 1) (n := n) (sh := sh)
    (dst := 0) (by omega) hn' hsh (by omega)
  rw [hstep (n - 1) (by omega), show n - 1 + 1 = n by omega] at hlast
  have hentry := cext_entry hs hr m n sh 0
  rw [call_iff, Entry.cext, Gas.cext]
  refine ((hentry.trans (hloop.trans hlast)).mono (by
    have : (n - 1) * 205 + 205 = n * 205 := by
      rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    omega)).of_eq (by simp) rfl

end MlDsaOpt65.Proofs.S6Mu
