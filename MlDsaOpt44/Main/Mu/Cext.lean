import MlDsaOpt44.Fn.Sponge.Cext
set_option warningAsError true
/-!
# `cext` in place (`dst = KS`)

`hash_mu` extracts slot 1 of the kf4 image copied to `KS` into `KS` itself
(`cext 25, 1, 0`). The contract `cext_call` asks `KS + 800 ≤ dst`; in place,
lane `x` is read before it is written and the later lanes are untouched, so
the same loop gives the same lane values. The block lemmas are those of
`Fn/Sponge/Cext.lean` without the (unused) bound on `dst`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.WP4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cextIP_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 < n) (hn : n ≤ 25) (hsh : sh < 4) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 12153 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s 12153 (wd (x + 1) :: wd n :: wd sh :: wd dst :: wd ret :: tail)
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      205 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  opt44_reach [5363, 5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398, 5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428] with []
  exact ⟨rfl, by rw [Nat.add_comm]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cextIP_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 = n) (hn : n ≤ 25) (hsh : sh < 4) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 12153 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      221 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [5363, 5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398, 5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433] with [hj]
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
    callState s 12153 (wd k :: wd n :: wd sh :: wd 0 :: wd ret :: tail) (storeWords m 0 g k)
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

end MlDsaOpt44.Proofs
