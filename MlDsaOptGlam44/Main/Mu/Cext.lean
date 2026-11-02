import MlDsaOptGlam44.Fn.Sponge.Cext
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/Mu/Cext.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# `cext` in place (`dst = KS`)

`hash_mu` extracts slot 1 of the kf4 image copied to `KS` into `KS` itself
(`cext 25, 1, 0`). The contract `cext_call` asks `KS + 800 ≤ dst`; in place,
lane `x` is read before it is written and the later lanes are untouched, so
the same loop gives the same lane values. The block lemmas are those of
`Fn/Sponge/Cext.lean` without the (unused) bound on `dst`.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra
open MlDsaOptGlam44.Proofs.WP4 MlDsaOpt44.Proofs.WP4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cextIP_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 < n) (hn : n ≤ 25) (hsh : sh < 4) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 19243 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s 19243 (wd (x + 1) :: wd n :: wd sh :: wd dst :: wd ret :: tail)
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      205 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  glam44_rreach [8148, 8149, 8150, 8151, 8152, 8153, 8154, 8155, 8156, 8157, 8158, 8159, 8160, 8161, 8162, 8163, 8164, 8165, 8166, 8167, 8168, 8169, 8170, 8171, 8172, 8173, 8174, 8175, 8176, 8177, 8178, 8179, 8180, 8181, 8182, 8183, 8184, 8185, 8186, 8187, 8188, 8189, 8190, 8191, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8203, 8204, 8205, 8206, 8207, 8208, 8209, 8210, 8211, 8212, 8213] with []
  exact ⟨rfl, by rw [Nat.add_comm]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cextIP_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 = n) (hn : n ≤ 25) (hsh : sh < 4) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 19243 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      221 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8148, 8149, 8150, 8151, 8152, 8153, 8154, 8155, 8156, 8157, 8158, 8159, 8160, 8161, 8162, 8163, 8164, 8165, 8166, 8167, 8168, 8169, 8170, 8171, 8172, 8173, 8174, 8175, 8176, 8177, 8178, 8179, 8180, 8181, 8182, 8183, 8184, 8185, 8186, 8187, 8188, 8189, 8190, 8191, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8203, 8204, 8205, 8206, 8207, 8208, 8209, 8210, 8211, 8212, 8213, 8214, 8215, 8216, 8217, 8218] with [hj]
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
    callState s 19243 (wd k :: wd n :: wd sh :: wd 0 :: wd ret :: tail) (storeWords m 0 g k)
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

end MlDsaOptGlam44.Proofs
