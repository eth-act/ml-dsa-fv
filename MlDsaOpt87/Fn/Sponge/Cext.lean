import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOpt87.Budget
import MlDsaOpt87.Layout
/- Ported from `MlDsaOpt44/Fn/Sponge/Cext.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `cext`: extract the lanes of one slot of a `kf4` state
-/

namespace MlDsaOpt87.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- One compressing stage: `M & (y | y >> k)` (in `opt87_block` normal form). -/
def cstage (k M y : Nat) : Nat := M &&& (y % 2 ^ 256 / 2 ^ k ||| y)

/-- The `cext` compress network on the shifted state word `u`. -/
def compNet (u : Nat) : Nat :=
  cstage 96 0xffffffffffffffff
    (cstage 48 0xffffffff000000000000000000000000ffffffff
      (cstage 24 0xffff000000000000ffff000000000000ffff000000000000ffff
        (cstage 12 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
          (cstage 6 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
            (cstage 3 0x0303030303030303030303030303030303030303030303030303030303030303
              (0x1111111111111111111111111111111111111111111111111111111111111111 &&& u))))))

/-- The word `cext` stores for lane `x` (`u` = state word shifted by the slot). -/
def cextOut (x u : Nat) : Nat :=
  (18446744073709551615 * (1 &&& 1184006 / 2 ^ x) ^^^ compNet u) % 2 ^ 256

theorem spread_M64 : spread M64 = 0x1111111111111111111111111111111111111111111111111111111111111111 := by
  decide +kernel

theorem compNet_lt (u : Nat) : compNet u < 2 ^ 64 := by
  unfold compNet cstage
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)

/-- `compNet` on symbolic bits. -/
def compSym : Nat → List Nat :=
  symCStage 96 0xffffffffffffffff
    (symCStage 48 0xffffffff000000000000000000000000ffffffff
      (symCStage 24 0xffff000000000000ffff000000000000ffff000000000000ffff
        (symCStage 12 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
          (symCStage 6 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
            (symCStage 3 0x0303030303030303030303030303030303030303030303030303030303030303
              (symMask 0x1111111111111111111111111111111111111111111111111111111111111111
                fun j => [j]))))))

theorem compSym_eq : ∀ j, j < 64 → compSym j = [4 * j] ∧
    (0x1111111111111111111111111111111111111111111111111111111111111111 : Nat).testBit (4 * j) =
      true := by
  decide +kernel

theorem compNet_eq (u : Nat) : compNet u = compress (u &&& spread M64) := by
  have hs : ∀ j, (compNet u).testBit j = (compSym j).any u.testBit :=
    symCStage_ok _ _ (symCStage_ok _ _ (symCStage_ok _ _ (symCStage_ok _ _ (symCStage_ok _ _
      (symCStage_ok _ _ (symMask_ok _ fun j => by simp))))))
  apply eq_of_testBit_lt (n := 64) (compNet_lt u) (compress_lt _)
  intro j hj
  obtain ⟨h1, h2⟩ := compSym_eq j hj
  rw [testBit_compress, Nat.testBit_and, spread_M64, hs, h1, h2]
  simp [hj]

theorem xor_M64 {c : Nat} (hc : c < 2 ^ 64) : 18446744073709551615 ^^^ c = 2 ^ 64 - 1 - c := by
  apply eq_of_testBit_lt (n := 64) (Nat.xor_lt_two_pow (by norm_num) hc) (by omega)
  intro j hj
  rw [Nat.testBit_xor, show 2 ^ 64 - 1 - c = 2 ^ 64 - (c + 1) by omega,
    Nat.testBit_two_pow_sub_succ hc, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
    Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem cextOut_eq {x : Nat} (hx : x < 25) (u : Nat) :
    cextOut x u = cpl x (compress (u &&& spread M64)) := by
  unfold cextOut
  rw [compNet_eq]
  have hc := compress_lt (u &&& spread M64)
  generalize compress (u &&& spread M64) = c at hc ⊢
  interval_cases x <;>
    simp only [cpl, complemented, List.mem_cons, List.not_mem_nil, Nat.reducePow, Nat.reduceDiv,
      Nat.reduceAnd, Nat.reduceMul, Nat.mul_zero, Nat.mul_one, Nat.zero_xor, xor_M64 hc,
      Nat.reduceEqDiff, or_false, or_true, false_or, if_true, if_false] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cext_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 < n) (hn : n ≤ 25) (hsh : sh < 4) (_hdst : 800 ≤ dst) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 14182 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s 14182 (wd (x + 1) :: wd n :: wd sh :: wd dst :: wd ret :: tail)
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      205 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  opt87_reach [6299, 6300, 6301, 6302, 6303, 6304, 6305, 6306, 6307, 6308, 6309, 6310, 6311, 6312, 6313, 6314, 6315, 6316, 6317, 6318, 6319, 6320, 6321, 6322, 6323, 6324, 6325, 6326, 6327, 6328, 6329, 6330, 6331, 6332, 6333, 6334, 6335, 6336, 6337, 6338, 6339, 6340, 6341, 6342, 6343, 6344, 6345, 6346, 6347, 6348, 6349, 6350, 6351, 6352, 6353, 6354, 6355, 6356, 6357, 6358, 6359, 6360, 6361, 6362, 6363, 6364] with []
  exact ⟨rfl, by rw [Nat.add_comm]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cext_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) {x n sh dst : Nat}
    (hx : x + 1 = n) (hn : n ≤ 25) (hsh : sh < 4) (hdst : 800 ≤ dst) (hdm : dst + 32 * n ≤ TOP) :
    Reach (callState s 14182 (wd x :: wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (cextOut x (word M (x * 32) / 2 ^ sh)) 32) (dst + x * 32)))
      221 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords, TOP] at hsz hdm
  have hret := hr.small
  have hj := hr.jumpdest
  opt87_reach [6299, 6300, 6301, 6302, 6303, 6304, 6305, 6306, 6307, 6308, 6309, 6310, 6311, 6312, 6313, 6314, 6315, 6316, 6317, 6318, 6319, 6320, 6321, 6322, 6323, 6324, 6325, 6326, 6327, 6328, 6329, 6330, 6331, 6332, 6333, 6334, 6335, 6336, 6337, 6338, 6339, 6340, 6341, 6342, 6343, 6344, 6345, 6346, 6347, 6348, 6349, 6350, 6351, 6352, 6353, 6354, 6355, 6356, 6357, 6358, 6359, 6360, 6361, 6362, 6363, 6364, 6365, 6366, 6367, 6368, 6369] with [hj]
  rfl

theorem cext_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (M : ByteArray) (n sh dst : Nat) :
    Reach (callState s 14180 (wd n :: wd sh :: wd dst :: wd ret :: tail) M)
      (callState s 14182 (wd 0 :: wd n :: wd sh :: wd dst :: wd ret :: tail) M) 3 := by
  have := hr.depth; simp only [Stack.cext, Stack.leaf] at this
  opt87_reach [6297, 6298] with []

theorem cext_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (m : ByteArray) {dst sh n : Nat}
    (hsh : sh < 4) (hn : 1 ≤ n) (hn' : n ≤ 25) (hdst : KS + 800 ≤ dst)
    (hdm : dst + 32 * n ≤ TOP) :
    ∃ m', (∀ x, x < n → word m' (dst + 32 * x) =
        cpl x (compress (word m (KS + 32 * x) / 2 ^ sh &&& spread M64))) ∧
      FrameExcept m m' [(dst, dst + 32 * n)] ∧
      Call s Entry.cext [wd n, wd sh, wd dst] ret tail m [] m' (Gas.cext n) := by
  simp only [KS, Nat.zero_add] at hdst ⊢
  let g : Nat → Nat := fun x => cpl x (compress (word m (32 * x) / 2 ^ sh &&& spread M64))
  have hg : ∀ x, g x < 2 ^ 256 := by
    intro x
    have := compress_lt (word m (32 * x) / 2 ^ sh &&& spread M64)
    simp only [g, cpl]; split <;> omega
  refine ⟨storeWords m dst g n, fun x hx => word_storeWords_get (hg x) hx,
    FrameExcept.storeWords m dst g n, ?_⟩
  let I : Nat → State := fun k =>
    callState s 14182 (wd k :: wd n :: wd sh :: wd dst :: wd ret :: tail) (storeWords m dst g k)
  have hstep : ∀ k, k < 25 → MachineState.writeBytes (storeWords m dst g k)
      (Data.Bytes.natToBytesPadded (cextOut k (word (storeWords m dst g k) (k * 32) / 2 ^ sh)) 32)
      (dst + k * 32) = storeWords m dst g (k + 1) := by
    intro k hk
    rw [storeWords_succ, word_storeWords_out (Or.inl (by omega)), cextOut_eq hk,
      show k * 32 = 32 * k by omega]
  have hbody : ∀ k, k < n - 1 → Reach (I k) (I (k + 1)) 205 := by
    intro k hk
    have h := cext_body hs hr (storeWords m dst g k) (x := k) (n := n) (sh := sh) (dst := dst)
      (by omega) hn' hsh hdst hdm
    rwa [hstep k (by omega)] at h
  have hloop := Reach.loop (I := I) (n - 1) hbody
  have hlast := cext_last hs hr (storeWords m dst g (n - 1)) (x := n - 1) (n := n) (sh := sh)
    (dst := dst) (by omega) hn' hsh hdst hdm
  rw [hstep (n - 1) (by omega), show n - 1 + 1 = n by omega] at hlast
  have hentry := cext_entry hs hr m n sh dst
  rw [call_iff, Entry.cext, Gas.cext]
  refine ((hentry.trans (hloop.trans hlast)).mono (by
    have : (n - 1) * 205 + 205 = n * 205 := by
      rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    omega)).of_eq (by simp) rfl

end MlDsaOpt87.Proofs.WP4
