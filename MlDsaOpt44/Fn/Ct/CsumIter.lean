import MlDsaOpt44.Fn.Ct.CsumBlocks
/-!
# `csum` (WP10): one loop iteration, the loop and the trace of the call
-/

set_option linter.unusedVariables false

namespace MlDsaOpt44.Proofs.CS

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

/-! ## Values of one iteration (start memory `M`) -/

def s1 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs1o0 M bu cw sp g
def s2 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs2o0 M bu cw sp g (s1 M bu cw sp g)
def s3 (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs3o0 M bu cw sp g (s2 M bu cw sp g)
/-- The transposed window sum. -/
def sT (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs4o0 M bu cw sp g (s3 M bu cw sp g)
/-- `g` after the four positions. -/
def gN (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs5g M bu cw sp g (sT M bu cw sp g)

/-- Memory after one iteration. -/
def csMem (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
    (Data.Bytes.natToBytesPadded (cs5w0 M bu cw sp g (sT M bu cw sp g)).toNat 32) sp)
    (Data.Bytes.natToBytesPadded (cs5w1 M bu cw sp g (sT M bu cw sp g)).toNat 32) (32 + sp))
    (Data.Bytes.natToBytesPadded (cs5w2 M bu cw sp g (sT M bu cw sp g)).toNat 32) (64 + sp))
    (Data.Bytes.natToBytesPadded (cs5w3 M bu cw sp g (sT M bu cw sp g)).toNat 32) (96 + sp)

theorem cs_iter {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) (hlt : cw + 128 < 20480) :
    Reach (callState s 14744 (wd bu :: wd cw :: g :: wd sp :: wd 20480 :: wd ret :: tail) M)
      (callState s 14744 (wd (bu - 32) :: wd (128 + cw) :: gN M bu cw sp g :: wd (128 + sp) :: wd 20480 ::
        wd ret :: tail) (csMem M bu cw sp g)) 1091 :=
  ((((cs_b1 hs htail M bu cw sp g hbu hbu2 hcw hcw2 hsp hsp2 hB).trans
    (cs_b2 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (cs_b3 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (cs_b4 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (cs_b5 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB hlt)

theorem cs_iterx {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) (hlt : cw + 128 = 20480) :
    Reach (callState s 14744 (wd bu :: wd cw :: g :: wd sp :: wd 20480 :: wd ret :: tail) M)
      (callState s 15451 (wd (bu - 32) :: wd (128 + cw) :: gN M bu cw sp g :: wd (128 + sp) :: wd 20480 ::
        wd ret :: tail) (csMem M bu cw sp g)) 1091 :=
  ((((cs_b1 hs htail M bu cw sp g hbu hbu2 hcw hcw2 hsp hsp2 hB).trans
    (cs_b2 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (cs_b3 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (cs_b4 hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (cs_b5x hs htail M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB hlt)

/-! ## The loop -/

/-- Memory and `g` after `u` iterations. -/
def stU (m : ByteArray) : Nat → ByteArray × UInt256
  | 0 => (m, UInt256.ofNat 39 - UInt256.ofNat (word m 4000))
  | u + 1 => (csMem (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2,
      gN (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2)

theorem csMem_other (M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a + 32 ≤ sp ∨ sp + 128 ≤ a) : word (csMem M bu cw sp g) a = word M a := by
  simp (disch := omega) only [csMem, word_mstore_disjoint]

theorem byteAt_csMem (M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a < sp ∨ sp + 128 ≤ a) : byteAt (csMem M bu cw sp g) a = byteAt M a := by
  simp (disch := (rw [natToBytesPadded_size]; omega)) only [csMem, byteAt_writeBytes_of_not_mem]

theorem stU_other (m : ByteArray) {a : Nat} (h : a + 32 ≤ 26624 ∨ 26624 + 8192 ≤ a) :
    ∀ u, u ≤ 64 → word (stU m u).1 a = word m a
  | 0, _ => rfl
  | u + 1, hu => by
    show word (csMem _ _ _ _ _) a = _
    rw [csMem_other _ _ _ _ _ (by omega), stU_other m h u (by omega)]

theorem stU_byte (m : ByteArray) {a : Nat} (h : a < 26624 ∨ 26624 + 8192 ≤ a) :
    ∀ u, u ≤ 64 → byteAt (stU m u).1 a = byteAt m a
  | 0, _ => rfl
  | u + 1, hu => by
    show byteAt (csMem _ _ _ _ _) a = _
    rw [byteAt_csMem _ _ _ _ _ (by omega), stU_byte m h u (by omega)]

theorem cs_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 14732 (wd 26624 :: wd 20480 :: wd ret :: tail) M)
      (callState s 14744 (wd 20480 :: wd 12288 :: (UInt256.ofNat 39 - UInt256.ofNat (word M 4000)) ::
        wd 26624 :: wd 20480 :: wd ret :: tail) M) 19 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6560, 6561, 6562, 6563, 6564, 6565, 6566]

set_option maxRecDepth 100000 in
theorem cs_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) (a b c : Nat) (g : UInt256) :
    Reach (callState s 15451 (wd a :: wd b :: g :: wd c :: wd 20480 :: wd ret :: tail) M)
      (callState s ret tail M) 18 := by
  opt44_reach [6928, 6929, 6930, 6931, 6932, 6933] with [hj]

theorem cs_run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (m : ByteArray)
    (hB : ∀ i, i < 39 → word m (40960 + 32 * i) ≤ 6112) :
    Reach (callState s 14732 (wd 26624 :: wd 20480 :: wd ret :: tail) m)
      (callState s ret tail (stU m 64).1) (19 + (63 * 1091 + 1091) + 18) := by
  have hBu : ∀ u, u ≤ 64 → ∀ i, i < 39 → word (stU m u).1 (40960 + 32 * i) ≤ 6112 := fun u hu i hi => by
    rw [stU_other m (by omega) u hu]; exact hB i hi
  have hstep : ∀ u, u < 63 → Reach
      (callState s 14744 (wd (20480 - 32 * u) :: wd (12288 + 128 * u) :: (stU m u).2 :: wd (26624 + 128 * u) ::
        wd 20480 :: wd ret :: tail) (stU m u).1)
      (callState s 14744 (wd (20480 - 32 * (u + 1)) :: wd (12288 + 128 * (u + 1)) :: (stU m (u + 1)).2 ::
        wd (26624 + 128 * (u + 1)) :: wd 20480 :: wd ret :: tail) (stU m (u + 1)).1) 1091 := by
    intro u hu
    have h := cs_iter hs (ret := ret) htail (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u)
      (stU m u).2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (hBu u (by omega)) (by omega)
    rw [show 20480 - 32 * u - 32 = 20480 - 32 * (u + 1) by omega,
      show 128 + (12288 + 128 * u) = 12288 + 128 * (u + 1) by omega,
      show 128 + (26624 + 128 * u) = 26624 + 128 * (u + 1) by omega] at h
    exact h
  have hloop := Reach.loop (I := fun u => callState s 14744 (wd (20480 - 32 * u) :: wd (12288 + 128 * u) ::
    (stU m u).2 :: wd (26624 + 128 * u) :: wd 20480 :: wd ret :: tail) (stU m u).1) 63 hstep
  have hlast := cs_iterx hs (ret := ret) htail (stU m 63).1 (20480 - 32 * 63) (12288 + 128 * 63)
    (26624 + 128 * 63) (stU m 63).2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hBu 63 (by omega)) (by omega)
  exact (((cs_entry hs htail m).trans (hloop.of_eq rfl rfl)).trans hlast).trans
    (cs_exit hs htail hj hret _ _ _ _ _)

end MlDsaOpt44.Proofs.CS
