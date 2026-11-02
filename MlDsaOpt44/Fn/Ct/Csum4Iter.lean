import MlDsaOpt44.Fn.Ct.Csum4Blocks
/-!
# `csum` (v4, WP I): one loop iteration, the loop and the trace of the call
-/

set_option linter.unusedVariables false

namespace MlDsaOpt44.Proofs.CS4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

/-! ## Values of one iteration (start memory `M`, bases read from `m0` at entry) -/

def s1 (m0 M : ByteArray) (bu : Nat) : UInt256 := c4s1 M bu (word m0 40960) (word m0 40992) (word m0 41024) (word m0 41056) (word m0 41088) (word m0 41120) (word m0 41152) (word m0 41184) (word m0 41216) (word m0 41248) (word m0 41280)
def s2 (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := c4s2 M bu cw sp g (s1 m0 M bu)
def s3 (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := c4s3 M bu cw sp g (s2 m0 M bu cw sp g)
/-- The transposed window sum. -/
def sT (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := c4T M bu cw sp g (s3 m0 M bu cw sp g)

/-- Memory after one iteration. -/
def csMem (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
    (Data.Bytes.natToBytesPadded (c4w0 M cw g (sT m0 M bu cw sp g)).toNat 32) sp)
    (Data.Bytes.natToBytesPadded (c4w1 M cw g (sT m0 M bu cw sp g)).toNat 32) (32 + sp))
    (Data.Bytes.natToBytesPadded (c4w2 M cw g (sT m0 M bu cw sp g)).toNat 32) (64 + sp))
    (Data.Bytes.natToBytesPadded (c4w3 M cw g (sT m0 M bu cw sp g)).toNat 32) (96 + sp)

theorem bases_le (m0 : ByteArray) (hb : ∀ i, i < 39 → word m0 (40960 + 32 * i) ≤ 6112) (i : Nat) (hi : i < 11) :
    word m0 (40960 + 32 * i) ≤ 6112 := hb i (by omega)

theorem cs_iter {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963)
    (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hb : ∀ i, i < 39 → word m0 (40960 + 32 * i) ≤ 6112)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) (hlt : cw + 128 < 20480) :
    Reach (callState s 14876 (wd bu :: wd cw :: g :: wd sp :: wd (word m0 41280) :: wd (word m0 41248) :: wd (word m0 41216) :: wd (word m0 41184) :: wd (word m0 41152) :: wd (word m0 41120) :: wd (word m0 41088) :: wd (word m0 41056) :: wd (word m0 41024) :: wd (word m0 40992) :: wd (word m0 40960) :: rest) M)
      (callState s 14876 (wd (bu - 32) :: wd (128 + cw) :: c4g4 M cw g :: wd (128 + sp) :: wd (word m0 41280) :: wd (word m0 41248) :: wd (word m0 41216) :: wd (word m0 41184) :: wd (word m0 41152) :: wd (word m0 41120) :: wd (word m0 41088) :: wd (word m0 41056) :: wd (word m0 41024) :: wd (word m0 40992) :: wd (word m0 40960) :: rest)
        (csMem m0 M bu cw sp g)) 1008 :=
  ((((c4_b1 hs hrest M bu cw sp g (bases_le m0 hb 0 (by norm_num)) (bases_le m0 hb 1 (by norm_num)) (bases_le m0 hb 2 (by norm_num)) (bases_le m0 hb 3 (by norm_num)) (bases_le m0 hb 4 (by norm_num)) (bases_le m0 hb 5 (by norm_num)) (bases_le m0 hb 6 (by norm_num)) (bases_le m0 hb 7 (by norm_num)) (bases_le m0 hb 8 (by norm_num)) (bases_le m0 hb 9 (by norm_num)) (bases_le m0 hb 10 (by norm_num)) hbu hbu2 hcw hcw2 hsp hsp2 hB).trans
    (c4_b2 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (c4_b3 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (c4_b4 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (c4_b5 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hlt)

theorem cs_iterx {s : State} (hs : Ctx s) {rest : List UInt256} (hrest : rest.length ≤ 963)
    (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256)
    (hbu : 20480 - 2016 ≤ bu) (hbu2 : bu ≤ 20480) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 26624 ≤ sp) (hsp2 : sp + 128 ≤ 26624 + 8192)
    (hb : ∀ i, i < 39 → word m0 (40960 + 32 * i) ≤ 6112)
    (hB : ∀ m, m < 39 → word M (40960 + 32 * m) ≤ 6112) (hlt : cw + 128 = 20480) :
    Reach (callState s 14876 (wd bu :: wd cw :: g :: wd sp :: wd (word m0 41280) :: wd (word m0 41248) :: wd (word m0 41216) :: wd (word m0 41184) :: wd (word m0 41152) :: wd (word m0 41120) :: wd (word m0 41088) :: wd (word m0 41056) :: wd (word m0 41024) :: wd (word m0 40992) :: wd (word m0 40960) :: rest) M)
      (callState s 15441 (wd (bu - 32) :: wd (128 + cw) :: c4g4 M cw g :: wd (128 + sp) :: wd (word m0 41280) :: wd (word m0 41248) :: wd (word m0 41216) :: wd (word m0 41184) :: wd (word m0 41152) :: wd (word m0 41120) :: wd (word m0 41088) :: wd (word m0 41056) :: wd (word m0 41024) :: wd (word m0 40992) :: wd (word m0 40960) :: rest)
        (csMem m0 M bu cw sp g)) 1008 :=
  ((((c4_b1 hs hrest M bu cw sp g (bases_le m0 hb 0 (by norm_num)) (bases_le m0 hb 1 (by norm_num)) (bases_le m0 hb 2 (by norm_num)) (bases_le m0 hb 3 (by norm_num)) (bases_le m0 hb 4 (by norm_num)) (bases_le m0 hb 5 (by norm_num)) (bases_le m0 hb 6 (by norm_num)) (bases_le m0 hb 7 (by norm_num)) (bases_le m0 hb 8 (by norm_num)) (bases_le m0 hb 9 (by norm_num)) (bases_le m0 hb 10 (by norm_num)) hbu hbu2 hcw hcw2 hsp hsp2 hB).trans
    (c4_b2 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (c4_b3 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (c4_b4 hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hB)).trans
    (c4_b5x hs hrest M bu cw sp g _ hbu hbu2 hcw hcw2 hsp hsp2 hlt)

/-! ## The loop -/

/-- Memory and `g` after `u` iterations. -/
def stU (m : ByteArray) : Nat → ByteArray × UInt256
  | 0 => (m, c4e m)
  | u + 1 => (csMem m (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u) (stU m u).2,
      c4g4 (stU m u).1 (12288 + 128 * u) (stU m u).2)

theorem csMem_other (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a + 32 ≤ sp ∨ sp + 128 ≤ a) : word (csMem m0 M bu cw sp g) a = word M a := by
  simp (disch := omega) only [csMem, word_mstore_disjoint]

theorem byteAt_csMem (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a < sp ∨ sp + 128 ≤ a) : byteAt (csMem m0 M bu cw sp g) a = byteAt M a := by
  simp (disch := (rw [natToBytesPadded_size]; omega)) only [csMem, byteAt_writeBytes_of_not_mem]

theorem stU_other (m : ByteArray) {a : Nat} (h : a + 32 ≤ 26624 ∨ 26624 + 8192 ≤ a) :
    ∀ u, u ≤ 64 → word (stU m u).1 a = word m a
  | 0, _ => rfl
  | u + 1, hu => by
    show word (csMem _ _ _ _ _ _) a = _
    rw [csMem_other _ _ _ _ _ _ (by omega), stU_other m h u (by omega)]

theorem stU_byte (m : ByteArray) {a : Nat} (h : a < 26624 ∨ 26624 + 8192 ≤ a) :
    ∀ u, u ≤ 64 → byteAt (stU m u).1 a = byteAt m a
  | 0, _ => rfl
  | u + 1, hu => by
    show byteAt (csMem _ _ _ _ _ _) a = _
    rw [byteAt_csMem _ _ _ _ _ _ (by omega), stU_byte m h u (by omega)]

theorem cs_run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (m : ByteArray)
    (hB : ∀ i, i < 39 → word m (40960 + 32 * i) ≤ 6112) :
    Reach (callState s 14762 (wd 26624 :: wd 20480 :: wd ret :: tail) m)
      (callState s ret tail (stU m 64).1) (102 + (63 * 1008 + 1008) + 42) := by
  have hrest : (wd 26624 :: wd 20480 :: wd ret :: tail).length ≤ 963 := by simp; omega
  have hBu : ∀ u, u ≤ 64 → ∀ i, i < 39 → word (stU m u).1 (40960 + 32 * i) ≤ 6112 := fun u hu i hi => by
    rw [stU_other m (by omega) u hu]; exact hB i hi
  have hstep : ∀ u, u < 63 → Reach
      (callState s 14876 (wd (20480 - 32 * u) :: wd (12288 + 128 * u) :: (stU m u).2 :: wd (26624 + 128 * u) ::
        wd (word m 41280) :: wd (word m 41248) :: wd (word m 41216) :: wd (word m 41184) :: wd (word m 41152) :: wd (word m 41120) :: wd (word m 41088) :: wd (word m 41056) :: wd (word m 41024) :: wd (word m 40992) :: wd (word m 40960) :: wd 26624 :: wd 20480 :: wd ret :: tail) (stU m u).1)
      (callState s 14876 (wd (20480 - 32 * (u + 1)) :: wd (12288 + 128 * (u + 1)) :: (stU m (u + 1)).2 ::
        wd (26624 + 128 * (u + 1)) :: wd (word m 41280) :: wd (word m 41248) :: wd (word m 41216) :: wd (word m 41184) :: wd (word m 41152) :: wd (word m 41120) :: wd (word m 41088) :: wd (word m 41056) :: wd (word m 41024) :: wd (word m 40992) :: wd (word m 40960) :: wd 26624 :: wd 20480 :: wd ret :: tail) (stU m (u + 1)).1) 1008 := by
    intro u hu
    have h := cs_iter hs hrest m (stU m u).1 (20480 - 32 * u) (12288 + 128 * u) (26624 + 128 * u)
      (stU m u).2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hB (hBu u (by omega)) (by omega)
    rw [show 20480 - 32 * u - 32 = 20480 - 32 * (u + 1) by omega,
      show 128 + (12288 + 128 * u) = 12288 + 128 * (u + 1) by omega,
      show 128 + (26624 + 128 * u) = 26624 + 128 * (u + 1) by omega] at h
    exact h
  have hloop := Reach.loop (I := fun u => callState s 14876 (wd (20480 - 32 * u) :: wd (12288 + 128 * u) ::
    (stU m u).2 :: wd (26624 + 128 * u) :: wd (word m 41280) :: wd (word m 41248) :: wd (word m 41216) :: wd (word m 41184) :: wd (word m 41152) :: wd (word m 41120) :: wd (word m 41088) :: wd (word m 41056) :: wd (word m 41024) :: wd (word m 40992) :: wd (word m 40960) :: wd 26624 :: wd 20480 :: wd ret :: tail) (stU m u).1) 63 hstep
  have hlast := cs_iterx hs hrest m (stU m 63).1 (20480 - 32 * 63) (12288 + 128 * 63)
    (26624 + 128 * 63) (stU m 63).2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hB (hBu 63 (by omega)) (by omega)
  exact (((c4_entry hs (by simp; omega) m 26624 20480).trans (hloop.of_eq rfl rfl)).trans hlast).trans
    (c4_exit hs htail hj hret _ _ _ _ _ _ _)

end MlDsaOpt44.Proofs.CS4
