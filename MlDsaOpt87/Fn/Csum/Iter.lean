import MlDsaOpt87.Fn.Csum.Blocks
set_option warningAsError true
/-!
# `csum` (v4): the loop and the trace of the call (ML-DSA-87)

As `MlDsaOpt44/Fn/Ct/Csum4Iter.lean` with the table pointer `T` and the output pointer
`S` free (`csum [S, T]`, `(S, T) = (SP, TT)` or `(SP + 0x2000, TT + 0x1800)`). One
iteration (`cs_iter`, `Blocks.lean`) costs 1386.
-/

set_option linter.unusedVariables false

namespace MlDsaOpt87.Proofs.G4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt44.Proofs.CS4 (c4g4)

/-- Memory and the count word after `u` iterations (table at `T`, output at `S`). -/
def stU (m : ByteArray) (T S : Nat) : Nat → ByteArray × UInt256
  | 0 => (m, cse m)
  | u + 1 => (csMem m (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2,
      c4g4 (stU m T S u).1 (12288 + 128 * u) (stU m T S u).2)

theorem csMem_other (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a + 32 ≤ sp ∨ sp + 128 ≤ a) : word (csMem m0 M bu cw sp g) a = word M a := by
  simp (disch := omega) only [csMem, word_mstore_disjoint]

theorem byteAt_csMem (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a < sp ∨ sp + 128 ≤ a) : byteAt (csMem m0 M bu cw sp g) a = byteAt M a := by
  simp (disch := (rw [natToBytesPadded_size]; omega)) only [csMem, byteAt_writeBytes_of_not_mem]

theorem stU_other (m : ByteArray) (T S : Nat) {a : Nat} (h : a + 32 ≤ S ∨ S + 8192 ≤ a) :
    ∀ u, u ≤ 64 → word (stU m T S u).1 a = word m a
  | 0, _ => rfl
  | u + 1, hu => by
    show word (csMem _ _ _ _ _ _) a = _
    rw [csMem_other _ _ _ _ _ _ (by omega), stU_other m T S h u (by omega)]

theorem stU_byte (m : ByteArray) (T S : Nat) {a : Nat} (h : a < S ∨ S + 8192 ≤ a) :
    ∀ u, u ≤ 64 → byteAt (stU m T S u).1 a = byteAt m a
  | 0, _ => rfl
  | u + 1, hu => by
    show byteAt (csMem _ _ _ _ _ _) a = _
    rw [byteAt_csMem _ _ _ _ _ _ (by omega), stU_byte m T S h u (by omega)]

theorem cs_run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (m : ByteArray) {T S : Nat} (hT1 : 2048 ≤ T) (hT2 : T ≤ 26624)
    (hS1 : 32768 ≤ S) (hS2 : S + 8192 ≤ 49152)
    (hB : ∀ i, i < 60 → word m (49152 + 32 * i) ≤ 6112) :
    Reach (callState s 16227 (wd S :: wd T :: wd ret :: tail) m)
      (callState s ret tail (stU m T S 64).1) (102 + (63 * 1386 + 1386) + 42) := by
  have hrest : (wd S :: wd T :: wd ret :: tail).length ≤ 963 := by simp; omega
  have hb0 : ∀ i, i < 11 → word m (49152 + 32 * i) ≤ 6112 := fun i hi => hB i (by omega)
  have hBu : ∀ u, u ≤ 64 → ∀ i, i < 60 → word (stU m T S u).1 (49152 + 32 * i) ≤ 6112 :=
    fun u hu i hi => by rw [stU_other m T S (by omega) u hu]; exact hB i hi
  have hstep : ∀ u, u < 63 → Reach
      (callState s 16341 (wd (T - 32 * u) :: wd (12288 + 128 * u) :: (stU m T S u).2 ::
        wd (S + 128 * u) :: wd (word m 49472) :: wd (word m 49440) :: wd (word m 49408) ::
        wd (word m 49376) :: wd (word m 49344) :: wd (word m 49312) :: wd (word m 49280) ::
        wd (word m 49248) :: wd (word m 49216) :: wd (word m 49184) :: wd (word m 49152) ::
        wd S :: wd T :: wd ret :: tail) (stU m T S u).1)
      (callState s 16341 (wd (T - 32 * (u + 1)) :: wd (12288 + 128 * (u + 1)) :: (stU m T S (u + 1)).2 ::
        wd (S + 128 * (u + 1)) :: wd (word m 49472) :: wd (word m 49440) :: wd (word m 49408) ::
        wd (word m 49376) :: wd (word m 49344) :: wd (word m 49312) :: wd (word m 49280) ::
        wd (word m 49248) :: wd (word m 49216) :: wd (word m 49184) :: wd (word m 49152) ::
        wd S :: wd T :: wd ret :: tail) (stU m T S (u + 1)).1) 1386 := by
    intro u hu
    have h := cs_iter hs hrest m (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u)
      (stU m T S u).2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hBu u (by omega)) hb0 (by omega)
    rw [show T - 32 * u - 32 = T - 32 * (u + 1) by omega,
      show 128 + (12288 + 128 * u) = 12288 + 128 * (u + 1) by omega,
      show 128 + (S + 128 * u) = S + 128 * (u + 1) by omega] at h
    exact h
  have hloop := Reach.loop (I := fun u => callState s 16341 (wd (T - 32 * u) :: wd (12288 + 128 * u) ::
    (stU m T S u).2 :: wd (S + 128 * u) :: wd (word m 49472) :: wd (word m 49440) ::
    wd (word m 49408) :: wd (word m 49376) :: wd (word m 49344) :: wd (word m 49312) ::
    wd (word m 49280) :: wd (word m 49248) :: wd (word m 49216) :: wd (word m 49184) ::
    wd (word m 49152) :: wd S :: wd T :: wd ret :: tail) (stU m T S u).1) 63 hstep
  have hlast := cs_iterx hs hrest m (stU m T S 63).1 (T - 32 * 63) (12288 + 128 * 63)
    (S + 128 * 63) (stU m T S 63).2 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (hBu 63 (by omega)) hb0 (by omega)
  exact (((cs_entry hs (by simp; omega) m S T).trans (hloop.of_eq rfl rfl)).trans hlast).trans
    (cs_exit hs htail hj hret _ _ _ _ _ _ _)

end MlDsaOpt87.Proofs.G4
