import MlDsaOpt87.Fn.Csum.Blocks
set_option warningAsError true
/-!
# `csum` (WP G4): one loop iteration, the loop and the trace of the call (ML-DSA-87)

As `MlDsaOpt44/Fn/Ct/CsumIter.lean` with the table pointer `T` and the output pointer
`S` free (`csum [S, T]`, `(S, T) = (SP, TT)` or `(SP + 0x2000, TT + 0x1800)`).
-/

set_option linter.unusedVariables false

namespace MlDsaOpt87.Proofs.G4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt44.Proofs.CS (cs4o0 cs5g cs5w0 cs5w1 cs5w2 cs5w3)

/-! ## Values of one iteration (start memory `M`) -/

/-- The window sum (all τ loads). -/
def sW (M : ByteArray) (bu : Nat) : UInt256 := ld3 M bu (ld2 M bu (ld1 M bu (ld0 M bu)))
/-- The transposed window sum. -/
def sT (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs4o0 M bu cw sp g (sW M bu)
/-- `g` after the four positions. -/
def gN (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : UInt256 := cs5g M bu cw sp g (sT M bu cw sp g)

/-- Memory after one iteration. -/
def csMem (M : ByteArray) (bu cw sp : Nat) (g : UInt256) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
    (Data.Bytes.natToBytesPadded (cs5w0 M bu cw sp g (sT M bu cw sp g)).toNat 32) sp)
    (Data.Bytes.natToBytesPadded (cs5w1 M bu cw sp g (sT M bu cw sp g)).toNat 32) (32 + sp))
    (Data.Bytes.natToBytesPadded (cs5w2 M bu cw sp g (sT M bu cw sp g)).toNat 32) (64 + sp))
    (Data.Bytes.natToBytesPadded (cs5w3 M bu cw sp g (sT M bu cw sp g)).toNat 32) (96 + sp)

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem cs_body (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp T : Nat)
    (g : UInt256) (hbu1 : 32 ≤ bu) (hbu : bu ≤ 26624) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 32768 ≤ sp) (hsp2 : sp + 128 ≤ 49152)
    (hB : ∀ m, m < 60 → word M (49152 + 32 * m) ≤ 6112) :
    Reach (callState s 16341 (wd bu :: wd cw :: g :: wd sp :: wd T :: wd ret :: tail) M)
      (callState s 16856 (sT M bu cw sp g :: wd bu :: wd cw :: g :: wd sp :: wd T :: wd ret :: tail) M)
      (286 + 288 + 288 + 216 + 72) :=
  ((((cs_b0 hs htail M bu cw sp T g hbu1 hbu hcw hcw2 hsp hsp2 hB).trans
    (cs_b1 hs htail M bu cw sp T g _ hbu1 hbu hcw hcw2 hsp hsp2 hB)).trans
    (cs_b2 hs htail M bu cw sp T g _ hbu1 hbu hcw hcw2 hsp hsp2 hB)).trans
    (cs_b3 hs htail M bu cw sp T g _ hbu1 hbu hcw hcw2 hsp hsp2 hB)).trans
    (cs_tp hs htail M bu cw sp T g _)

theorem cs_iter (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp T : Nat)
    (g : UInt256) (hbu1 : 32 ≤ bu) (hbu : bu ≤ 26624) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 32768 ≤ sp) (hsp2 : sp + 128 ≤ 49152)
    (hB : ∀ m, m < 60 → word M (49152 + 32 * m) ≤ 6112) (hlt : cw + 128 < 20480) :
    Reach (callState s 16341 (wd bu :: wd cw :: g :: wd sp :: wd T :: wd ret :: tail) M)
      (callState s 16341 (wd (bu - 32) :: wd (128 + cw) :: gN M bu cw sp g :: wd (128 + sp) ::
        wd T :: wd ret :: tail) (csMem M bu cw sp g)) 1469 :=
  (cs_body hs htail M bu cw sp T g hbu1 hbu hcw hcw2 hsp hsp2 hB).trans
    (cs_em hs htail M bu cw sp T g _ hbu1 hbu hcw hcw2 hsp hsp2 hB hlt)

theorem cs_iterx (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (bu cw sp T : Nat)
    (g : UInt256) (hbu1 : 32 ≤ bu) (hbu : bu ≤ 26624) (hcw : 12288 ≤ cw) (hcw2 : cw + 128 ≤ 20480)
    (hsp : 32768 ≤ sp) (hsp2 : sp + 128 ≤ 49152)
    (hB : ∀ m, m < 60 → word M (49152 + 32 * m) ≤ 6112) (hlt : cw + 128 = 20480) :
    Reach (callState s 16341 (wd bu :: wd cw :: g :: wd sp :: wd T :: wd ret :: tail) M)
      (callState s 17074 (wd (bu - 32) :: wd (128 + cw) :: gN M bu cw sp g :: wd (128 + sp) ::
        wd T :: wd ret :: tail) (csMem M bu cw sp g)) 1469 :=
  (cs_body hs htail M bu cw sp T g hbu1 hbu hcw hcw2 hsp hsp2 hB).trans
    (cs_emx hs htail M bu cw sp T g _ hbu1 hbu hcw hcw2 hsp hsp2 hB hlt)

end

/-! ## The loop -/

/-- Memory and `g` after `u` iterations (table at `T`, output at `S`). -/
def stU (m : ByteArray) (T S : Nat) : Nat → ByteArray × UInt256
  | 0 => (m, UInt256.ofNat 60 - UInt256.ofNat (word m 4000))
  | u + 1 => (csMem (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2,
      gN (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2)

theorem csMem_other (M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a + 32 ≤ sp ∨ sp + 128 ≤ a) : word (csMem M bu cw sp g) a = word M a := by
  simp (disch := omega) only [csMem, word_mstore_disjoint]

theorem byteAt_csMem (M : ByteArray) (bu cw sp : Nat) (g : UInt256) {a : Nat}
    (h : a < sp ∨ sp + 128 ≤ a) : byteAt (csMem M bu cw sp g) a = byteAt M a := by
  simp (disch := (rw [natToBytesPadded_size]; omega)) only [csMem, byteAt_writeBytes_of_not_mem]

theorem stU_other (m : ByteArray) (T S : Nat) {a : Nat} (h : a + 32 ≤ S ∨ S + 8192 ≤ a) :
    ∀ u, u ≤ 64 → word (stU m T S u).1 a = word m a
  | 0, _ => rfl
  | u + 1, hu => by
    show word (csMem _ _ _ _ _) a = _
    rw [csMem_other _ _ _ _ _ (by omega), stU_other m T S h u (by omega)]

theorem stU_byte (m : ByteArray) (T S : Nat) {a : Nat} (h : a < S ∨ S + 8192 ≤ a) :
    ∀ u, u ≤ 64 → byteAt (stU m T S u).1 a = byteAt m a
  | 0, _ => rfl
  | u + 1, hu => by
    show byteAt (csMem _ _ _ _ _) a = _
    rw [byteAt_csMem _ _ _ _ _ (by omega), stU_byte m T S h u (by omega)]

theorem cs_run {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (m : ByteArray) {T S : Nat} (hT1 : 2048 ≤ T) (hT2 : T ≤ 26624)
    (hS1 : 32768 ≤ S) (hS2 : S + 8192 ≤ 49152)
    (hB : ∀ i, i < 60 → word m (49152 + 32 * i) ≤ 6112) :
    Reach (callState s 16227 (wd S :: wd T :: wd ret :: tail) m)
      (callState s ret tail (stU m T S 64).1) (19 + (63 * 1469 + 1469) + 18) := by
  have hBu : ∀ u, u ≤ 64 → ∀ i, i < 60 → word (stU m T S u).1 (49152 + 32 * i) ≤ 6112 :=
    fun u hu i hi => by rw [stU_other m T S (by omega) u hu]; exact hB i hi
  have hstep : ∀ u, u < 63 → Reach
      (callState s 16341 (wd (T - 32 * u) :: wd (12288 + 128 * u) :: (stU m T S u).2 ::
        wd (S + 128 * u) :: wd T :: wd ret :: tail) (stU m T S u).1)
      (callState s 16341 (wd (T - 32 * (u + 1)) :: wd (12288 + 128 * (u + 1)) :: (stU m T S (u + 1)).2 ::
        wd (S + 128 * (u + 1)) :: wd T :: wd ret :: tail) (stU m T S (u + 1)).1) 1469 := by
    intro u hu
    have h := cs_iter hs (ret := ret) htail (stU m T S u).1 (T - 32 * u) (12288 + 128 * u)
      (S + 128 * u) T (stU m T S u).2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (hBu u (by omega)) (by omega)
    rw [show T - 32 * u - 32 = T - 32 * (u + 1) by omega,
      show 128 + (12288 + 128 * u) = 12288 + 128 * (u + 1) by omega,
      show 128 + (S + 128 * u) = S + 128 * (u + 1) by omega] at h
    exact h
  have hloop := Reach.loop (I := fun u => callState s 16341 (wd (T - 32 * u) :: wd (12288 + 128 * u) ::
    (stU m T S u).2 :: wd (S + 128 * u) :: wd T :: wd ret :: tail) (stU m T S u).1) 63 hstep
  have hlast := cs_iterx hs (ret := ret) htail (stU m T S 63).1 (T - 32 * 63) (12288 + 128 * 63)
    (S + 128 * 63) T (stU m T S 63).2 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (hBu 63 (by omega)) (by omega)
  exact (((cs_entry hs htail m S T).trans (hloop.of_eq rfl rfl)).trans hlast).trans (cs_exit hs htail hj hret _ _ _ _ _ _)

end MlDsaOpt87.Proofs.G4
