import MlDsa44.Proofs.Main.Prelude
import MlDsa44.Proofs.Main.Data
import MlDsa44.Proofs.Bridge
import MlDsa44.Proofs.Gas
set_option warningAsError true
/-!
# Round constants, zetas, `tr` and `μ`

From the sized frame (pc 4766) to the return of the `μ` absorption
(pc 5112): the RC table, `initZetas()`, `calldatacopy(PK, 0, 1312)`,
`tr = shake256(pk, 64)` at `MSGIN`, `tr ‖ 0 ‖ 0 ‖ M` at `MSGIN`, and
`μ = shake256(tr ‖ 0 ‖ 0 ‖ M, 64)` at `W1`.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.Infra

/-- `[lo, hi)` avoids the listed ranges: unfold the layout and decide. -/
macro "avoid" : tactic => `(tactic| (simp only [MlDsa44.Proofs.Infra.avoids_cons,
  MlDsa44.Proofs.Infra.avoids_nil, MlDsa44.Proofs.Infra.avoids_append, List.cons_append,
  List.nil_append, and_true, ST, BT, CT, RC, ZETA, POLY, ZH, CH, AP, ACC, TP,
  HB, XOF, SEEDA, SEEDC, PADB, W1, PK, MSGIN]; omega))

/-- The message field of EIP-8355 calldata. -/
def msgOf (cd : ByteArray) : ByteArray := cd.extract 3732 cd.size

/-- `tr = H(pk, 64)`. -/
def trOf (cd : ByteArray) : ByteArray := Fips204.H (pkOf cd) 64

/-- `μ = H(tr ‖ 0 ‖ 0 ‖ M, 64)` (empty context string). -/
def muOf (cd : ByteArray) : ByteArray :=
  Fips204.H (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) 64

theorem H_size (msg : ByteArray) (n : Nat) : (Fips204.H msg n).size = n := by
  unfold Fips204.H Fips202.shake256 Fips202.shake
  rw [ByteArray.size_extract, squeeze_size _ _ _ (Or.inl rfl)]
  have : n ≤ (n + 136 - 1) / 136 * 136 := by omega
  omega

/-- The first `n` bytes of a one-or-more-block SHAKE256 squeeze. -/
theorem bytesAt_H {m : ByteArray} {out : Nat} {msg : ByteArray} {blocks n : Nat}
    (h : BytesAt m out (Fips202.squeeze 136 (Fips202.absorb 136 (Fips202.pad 136 0x1F msg)) blocks))
    (hn : n ≤ blocks * 136) : BytesAt m out (Fips204.H msg n) := by
  have := h.extract n
  rwa [squeeze_extract_eq_shake 136 msg n blocks (Or.inl rfl) hn] at this

theorem retOK_top {B ret : Nat} {tail : List UInt256}
    (hj : Decode.isValidJumpDest referenceBytecode ret = true) (hret : ret < 2 ^ 16)
    (hB : tail.length + B ≤ 1024) : RetOK B ret tail := ⟨hj, hret, hB⟩

/-- Cost from the sized frame to the return of the `μ` absorption. -/
def hashCost (mlen : Nat) : Nat :=
  230 + Gas.initZetas + 9 + 126 + 29 + Gas.shake 136 1312 1 + 44 + (3 + 3 * ((mlen + 31) / 32)) +
    35 + Gas.shake 136 (66 + mlen) 1


theorem pk_blockA {s : State} (hs : Ctx s) (mlen : Nat) (M : ByteArray) :
    Reach (callState s 5026 [wd mlen] M)
      (callState s 5035 [wd PK, wd 0, wd 1312, wd mlen] M) 9 := by
  evm_reach [3233, 3234, 3235, 3236] with [PK]

theorem pk_blockB {s : State} (hs : Ctx s) (mlen : Nat) (M : ByteArray) :
    Reach (callState s 5036 [wd mlen] M)
      (callState s 2680 [wd 136, wd PK, wd 1312, wd MSGIN, wd 1, wd 5058, wd mlen] M) 29 := by
  evm_reach [3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245] with [PK, MSGIN]

theorem msg_blockA {s : State} (hs : Ctx s) {mlen : Nat}
    (hW : MSGIN + mlen + 288 ≤ 32 * s.activeWords.toNat) (M : ByteArray) :
    Reach (callState s 5058 [wd mlen] M)
      (callState s 5088 [wd (MSGIN + 66), wd 3732, wd mlen, wd mlen]
        (MachineState.writeBytes (MachineState.writeBytes M (ByteArray.mk #[UInt8.ofNat 0])
          (MSGIN + 64)) (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 65))) 44 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold MSGIN at hW ⊢
  evm_reach [3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261]

theorem msg_blockB {s : State} (hs : Ctx s) {mlen : Nat}
    (hmlen : mlen + 3732 = s.executionEnv.calldata.size) (M : ByteArray) :
    Reach (callState s 5089 [wd mlen] M)
      (callState s 2680 [wd 136, wd MSGIN, wd (66 + mlen), wd W1, wd 1, wd 5112, wd mlen] M) 35 := by
  have hml : mlen < 18446744073709551616 := by have := hs.calldataFits; omega
  evm_reach [3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272] with [MSGIN, W1]

/-- Bytes of `tr ‖ 0 ‖ 0 ‖ M` after the two `mstore8`s and the message copy. -/
theorem msgin_bytes {M4 cd : ByteArray} {mlen : Nat} (hmlen : mlen + 3732 = cd.size)
    (htr : BytesAt M4 MSGIN (trOf cd)) :
    BytesAt (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M4
        (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 64)) (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 65))
        (MachineState.readPadded cd 3732 mlen) (MSGIN + 66))
      MSGIN (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) := by
  have hsz : (MachineState.readPadded cd 3732 mlen).size = mlen := by simp
  have htrs : (trOf cd).size = 64 := H_size _ _
  rw [bytesAt_append, bytesAt_append, htrs]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [htrs] at hi
    rw [byteAt_writeBytes_of_not_mem (by rw [hsz]; omega),
      byteAt_writeBytes_single_ne _ _ (by omega), byteAt_writeBytes_single_ne _ _ (by omega)]
    exact htr i (by rw [htrs]; exact hi)
  · change i < 2 at hi
    rw [byteAt_writeBytes_of_not_mem (by rw [hsz]; omega)]
    interval_cases i
    · rw [byteAt_writeBytes_single_ne _ _ (by omega), Nat.add_zero, byteAt_writeBytes_single]; rfl
    · rw [show MSGIN + 64 + 1 = MSGIN + 65 by omega, byteAt_writeBytes_single]; rfl
  · have h := bytesAt_calldatacopy (MachineState.writeBytes (MachineState.writeBytes M4
        (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 64)) (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 65))
      cd (MSGIN + 66) 3732 mlen (by omega)
    rw [show 3732 + mlen = cd.size by omega] at h
    exact h

theorem msgOf_size {cd : ByteArray} {mlen : Nat} (hmlen : mlen + 3732 = cd.size) :
    (msgOf cd).size = mlen := by
  simp [msgOf, ByteArray.size_extract]; omega

theorem pkOf_size {cd : ByteArray} (h : 3732 ≤ cd.size) : (pkOf cd).size = 1312 := by
  simp [pkOf, ByteArray.size_extract]; omega

theorem hash_phase {s : State} (hs : Ctx s) {mlen : Nat}
    (hmlen : mlen + 3732 = s.executionEnv.calldata.size)
    (hW : MSGIN + mlen + 288 ≤ 32 * s.activeWords.toNat) (M : ByteArray) :
    ∃ M', RCTable M' ∧ ZetaTable M' ∧ BytesAt M' W1 (muOf s.executionEnv.calldata) ∧
      Reach (callState s 4766 [wd mlen] M) (callState s 5112 [wd mlen] M') (hashCost mlen) := by
  have hfit := hs.calldataFits
  -- round constants and zetas
  obtain ⟨M1, hrc1, -, hR1⟩ := rc_blocks hs mlen M
  obtain ⟨M2, hz2, hf2, hC2⟩ := initZetas_call hs
    (retOK_top (ret := 5026) (tail := [wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.initZetas, Stack.brv8, Stack.leaf])) M1
  have hR2 : Reach (callState s 3003 [wd 5026, wd mlen] M1) (callState s 5026 [wd mlen] M2)
      Gas.initZetas := (Infra.call_iff.mp hC2).of_eq (by simp [Entry.initZetas]) (by simp)
  have hrc2 := RCTable.frame hrc1 hf2 (by avoid)
  -- pk copy
  have hR3 : Reach (callState s 5035 [wd PK, wd 0, wd 1312, wd mlen] M2)
      (callState s 5036 [wd mlen]
        (MachineState.writeBytes M2 (MachineState.readPadded s.executionEnv.calldata 0 1312) PK))
      126 := by
    have := reach_calldatacopy hs 3237 (pc := 5035) (d := PK) (src := 0) (n := 1312)
      (rest := [wd mlen]) (m := M2) (by simp only [finVal_lit, instrAt_lit])
      (by simp only [finVal_lit, pcAt_lit]) (by unfold PK; norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by unfold PK MSGIN at *; omega) (by simp)
    exact this
  generalize hM3 : MachineState.writeBytes M2 (MachineState.readPadded s.executionEnv.calldata 0 1312) PK
    = M3 at hR3
  have hf3 : FrameExcept M2 M3 [(PK, PK + 1312)] := by
    rw [← hM3]; simpa using FrameExcept.writeBytes M2 (MachineState.readPadded s.executionEnv.calldata 0 1312) PK
  have hpk : BytesAt M3 PK (pkOf s.executionEnv.calldata) := by
    rw [← hM3]; exact bytesAt_calldatacopy M2 _ PK 0 1312 (by omega)
  have hpkr : MachineState.readPadded M3 PK 1312 = pkOf s.executionEnv.calldata := by
    have := readPadded_of_bytesAt hpk
    rwa [pkOf_size (by omega)] at this
  have hrc3 := RCTable.frame hrc2 hf3 (by avoid)
  have hz3 := ZetaTable.frame hz2 hf3 (by avoid)
  -- tr
  obtain ⟨M4, hb4, hf4, hC4⟩ := shake_call hs
    (retOK_top (ret := 5058) (tail := [wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.shake, Stack.keccakF, Stack.xorBlock, Stack.loadLE64, Stack.storeLE64,
        Stack.bswap64, Stack.leaf]))
    (m := M3) (rate := 136) (ptr := PK) (len := 1312) (out := MSGIN) (blocks := 1)
    (Or.inl rfl) (by norm_num) hrc3 (by unfold ZETA PK; omega) (by unfold PADB PK; omega)
    (by unfold ZETA MSGIN; omega) (by unfold PADB MSGIN; omega) (by unfold PK MSGIN; omega)
    (by unfold PK MSGIN at *; omega)
  have hR4 : Reach (callState s 2680 [wd 136, wd PK, wd 1312, wd MSGIN, wd 1, wd 5058, wd mlen] M3)
      (callState s 5058 [wd mlen] M4) (Gas.shake 136 1312 1) :=
    (Infra.call_iff.mp hC4).of_eq (by simp [Entry.shake]) (by simp)
  rw [hpkr] at hb4
  have htr : BytesAt M4 MSGIN (trOf s.executionEnv.calldata) := bytesAt_H hb4 (by norm_num)
  have hrc4 := RCTable.frame hrc3 hf4 (by avoid)
  have hz4 := ZetaTable.frame hz3 hf4 (by avoid)
  -- tr ‖ 0 ‖ 0 ‖ M
  have hR5 := msg_blockA hs hW M4
  have hR6 := reach_calldatacopy hs 3262 (pc := 5088) (d := MSGIN + 66) (src := 3732) (n := mlen)
      (rest := [wd mlen]) (m := MachineState.writeBytes (MachineState.writeBytes M4
        (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 64)) (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 65))
      (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
      (by unfold MSGIN; omega) (by norm_num) (by omega) (by norm_num) (by omega) (by simp)
  have hmsg := msgin_bytes (M4 := M4) hmlen htr
  generalize hM6 : MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M4
      (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 64)) (ByteArray.mk #[UInt8.ofNat 0]) (MSGIN + 65))
      (MachineState.readPadded s.executionEnv.calldata 3732 mlen) (MSGIN + 66) = M6 at hR6 hmsg
  have hf6 : FrameExcept M4 M6 [(MSGIN + 64, MSGIN + 66 + mlen)] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ha
    rw [← hM6, byteAt_writeBytes_of_not_mem (by simp; omega),
      byteAt_writeBytes_single_ne _ _ (by omega), byteAt_writeBytes_single_ne _ _ (by omega)]
  have hrc6 := RCTable.frame hrc4 hf6 (by avoid)
  have hz6 := ZetaTable.frame hz4 hf6 (by avoid)
  have hmsgr : MachineState.readPadded M6 MSGIN (66 + mlen) =
      trOf s.executionEnv.calldata ++ (ByteArray.mk #[0, 0] ++ msgOf s.executionEnv.calldata) := by
    have := readPadded_of_bytesAt hmsg
    have htrs : (trOf s.executionEnv.calldata).size = 64 := H_size _ _
    rwa [ByteArray.size_append, ByteArray.size_append, htrs, msgOf_size hmlen,
      show 64 + ((ByteArray.mk #[0, 0]).size + mlen) = 66 + mlen by
        change 64 + (2 + mlen) = 66 + mlen; omega] at this
  have hR7 := msg_blockB hs hmlen M6
  -- μ
  obtain ⟨M8, hb8, hf8, hC8⟩ := shake_call hs
    (retOK_top (ret := 5112) (tail := [wd mlen]) (by simp only [isValidJumpDest_lit]) (by norm_num)
      (by simp [Stack.shake, Stack.keccakF, Stack.xorBlock, Stack.loadLE64, Stack.storeLE64,
        Stack.bswap64, Stack.leaf]))
    (m := M6) (rate := 136) (ptr := MSGIN) (len := 66 + mlen) (out := W1) (blocks := 1)
    (Or.inl rfl) (by norm_num) hrc6 (by unfold ZETA MSGIN; omega) (by unfold PADB MSGIN; omega)
    (by unfold ZETA W1; omega) (by unfold PADB W1; omega) (by unfold W1 MSGIN; omega)
    (by unfold W1 MSGIN at *; omega)
  have hR8 : Reach (callState s 2680 [wd 136, wd MSGIN, wd (66 + mlen), wd W1, wd 1, wd 5112, wd mlen] M6)
      (callState s 5112 [wd mlen] M8) (Gas.shake 136 (66 + mlen) 1) :=
    (Infra.call_iff.mp hC8).of_eq (by simp [Entry.shake]) (by simp)
  rw [hmsgr] at hb8
  refine ⟨M8, RCTable.frame hrc6 hf8 (by avoid), ZetaTable.frame hz6 hf8 (by avoid), bytesAt_H hb8 (by norm_num), ?_⟩
  have h := ((((((((hR1.trans hR2).trans (pk_blockA hs mlen M2)).trans hR3).trans
    (pk_blockB hs mlen M3)).trans hR4).trans hR5).trans hR6).trans hR7).trans hR8
  refine h.mono (le_of_eq ?_)
  unfold hashCost
  omega

end MlDsa44.Proofs.Main
