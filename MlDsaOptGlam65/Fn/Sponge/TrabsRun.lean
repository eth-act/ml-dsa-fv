import MlDsaOpt44.Fn.Sponge.TrabsZip
import MlDsaOptGlam65.Infra.Reflect
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Sponge/TrabsRun.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Sponge/TrabsRun.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `trabs` (v4): entry, loop body, last (masked) group with exit, contract

One loop iteration per calldata word: `CALLDATALOAD`, the mask on the last
group, the seven-stage network `trabsNet` (`TrabsZip.lean`), and four lanes
XORed into `kp + 32 j`. The block lemmas keep the network in the form
`glam65_block` leaves it, folded by `dsw_fold*`.
-/

namespace MlDsaOptGlam65.Proofs.WP4

open MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs.WP4
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

theorem dsw_fold16 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536)) * 65536 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536) ^^^ x = dsw 16 U x := rfl
theorem dsw_fold6 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 64)) * 64 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 64) ^^^ x = dsw 6 U x := rfl
theorem dsw_fold34 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 17179869184)) * 17179869184 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 17179869184) ^^^ x = dsw 34 U x := rfl
theorem dsw_fold126 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 85070591730234615865843651857942052864)) * 85070591730234615865843651857942052864 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 85070591730234615865843651857942052864) ^^^ x = dsw 126 U x := rfl
theorem dsw_fold3 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 8)) * 8 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 8) ^^^ x = dsw 3 U x := rfl
theorem dsw_fold15 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 32768)) * 32768 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 32768) ^^^ x = dsw 15 U x := rfl
theorem dsw_fold63 (U x : Nat) :
    (U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 9223372036854775808)) * 9223372036854775808 ^^^ U &&& (x ^^^ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 9223372036854775808) ^^^ x = dsw 63 U x := rfl
theorem dsw_fold16w (U : Nat) (m : ByteArray) (a : Nat) :
    (U &&& (word m a ^^^ word m a / 65536)) * 65536 ^^^ U &&& (word m a ^^^ word m a / 65536) ^^^ word m a =
      dsw 16 U (word m a) := by
  rw [← dsw_fold16, word_mod]
theorem trabsNet_fold (x : Nat) :
    dsw 63 tzU6 (dsw 15 tzU5 (dsw 3 tzU4 (dsw 126 tzU3 (dsw 34 tzU2 (dsw 6 tzU1 (dsw 16 tzU0 x)))))) =
      trabsNet x := rfl

theorem trabs4_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) (kp lm n4 sh off : Nat) :
    Reach (callState s 18543 (wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 18775 (wd tzS0 :: wd tzU6 :: wd tzU5 :: wd tzU4 :: wd tzU3 :: wd tzU2 :: wd tzU1 :: wd tzU0 :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M) 25 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  glam65_rreach [7941, 7942, 7943, 7944, 7945, 7946, 7947, 7948, 7949] with [tzS0, tzU0, tzU1, tzU2, tzU3, tzU4, tzU5, tzU6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs4_mid {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm n4 sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hn4 : 2 ≤ n4) (hn4' : n4 ≤ 25) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 18775 (wd tzS0 :: wd tzU6 :: wd tzU5 :: wd tzU4 :: wd tzU3 :: wd tzU2 :: wd tzU1 :: wd tzU0 :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 18775 (wd tzS0 :: wd tzU6 :: wd tzU5 :: wd tzU4 :: wd tzU3 :: wd tzU2 :: wd tzU1 :: wd tzU0 :: wd (128 + kp) :: wd lm :: wd (n4 - 1) :: wd sh :: wd (32 + off) :: wd ret :: tail)
        (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 8) * 2 ^ sh ^^^ word M kp) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) kp)
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 4) * 2 ^ sh ^^^ word M (32 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + kp))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 2) * 2 ^ sh ^^^ word M (64 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + kp))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (word s.executionEnv.calldata off)) * 2 ^ sh ^^^ word M (96 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + kp))) 529 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  glam65_rreach [7950, 7951, 7952, 7953, 7954, 7955, 7956, 7957, 7958, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974, 7975, 7976, 7977, 7978, 7979, 7980, 7981, 7982, 7983, 7984, 7985, 7986, 7987, 7988, 7989, 7990, 7991, 7992, 7993, 7994, 7995, 7996, 7997, 7998, 7999, 8000, 8001, 8002, 8003, 8004, 8005, 8006, 8007, 8008, 8009, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020, 8021, 8022, 8023, 8024, 8025, 8026, 8027, 8028, 8029, 8030, 8031, 8032, 8033, 8034, 8035, 8036, 8037, 8038, 8039, 8040, 8041, 8042, 8043, 8044, 8045, 8046, 8047, 8048, 8049, 8050, 8051, 8052, 8053, 8054, 8055, 8056, 8057, 8058, 8059, 8060, 8061, 8062, 8063, 8064, 8065, 8066, 8067, 8068, 8069, 8070, 8071, 8072, 8073, 8074, 8075, 8076, 8077, 8078, 8079, 8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090, 8091, 8092, 8093, 8094, 8095, 8096, 8097, 8098, 8099, 8100, 8101, 8102, 8103, 8104, 8105, 8106, 8107, 8108, 8109, 8110, 8111, 8112, 8113, 8114, 8115, 8116, 8117, 8118, 8119, 8120, 8121, 8122, 8123, 8124] with [word_mstore_disjoint, dsw_fold16, dsw_fold6, dsw_fold34, dsw_fold126, dsw_fold3, dsw_fold15, dsw_fold63, dsw_fold16w, trabsNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs4_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hlm : lm < 2 ^ 256) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 18775 (wd tzS0 :: wd tzU6 :: wd tzU5 :: wd tzU4 :: wd tzU3 :: wd tzU2 :: wd tzU1 :: wd tzU0 :: wd kp :: wd lm :: wd 1 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (lm &&& word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 8) * 2 ^ sh ^^^ word M kp) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) kp)
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (lm &&& word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 4) * 2 ^ sh ^^^ word M (32 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + kp))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (lm &&& word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 2) * 2 ^ sh ^^^ word M (64 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + kp))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet (lm &&& word s.executionEnv.calldata off)) * 2 ^ sh ^^^ word M (96 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + kp))) 569 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  glam65_rreach [7950, 7951, 7952, 7953, 7954, 7955, 7956, 7957, 7958, 7959, 7960, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974, 7975, 7976, 7977, 7978, 7979, 7980, 7981, 7982, 7983, 7984, 7985, 7986, 7987, 7988, 7989, 7990, 7991, 7992, 7993, 7994, 7995, 7996, 7997, 7998, 7999, 8000, 8001, 8002, 8003, 8004, 8005, 8006, 8007, 8008, 8009, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020, 8021, 8022, 8023, 8024, 8025, 8026, 8027, 8028, 8029, 8030, 8031, 8032, 8033, 8034, 8035, 8036, 8037, 8038, 8039, 8040, 8041, 8042, 8043, 8044, 8045, 8046, 8047, 8048, 8049, 8050, 8051, 8052, 8053, 8054, 8055, 8056, 8057, 8058, 8059, 8060, 8061, 8062, 8063, 8064, 8065, 8066, 8067, 8068, 8069, 8070, 8071, 8072, 8073, 8074, 8075, 8076, 8077, 8078, 8079, 8080, 8081, 8082, 8083, 8084, 8085, 8086, 8087, 8088, 8089, 8090, 8091, 8092, 8093, 8094, 8095, 8096, 8097, 8098, 8099, 8100, 8101, 8102, 8103, 8104, 8105, 8106, 8107, 8108, 8109, 8110, 8111, 8112, 8113, 8114, 8115, 8116, 8117, 8118, 8119, 8120, 8121, 8122, 8123, 8124, 8125, 8126, 8127, 8128, 8129, 8130, 8131, 8132, 8133, 8134, 8135, 8136, 8137, 8138] with [word_mstore_disjoint, dsw_fold16, dsw_fold6, dsw_fold34, dsw_fold126, dsw_fold3, dsw_fold15, dsw_fold63, dsw_fold16w, trabsNet_fold, hj]

theorem trabs4_lane {m M cd : ByteArray} {off lm n4 sh kp i a W : Nat} (j : Nat) (hj : j < 4)
    (hsh : sh < 4) (hlm : lm < 2 ^ 256) (hlmL : ∀ k, k < 4 → lane lm k = 0 ∨ lane lm k = M64)
    (hw : word M a = word m (kp + 32 * (4 * i + j)))
    (hW : W = if i + 1 = n4 then lm &&& word cd (off + 32 * i) else word cd (off + 32 * i))
    (hWlt : W < 2 ^ 256)
    (L : Nat) (hL : L = tzS0 &&& trabsNet W % 2 ^ 256 / 2 ^ (3 - j)) :
    (L * 2 ^ sh ^^^ word M a) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      word m (kp + 32 * (4 * i + j)) ^^^ spread (trLane cd off lm n4 (4 * i + j)) * 2 ^ sh := by
  have hT : L = spread (trLane cd off lm n4 (4 * i + j)) := by
    rw [hL, trabsNet_lane hWlt hj, trLane_eq cd off lm n4 i hj, hW]
    split
    · rw [bswapNet_and_lane (word_lt _ _) hlm hlmL]
    · rfl
  rw [hT, hw, Nat.xor_comm,
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (word_lt _ _) (spread_sh_lt hsh))]

theorem trabs4_T_lt (m cd : ByteArray) (kp off lm n4 sh : Nat) (hsh : sh < 4) (u : Nat) :
    word m (kp + 32 * u) ^^^ spread (trLane cd off lm n4 u) * 2 ^ sh < 2 ^ 256 :=
  Nat.xor_lt_two_pow (word_lt _ _) (spread_sh_lt hsh)

set_option maxHeartbeats 4000000 in
theorem trabs_call_v4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (m : ByteArray) {off sh n4 lm kp : Nat}
    (hoff : off < 2 ^ 64) (hsh : sh < 4) (hn4 : 1 ≤ n4) (hlm : lm < 2 ^ 256)
    (hlmL : ∀ k, k < 4 → lane lm k = 0 ∨ lane lm k = M64)
    (hkp : kp + 128 * n4 ≤ KS + 800) (hkp' : KS ≤ kp) (hkp32 : kp % 32 = 0) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        if kp ≤ KS + 32 * x ∧ KS + 32 * x < kp + 128 * n4 then
          word m (KS + 32 * x) ^^^
            spread (trLane s.executionEnv.calldata off lm n4 ((KS + 32 * x - kp) / 32)) * 2 ^ sh
        else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(kp, kp + 128 * n4)] ∧
      Call s Entry.trabs [wd kp, wd lm, wd n4, wd sh, wd off] ret tail m [] m' (Gas.trabs n4) := by
  simp only [KS, Nat.zero_add] at hkp hkp' ⊢
  have hstep : ∀ i, i < n4 → ∀ W, (W = if i + 1 = n4 then lm &&& word s.executionEnv.calldata (off + 32 * i)
        else word s.executionEnv.calldata (off + 32 * i)) →
      (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet W % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 8) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (kp + 128 * i)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (kp + 128 * i))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet W % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 4) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (32 + (kp + 128 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + (kp + 128 * i)))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet W % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 2) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (64 + (kp + 128 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + (kp + 128 * i)))
          (Data.Bytes.natToBytesPadded (((tzS0 &&& trabsNet W) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (96 + (kp + 128 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + (kp + 128 * i))) =
      storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * (i + 1)) := by
    intro i hi W hW
    have hWlt : W < 2 ^ 256 := by
      rw [hW]; split
      · exact Nat.lt_of_le_of_lt Nat.and_le_left hlm
      · exact word_lt _ _
    conv_rhs => rw [show 4 * (i + 1) = 4 * i + 3 + 1 by ring, storeWords_succ, storeWords_succ,
      storeWords_succ, storeWords_succ]
    refine wbc (wbc (wbc (wbc rfl ?v0 (by ring)) ?v1 (by ring)) ?v2 (by ring)) ?v3 (by ring)
    case v0 =>
      refine trabs4_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
        (kp := kp) (i := i) 0 (by norm_num) hsh hlm hlmL ?_ hW hWlt _ (by norm_num)
      rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
    case v1 =>
      refine trabs4_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
        (kp := kp) (i := i) 1 (by norm_num) hsh hlm hlmL ?_ hW hWlt _ (by norm_num)
      rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
    case v2 =>
      refine trabs4_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
        (kp := kp) (i := i) 2 (by norm_num) hsh hlm hlmL ?_ hW hWlt _ (by norm_num)
      rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
    case v3 =>
      refine trabs4_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
        (kp := kp) (i := i) 3 (by norm_num) hsh hlm hlmL ?_ hW hWlt _ (by rw [Nat.sub_self, pow_zero, Nat.div_one, Nat.mod_eq_of_lt (trabsNet_lt hWlt)])
      rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
  let I : Nat → State := fun i => callState s 18775 (wd tzS0 :: wd tzU6 :: wd tzU5 :: wd tzU4 :: wd tzU3 :: wd tzU2 :: wd tzU1 :: wd tzU0 :: wd (kp + 128 * i) :: wd lm :: wd (n4 - i) :: wd sh :: wd (off + 32 * i) :: wd ret :: tail)
    (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i))
  have hbody : ∀ i, i < n4 - 1 → Reach (I i) (I (i + 1)) 529 := by
    intro i hi
    have h := trabs4_mid hs hr (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (kp := kp + 128 * i) (lm := lm) (n4 := n4 - i) (sh := sh)
      (off := off + 32 * i) (by omega) hsh (by omega) (by omega) (by omega)
    rw [hstep i (by omega) _ (by rw [if_neg (by omega)]), show 128 + (kp + 128 * i) = kp + 128 * (i + 1) by ring,
      show n4 - i - 1 = n4 - (i + 1) by omega, show 32 + (off + 32 * i) = off + 32 * (i + 1) by ring] at h
    exact h
  have hlast := trabs4_last hs hr (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * (n4 - 1))) (kp := kp + 128 * (n4 - 1))
    (lm := lm) (sh := sh) (off := off + 32 * (n4 - 1)) (by omega) hsh hlm (by omega)
  rw [hstep (n4 - 1) (by omega) _ (by rw [if_pos (by omega)]), show n4 - 1 + 1 = n4 by omega] at hlast
  have hloop := Reach.loop (I := I) (n4 - 1) hbody
  have hI : I (n4 - 1) = callState s 18775 (wd tzS0 :: wd tzU6 :: wd tzU5 :: wd tzU4 :: wd tzU3 :: wd tzU2 :: wd tzU1 :: wd tzU0 :: wd (kp + 128 * (n4 - 1)) :: wd lm :: wd 1 :: wd sh :: wd (off + 32 * (n4 - 1)) :: wd ret :: tail)
      (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * (n4 - 1))) := by
    simp only [I, show n4 - (n4 - 1) = 1 by omega]
  rw [hI] at hloop
  have hentry := trabs4_entry hs hr m kp lm n4 sh off
  refine ⟨storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * n4), fun x hx => ?_,
    storeWords_mono_frame (le_refl _) (by omega), ?_⟩
  · split
    · rename_i hin
      have e : kp + 32 * ((32 * x - kp) / 32) = 32 * x := by omega
      have h := word_storeWords_get (m := m) (base := kp) (k := 4 * n4) (i := (32 * x - kp) / 32)
        (v := (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh))
        (trabs4_T_lt m s.executionEnv.calldata kp off lm n4 sh hsh ((32 * x - kp) / 32)) (by omega)
      beta_reduce at h
      rw [e] at h
      exact h
    · exact word_storeWords_out (by omega)
  · rw [call_iff, Entry.trabs, Gas.trabs]
    have hentry' : Reach (callState s 18543 (wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) m)
        (I 0) 25 := by
      simp only [I, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, storeWords_zero]; exact hentry
    have htot := hentry'.trans (hloop.trans hlast)
    refine (htot.mono ?_).of_eq rfl rfl
    have : (n4 - 1) * 529 + 569 = 529 * n4 + 40 := by
      have : n4 = (n4 - 1) + 1 := by omega
      rw [this]; simp only [Nat.add_sub_cancel]; ring
    omega

end MlDsaOptGlam65.Proofs.WP4
