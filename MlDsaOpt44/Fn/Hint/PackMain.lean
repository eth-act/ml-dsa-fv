import MlDsaOpt44.Fn.Hint.PackCode
import MlDsaOpt44.Fn.Hint.PackSpec
/-!
# `pack` (WP10): the loop over the eight chunks and the contract body
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOpt44.Proofs.PK

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.L10

/-! ## Memory of one iteration -/

theorem qm2_low (M : ByteArray) (wp fp : Nat) {a : Nat} (h : a + 32 ≤ fp) : word (qm2 M wp fp) a = word M a := by
  simp (disch := omega) only [qm2, word_mstore_disjoint]

theorem qm4_low (M : ByteArray) (wp fp : Nat) {a : Nat} (h : a + 32 ≤ fp) : word (qm4 M wp fp) a = word M a := by
  simp (disch := omega) only [qm4, word_mstore_disjoint, qm2_low M wp fp h]

theorem qm6_low (M : ByteArray) (wp fp : Nat) {a : Nat} (h : a + 32 ≤ fp) : word (qm6 M wp fp) a = word M a := by
  simp (disch := omega) only [qm6, word_mstore_disjoint, qm4_low M wp fp h]

theorem qm6_far (M : ByteArray) (wp fp : Nat) {a y i : Nat} (ha : a = 59904 + 32 * y)
    (hfp : fp = 59904 + 96 * i) (hi : i < 8) (hy : y % 24 / 3 ≠ i) : word (qm6 M wp fp) a = word M a := by
  simp (disch := omega) only [qm6, qm4, qm2, word_mstore_disjoint]

theorem byteAt_qm6 (M : ByteArray) (wp fp : Nat) {a : Nat} (h : a < fp ∨ fp + 2400 ≤ a) :
    byteAt (qm6 M wp fp) a = byteAt M a := by
  simp (disch := (rw [natToBytesPadded_size]; omega)) only [qm6, qm4, qm2, byteAt_writeBytes_of_not_mem]

theorem Aw_qm2 (M : ByteArray) {wp fp : Nat} (h : wp + 1024 ≤ fp) {n r : Nat} (hn : n < 32) :
    Aw (qm2 M wp fp) wp n r = Aw M wp n r := by
  unfold Aw; rw [qm2_low M wp fp (by omega)]

theorem Aw_qm4 (M : ByteArray) {wp fp : Nat} (h : wp + 1024 ≤ fp) {n r : Nat} (hn : n < 32) :
    Aw (qm4 M wp fp) wp n r = Aw M wp n r := by
  unfold Aw; rw [qm4_low M wp fp (by omega)]

/-- The twelve stored words of an iteration, read back. -/
theorem qm6_hit (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    (h : wp + 1024 ≤ fp) {k r : Nat} (hk : k < 3) (hr : r < 4) :
    ∃ X, word (qm6 M wp fp) (fp + 32 * k + 768 * r) = rep X ∧ X < 2 ^ 64 ∧
      ∀ b, b < 64 → X.testBit b = (Aw M wp ((64 * k + b) / 6) r).testBit ((64 * k + b) % 6) := by
  have hq2 : ∀ n r, n < 32 → Aw (qm2 M wp fp) wp n r = Aw M wp n r := fun n r hn => Aw_qm2 M h hn
  have hq4 : ∀ n r, n < 32 → Aw (qm4 M wp fp) wp n r = Aw M wp n r := fun n r hn => Aw_qm4 M h hn
  have hX : ∀ V j, Xl V j < 2 ^ 64 := fun V j => Nat.mod_lt _ (by positivity)
  interval_cases k <;> interval_cases r
  · refine ⟨Xl (q2o0 M wp fp) 0, ?_, hX _ _, fun b hb => by simpa using v0_bits M wp fp hA (j := 0) (by omega) hb⟩
    rw [show fp + 32 * 0 + 768 * 0 = fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane0 _
  · refine ⟨Xl (q2o0 M wp fp) 1, ?_, hX _ _, fun b hb => by simpa using v0_bits M wp fp hA (j := 1) (by omega) hb⟩
    rw [show fp + 32 * 0 + 768 * 1 = 768 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane _ (by norm_num) (by norm_num)
  · refine ⟨Xl (q2o0 M wp fp) 2, ?_, hX _ _, fun b hb => by simpa using v0_bits M wp fp hA (j := 2) (by omega) hb⟩
    rw [show fp + 32 * 0 + 768 * 2 = 1536 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane _ (by norm_num) (by norm_num)
  · refine ⟨Xl (q2o0 M wp fp) 3, ?_, hX _ _, fun b hb => by simpa using v0_bits M wp fp hA (j := 3) (by omega) hb⟩
    rw [show fp + 32 * 0 + 768 * 3 = 2304 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane3 _
  · refine ⟨Xl (q4o0 M wp fp) 0, ?_, hX _ _, fun b hb => by simpa using v1_bits M wp fp hA hq2 (j := 0) (by omega) hb⟩
    rw [show fp + 32 * 1 + 768 * 0 = 32 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane0 _
  · refine ⟨Xl (q4o0 M wp fp) 1, ?_, hX _ _, fun b hb => by simpa using v1_bits M wp fp hA hq2 (j := 1) (by omega) hb⟩
    rw [show fp + 32 * 1 + 768 * 1 = 800 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane _ (by norm_num) (by norm_num)
  · refine ⟨Xl (q4o0 M wp fp) 2, ?_, hX _ _, fun b hb => by simpa using v1_bits M wp fp hA hq2 (j := 2) (by omega) hb⟩
    rw [show fp + 32 * 1 + 768 * 2 = 1568 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane _ (by norm_num) (by norm_num)
  · refine ⟨Xl (q4o0 M wp fp) 3, ?_, hX _ _, fun b hb => by simpa using v1_bits M wp fp hA hq2 (j := 3) (by omega) hb⟩
    rw [show fp + 32 * 1 + 768 * 3 = 2336 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane3 _
  · refine ⟨Xl (q5o0 M wp fp) 0, ?_, hX _ _, fun b hb => by simpa using v2_bits M wp fp hA hq2 hq4 (j := 0) (by omega) hb⟩
    rw [show fp + 32 * 2 + 768 * 0 = 64 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane0 _
  · refine ⟨Xl (q5o0 M wp fp) 1, ?_, hX _ _, fun b hb => by simpa using v2_bits M wp fp hA hq2 hq4 (j := 1) (by omega) hb⟩
    rw [show fp + 32 * 2 + 768 * 1 = 832 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane _ (by norm_num) (by norm_num)
  · refine ⟨Xl (q5o0 M wp fp) 2, ?_, hX _ _, fun b hb => by simpa using v2_bits M wp fp hA hq2 hq4 (j := 2) (by omega) hb⟩
    rw [show fp + 32 * 2 + 768 * 2 = 1600 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane _ (by norm_num) (by norm_num)
  · refine ⟨Xl (q5o0 M wp fp) 3, ?_, hX _ _, fun b hb => by simpa using v2_bits M wp fp hA hq2 hq4 (j := 3) (by omega) hb⟩
    rw [show fp + 32 * 2 + 768 * 3 = 2368 + fp by omega]
    simp (disch := first | omega | exact u_toNat_lt _) only [qm6, qm4, qm2, word_mstore_disjoint, word_mstore]
    exact st_lane3 _

/-! ## The loop -/

/-- Memory after `i` chunks. -/
def Mi (m : ByteArray) : Nat → ByteArray
  | 0 => m
  | i + 1 => qm6 (Mi m i) (43264 + 1024 * i) (59904 + 96 * i)

theorem Mi_low (m : ByteArray) {a : Nat} (h : a + 32 ≤ 59904) : ∀ i, word (Mi m i) a = word m a
  | 0 => rfl
  | i + 1 => by
    show word (qm6 (Mi m i) _ _) a = _
    rw [qm6_low _ _ _ (by omega), Mi_low m h i]

theorem Mi_far (m : ByteArray) {y i' : Nat} (hi' : i' < 8) (hy : y % 24 / 3 = i') :
    ∀ i, i' + 1 ≤ i → i ≤ 8 → word (Mi m i) (59904 + 32 * y) = word (Mi m (i' + 1)) (59904 + 32 * y)
  | 0, h1, _ => by omega
  | i + 1, h1, h2 => by
    by_cases hi : i' + 1 = i + 1
    · rw [hi]
    · show word (qm6 (Mi m i) _ _) _ = _
      rw [qm6_far _ _ _ rfl rfl (by omega) (by omega), Mi_far m hi' hy i (by omega) (by omega)]

theorem Mi_byte (m : ByteArray) {a : Nat} (h : a < 59904 ∨ 62976 ≤ a) :
    ∀ i, i ≤ 8 → byteAt (Mi m i) a = byteAt m a
  | 0, _ => rfl
  | i + 1, hi => by
    show byteAt (qm6 (Mi m i) _ _) a = _
    rw [byteAt_qm6 _ _ _ (by omega), Mi_byte m h i (by omega)]

theorem pk_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 15808 (wd 4 :: wd 59904 :: wd 43264 :: wd ret :: tail) M)
      (callState s 15817 (wd 4 :: wd 59904 :: wd 43264 :: wd 51456 :: wd ret :: tail) M) 19 := by
  opt44_reach [7021, 7022, 7023, 7024, 7025, 7026, 7027]

set_option maxRecDepth 100000 in
theorem pk_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) (a b : Nat) :
    Reach (callState s 16892 (wd 4 :: wd a :: wd b :: wd 51456 :: wd ret :: tail) M)
      (callState s ret tail M) 16 := by
  opt44_reach [7468, 7469, 7470, 7471, 7472] with [hj]

theorem pk_loop {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (m : ByteArray) :
    Reach (callState s 15817 (wd 4 :: wd 59904 :: wd 43264 :: wd 51456 :: wd ret :: tail) m)
      (callState s 16892 (wd 4 :: wd (96 + (59904 + 96 * 7)) :: wd (1024 + (43264 + 1024 * 7)) :: wd 51456 ::
        wd ret :: tail) (Mi m 8)) (7 * 1384 + 1384) := by
  have hstep : ∀ i, i < 7 → Reach
      (callState s 15817 (wd 4 :: wd (59904 + 96 * i) :: wd (43264 + 1024 * i) :: wd 51456 :: wd ret :: tail)
        (Mi m i))
      (callState s 15817 (wd 4 :: wd (59904 + 96 * (i + 1)) :: wd (43264 + 1024 * (i + 1)) :: wd 51456 ::
        wd ret :: tail) (Mi m (i + 1))) 1384 := by
    intro i hi
    have h := pk_iter hs (ret := ret) htail (Mi m i) (43264 + 1024 * i) (59904 + 96 * i)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show 96 + (59904 + 96 * i) = 59904 + 96 * (i + 1) by ring,
      show 1024 + (43264 + 1024 * i) = 43264 + 1024 * (i + 1) by ring] at h
    exact h
  have hloop := Reach.loop (I := fun i => callState s 15817 (wd 4 :: wd (59904 + 96 * i) ::
    wd (43264 + 1024 * i) :: wd 51456 :: wd ret :: tail) (Mi m i)) 7 hstep
  have hlast := pk_iterx hs (ret := ret) htail (Mi m 7) (43264 + 1024 * 7) (59904 + 96 * 7)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  exact (hloop.of_eq rfl rfl).trans hlast

theorem lanesPoly_get' (m : ByteArray) (base k : Nat) {t : Nat} (ht : t < 256) :
    (lanesPoly m base k)[t]! = (lane (word m (base + 32 * t)) k : Int) := by
  simp [lanesPoly, getElem!_pos, ht]

theorem pack_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pack ret tail) (m : ByteArray) :
    ∃ m', ((∀ t, t < 256 → ∀ r, r < 4 → lane (word m (ACC + 32 * t)) r < 64) →
        ∀ r, r < 4 → ∀ j, j < 24 → word m' (FIN + 256 + 32 * (24 * r + j)) =
          rep (le64 (Fips204.simpleBitPack (lanesPoly m ACC r) 43) (8 * j))) ∧
      FrameExcept m m' [(FIN + 256, FIN + 256 + 3072)] ∧
      Call s Entry.pack [wd 4, wd (FIN + 256), wd ACC] ret tail m [] m' Gas.pack := by
  have htail : tail.length ≤ 960 := by have := hr.depth; simp only [Stack.pack, Stack.leaf] at this; omega
  refine ⟨Mi m 8, fun hA r hr' j hj => ?_, fun a ha => ?_, ?_⟩
  · -- chunk `i' = j / 3`, stream word `k = j % 3`
    have hi' : j / 3 < 8 := by omega
    have hk : j % 3 < 3 := Nat.mod_lt _ (by omega)
    have haddr : FIN + 256 + 32 * (24 * r + j) = 59904 + 32 * (24 * r + j) := by unfold FIN; omega
    rw [haddr, Mi_far m hi' (by omega) 8 (by omega) le_rfl]
    have hA' : ∀ n r', n < 32 → r' < 4 → Aw (Mi m (j / 3)) (43264 + 1024 * (j / 3)) n r' < 64 := by
      intro n r' hn hr2
      unfold Aw
      rw [Mi_low m (by omega)]
      have := hA (32 * (j / 3) + n) (by omega) r' hr2
      rwa [show ACC + 32 * (32 * (j / 3) + n) = 32 * n + (43264 + 1024 * (j / 3)) by unfold ACC; omega] at this
    obtain ⟨X, hw, hX, hbits⟩ := qm6_hit (Mi m (j / 3)) (43264 + 1024 * (j / 3)) (59904 + 96 * (j / 3)) hA'
      (by omega) hk hr'
    show word (qm6 (Mi m (j / 3)) _ _) _ = _
    rw [show 59904 + 32 * (24 * r + j) = 59904 + 96 * (j / 3) + 32 * (j % 3) + 768 * r by omega, hw]
    congr 1
    apply eq_of_testBit_lt hX (le64_lt _ _)
    intro b hb
    rw [hbits b hb, le64_sbp_testBit _ hj, decide_eq_true hb, Bool.true_and,
      lanesPoly_get' m ACC r (by omega), Int.toNat_natCast]
    unfold Aw
    rw [Mi_low m (by omega),
      show 32 * ((64 * (j % 3) + b) / 6) + (43264 + 1024 * (j / 3)) = ACC + 32 * ((64 * j + b) / 6) by
        unfold ACC; omega,
      show (64 * (j % 3) + b) % 6 = (64 * j + b) % 6 by omega]
  · have h : a < 59904 ∨ 62976 ≤ a := by
      have := ha (FIN + 256, FIN + 256 + 3072) (by simp)
      simp only [FIN] at this; omega
    exact Mi_byte m h 8 le_rfl
  · rw [call_iff, Entry.pack, Gas.pack]
    have h := ((pk_entry hs (ret := ret) htail m).trans (pk_loop hs htail m)).trans
      (pk_exit hs htail hr.jumpdest hr.small (Mi m 8) _ _)
    refine (h.mono (by norm_num)).of_eq ?_ rfl
    simp [FIN, ACC]

end MlDsaOpt44.Proofs.PK
