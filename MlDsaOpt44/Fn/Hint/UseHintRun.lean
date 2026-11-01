import MlDsaOpt44.Fn.Hint.UseHint
/-!
# `usehint` (WP10): blocks, loop and the contract body

Entry (13 gas), 256 visits of the loop body (219 gas each; `uh_body` stores `uhW` at
`ACC + 32t`), exit (12 gas): `13 + 256 · 219 + 12 = 56089 = Gas.usehint`.
-/

namespace MlDsaOpt44.Proofs.UH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.L10

theorem uh_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 15457 (wd 43264 :: wd ret :: tail) M)
      (callState s 15464 (wd 43264 :: wd 51456 :: wd ret :: tail) M) 13 := by
  opt44_reach [6934, 6935, 6936, 6937, 6938]

theorem uh_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (wp : Nat) (hwp : 43264 ≤ wp) (hwe : wp + 32 < 51456) :
    Reach (callState s 15464 (wd wp :: wd 51456 :: wd ret :: tail) M)
      (callState s 15464 (wd (32 + wp) :: wd 51456 :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          (uhW (word M wp) (word M (wp - 16640)) (word M (8192 + wp))).toNat 32) wp)) 219 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946, 6947, 6948, 6949, 6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006] with [uhW, uhF, uhV, uhD, uhR, uhQ, uhX]

theorem uh_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 15464 (wd 51424 :: wd 51456 :: wd ret :: tail) M)
      (callState s 15736 (wd 51456 :: wd 51456 :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          (uhW (word M 51424) (word M 34784) (word M 59616)).toNat 32) 51424)) 219 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt44_reach [6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946, 6947, 6948, 6949, 6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004, 7005, 7006] with [uhW, uhF, uhV, uhD, uhR, uhQ, uhX]

set_option maxRecDepth 100000 in
theorem uh_ret {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hj : Decode.isValidJumpDest optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) :
    Reach (callState s 15736 (wd 51456 :: wd 51456 :: wd ret :: tail) M) (callState s ret tail M) 12 := by
  opt44_reach [7007, 7008, 7009] with [hj]

/-- Value stored at `ACC + 32 t`. -/
def uv (M : ByteArray) (t : Nat) : Nat :=
  (uhW (word M (ACC + 32 * t)) (word M (SP + 32 * t)) (word M (HP + 32 * t))).toNat

/-- Memory after `j` iterations. -/
def Mj (M : ByteArray) (j : Nat) : ByteArray := storeWords M ACC (uv M) j

theorem Mj_reads (M : ByteArray) {j a : Nat}
    (h2 : a + 32 ≤ ACC ∨ ACC + 32 * j ≤ a) : word (Mj M j) a = word M a :=
  FrameExcept.word (FrameExcept.storeWords M ACC (uv M) j)
    (by simp only [avoids_cons, avoids_nil, and_true]; omega)

theorem uh_step {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (j : Nat) (hj : j + 1 < 256) :
    Reach (callState s 15464 (wd (43264 + 32 * j) :: wd 51456 :: wd ret :: tail) (Mj M j))
      (callState s 15464 (wd (43264 + 32 * (j + 1)) :: wd 51456 :: wd ret :: tail) (Mj M (j + 1)))
      219 := by
  have hb := uh_body hs (ret := ret) htail (Mj M j) (43264 + 32 * j) (by omega) (by omega)
  rw [Mj_reads M (a := 43264 + 32 * j) (by unfold ACC; omega),
    Mj_reads M (a := 43264 + 32 * j - 16640) (by unfold ACC; omega),
    Mj_reads M (a := 8192 + (43264 + 32 * j)) (by unfold ACC; omega)] at hb
  refine hb.of_eq rfl ?_
  have e1 : 32 + (43264 + 32 * j) = 43264 + 32 * (j + 1) := by omega
  have e2 : Mj M (j + 1) = MachineState.writeBytes (Mj M j)
      (Data.Bytes.natToBytesPadded (uv M j) 32) (43264 + 32 * j) := by
    unfold Mj; rw [storeWords_succ, show ACC + j * 32 = 43264 + 32 * j by unfold ACC; omega]
  rw [e1, e2]
  unfold uv
  rw [show ACC + 32 * j = 43264 + 32 * j by unfold ACC; omega,
    show SP + 32 * j = 43264 + 32 * j - 16640 by unfold SP; omega,
    show HP + 32 * j = 8192 + (43264 + 32 * j) by unfold HP; omega]

theorem uv_spec (m : ByteArray) {t : Nat}
    (h : ∀ r, r < 4 → lane (word m (ACC + 32 * t)) r < 2 ^ 27 ∧ lane (word m (SP + 32 * t)) r < 2 ^ 29 ∧
      lane (word m (HP + 32 * t)) r ≤ 1) {r : Nat} (hr : r < 4) :
    lane (uv m t) r = (Fips204.useHint (lane (word m (HP + 32 * t)) r)
      ((lane (word m (ACC + 32 * t)) r : Int) - lane (word m (SP + 32 * t)) r)).toNat := by
  have key := uhW_pack (a := fun r => lane (word m (ACC + 32 * t)) r)
    (b := fun r => lane (word m (SP + 32 * t)) r) (c := fun r => lane (word m (HP + 32 * t)) r)
    (fun r hr => (h r hr).1) (fun r hr => (h r hr).2.1) (fun r hr => (h r hr).2.2)
  rw [pk_lanes (word_lt _ _), pk_lanes (word_lt _ _), pk_lanes (word_lt _ _)] at key
  have hl : Lanes fun r => uhLane (lane (word m (ACC + 32 * t)) r) (lane (word m (SP + 32 * t)) r)
      (lane (word m (HP + 32 * t)) r) := fun r hr =>
    Nat.lt_trans (uhLane_lt (h r hr).1 (h r hr).2.1 (h r hr).2.2) (by norm_num)
  unfold uv
  rw [key, toNat_ofNat_of_lt (pk_lt hl), pk_lane hl hr]
  exact uhLane_spec (h r hr).1 (h r hr).2.1 (h r hr).2.2

theorem toNat_lt' (x : UInt256) : x.toNat < 2 ^ 256 := x.val.isLt

theorem uv_lt (m : ByteArray) (t : Nat) : uv m t < 2 ^ 256 := by unfold uv; exact toNat_lt' _

theorem Mj_word (m : ByteArray) {t : Nat} (ht : t < 256) : word (Mj m 256) (ACC + 32 * t) = uv m t :=
  word_storeWords (uv_lt m t) 256 ht

theorem Mj_last (m : ByteArray) : MachineState.writeBytes (Mj m 255) (Data.Bytes.natToBytesPadded
    (uhW (word m 51424) (word m 34784) (word m 59616)).toNat 32) 51424 = Mj m 256 := by
  have e : Mj m 256 = MachineState.writeBytes (Mj m 255)
      (Data.Bytes.natToBytesPadded (uv m 255) 32) (ACC + 255 * 32) := storeWords_succ _ _ _ _
  rw [e]
  simp only [uv, ACC, SP, HP, Nat.reduceMul, Nat.reduceAdd]

theorem usehint_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m (ACC + 32 * t)) r < 2 ^ 27 ∧ lane (word m (SP + 32 * t)) r < 2 ^ 29 ∧
          lane (word m (HP + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m' (ACC + 32 * t)) r =
          (Fips204.useHint (lane (word m (HP + 32 * t)) r)
            ((lane (word m (ACC + 32 * t)) r : Int) - lane (word m (SP + 32 * t)) r)).toNat) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.usehint [wd ACC] ret tail m [] m' Gas.usehint := by
  have htail : tail.length ≤ 960 := by have := hr.depth; simp only [Stack.usehint, Stack.leaf] at this; omega
  refine ⟨Mj m 256, fun t ht h r hr' => ?_, ?_, ?_⟩
  · rw [Mj_word m ht]
    exact uv_spec m h hr'
  · have h := FrameExcept.storeWords m ACC (uv m) 256
    exact h
  · have hloop := Reach.loop (I := fun j => callState s 15464
      (wd (43264 + 32 * j) :: wd 51456 :: wd ret :: tail) (Mj m j)) 255
      (fun j hj => uh_step hs htail m j (by omega))
    have hent := uh_entry hs (ret := ret) htail m
    have hlast := uh_last hs (ret := ret) htail (Mj m 255)
    rw [Mj_reads m (a := 51424) (by unfold ACC; omega), Mj_reads m (a := 34784) (by unfold ACC; omega),
      Mj_reads m (a := 59616) (by unfold ACC; omega)] at hlast
    have hfin := uh_ret hs htail hr.jumpdest hr.small (Mj m 256)
    rw [Mj_last] at hlast
    rw [call_iff, Entry.usehint, Gas.usehint]
    have hall := ((hent.trans (hloop.of_eq rfl rfl)).trans hlast).trans hfin
    exact hall.mono (by norm_num)

end MlDsaOpt44.Proofs.UH
