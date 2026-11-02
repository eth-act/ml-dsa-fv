import MlDsaOpt65.Fn.Hint.G5Pure
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
set_option warningAsError true
/-!
# `pack` (ML-DSA-87): block lemmas and one loop iteration

`pack [nr, F, B, ret]` (`F = FIN + 256 + 2048 g`, `B = ACC + 0x2000 g`, `nr ∈ {2, 4}`): entry
`[nr, F, B, B + 0x2000]` (19 gas), 16 iterations `i` (`pk_A`: `x = OR_k word(B + 512 i + 32 k) << 4k`,
327 gas; `pk_B4` / `pk_B2`: lane `r < nr` of `x`, replicated, to `F + 32 i + 512 r`, 249 / 185 gas),
exit (16 gas): `19 + 16 · 576 + 16 = 9251`, `19 + 16 · 512 + 16 = 8227` (`Gas.pack nr`).
-/

namespace MlDsaOpt87.Proofs.G5PK

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt65.Proofs.G5H
open MlDsaOpt44.Proofs.PK (Xl)

/-- The stores of one iteration for `nr = 2`. -/
def wr2 (M : ByteArray) (x : UInt256) (fp : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (pw0 x).toNat 32) fp)
    (Data.Bytes.natToBytesPadded (pw1 x).toNat 32) (512 + fp)

/-- The stores of one iteration for `nr = 4`. -/
def wr4 (M : ByteArray) (x : UInt256) (fp : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (wr2 M x fp)
    (Data.Bytes.natToBytesPadded (pw2 x).toNat 32) (1024 + fp))
    (Data.Bytes.natToBytesPadded (pw3 x).toNat 32) (1536 + fp)

def wrN (nr : Nat) (M : ByteArray) (x : UInt256) (fp : Nat) : ByteArray :=
  if nr ≤ 2 then wr2 M x fp else wr4 M x fp

/-- Gas of one iteration. -/
def cI (nr : Nat) : Nat := if nr ≤ 2 then 512 else 576

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem pk_entry (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr F B : Nat) :
    Reach (callState s 17273 (wd nr :: wd F :: wd B :: wd ret :: tail) M)
      (callState s 17282 (wd nr :: wd F :: wd B :: wd (8192 + B) :: wd ret :: tail) M) 19 := by
  opt87_reach [7885, 7886, 7887, 7888, 7889, 7890, 7891]

theorem pk_A (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr wp fp e : Nat)
    (hwp : wp + 512 ≤ 90656) :
    Reach (callState s 17282 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17430 (pkA M wp :: wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M) 327 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7892, 7893, 7894, 7895, 7896, 7897, 7898, 7899, 7900, 7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7933, 7934, 7935, 7936, 7937, 7938, 7939, 7940, 7941, 7942, 7943, 7944, 7945, 7946, 7947, 7948, 7949, 7950, 7951, 7952, 7953, 7954, 7955, 7956, 7957, 7958, 7959, 7960, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974, 7975, 7976, 7977, 7978, 7979, 7980, 7981, 7982, 7983, 7984, 7985, 7986, 7987, 7988, 7989, 7990, 7991, 7992, 7993, 7994, 7995, 7996, 7997, 7998, 7999, 8000, 8001] with [pkA]

theorem pk_B4 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 17430 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17282 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [8002, 8003, 8004, 8005, 8006, 8007, 8008, 8009, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020, 8021, 8022, 8023, 8024, 8025, 8026, 8027, 8028, 8029, 8030, 8031, 8032, 8033, 8034, 8035, 8036, 8037, 8038, 8039, 8040, 8041, 8042, 8043, 8044, 8045, 8046, 8047, 8048, 8049, 8050, 8051, 8052, 8053, 8054, 8055, 8056, 8057, 8058, 8059, 8060, 8061, 8062, 8063, 8064, 8065, 8066, 8067, 8068, 8069, 8070, 8071, 8072, 8073, 8074, 8075] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B4x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 17430 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17651 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt87_reach [8002, 8003, 8004, 8005, 8006, 8007, 8008, 8009, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020, 8021, 8022, 8023, 8024, 8025, 8026, 8027, 8028, 8029, 8030, 8031, 8032, 8033, 8034, 8035, 8036, 8037, 8038, 8039, 8040, 8041, 8042, 8043, 8044, 8045, 8046, 8047, 8048, 8049, 8050, 8051, 8052, 8053, 8054, 8055, 8056, 8057, 8058, 8059, 8060, 8061, 8062, 8063, 8064, 8065, 8066, 8067, 8068, 8069, 8070, 8071, 8072, 8073, 8074, 8075] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B2 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 17430 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17282 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [8002, 8003, 8004, 8005, 8006, 8007, 8008, 8009, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020, 8021, 8022, 8023, 8024, 8025, 8026, 8027, 8028, 8029, 8030, 8031, 8032, 8033, 8045, 8046, 8047, 8048, 8049, 8050, 8051, 8061, 8062, 8063, 8064, 8065, 8066, 8067, 8068, 8069, 8070, 8071, 8072, 8073, 8074, 8075] with [wr2, pw0, pw1, REPc]

theorem pk_B2x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 17430 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17651 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt87_reach [8002, 8003, 8004, 8005, 8006, 8007, 8008, 8009, 8010, 8011, 8012, 8013, 8014, 8015, 8016, 8017, 8018, 8019, 8020, 8021, 8022, 8023, 8024, 8025, 8026, 8027, 8028, 8029, 8030, 8031, 8032, 8033, 8045, 8046, 8047, 8048, 8049, 8050, 8051, 8061, 8062, 8063, 8064, 8065, 8066, 8067, 8068, 8069, 8070, 8071, 8072, 8073, 8074, 8075] with [wr2, pw0, pw1, REPc]

set_option maxRecDepth 100000 in
theorem pk_exit (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (nr a b e : Nat) :
    Reach (callState s 17651 (wd nr :: wd a :: wd b :: wd e :: wd ret :: tail) M)
      (callState s ret tail M) 16 := by
  opt87_reach [8076, 8077, 8078, 8079, 8080] with [hj]

/-- One iteration, loop continues. -/
theorem pk_iter (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 17282 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17282 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2 hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4 hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

/-- The last iteration. -/
theorem pk_iterx (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 17282 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17651 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

end

end MlDsaOpt87.Proofs.G5PK
