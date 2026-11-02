import MlDsaOpt65.Fn.Hint.G5Pure
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Hint/G5PackBlocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# `pack` (ML-DSA-87): block lemmas and one loop iteration

`pack [nr, F, B, ret]` (`F = FIN + 256 + 2048 g`, `B = ACC + 0x2000 g`, `nr ∈ {2, 4}`): entry
`[nr, F, B, B + 0x2000]` (19 gas), 16 iterations `i` (`pk_A`: `x = OR_k word(B + 512 i + 32 k) << 4k`,
327 gas; `pk_B4` / `pk_B2`: lane `r < nr` of `x`, replicated, to `F + 32 i + 512 r`, 249 / 185 gas),
exit (16 gas): `19 + 16 · 576 + 16 = 9251`, `19 + 16 · 512 + 16 = 8227` (`Gas.pack nr`).
-/

namespace MlDsaOptGlam87.Proofs.G5PK

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs MlDsaOpt87.Proofs
open MlDsaOptGlam87.Proofs.Infra
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
    Reach (callState s 22435 (wd nr :: wd F :: wd B :: wd ret :: tail) M)
      (callState s 22444 (wd nr :: wd F :: wd B :: wd (8192 + B) :: wd ret :: tail) M) 19 := by
  glam87_rreach [9928, 9929, 9930, 9931, 9932, 9933, 9934]

theorem pk_A (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr wp fp e : Nat)
    (hwp : wp + 512 ≤ 90656) :
    Reach (callState s 22444 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22592 (pkA M wp :: wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M) 327 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [9935, 9936, 9937, 9938, 9939, 9940, 9941, 9942, 9943, 9944, 9945, 9946, 9947, 9948, 9949, 9950, 9951, 9952, 9953, 9954, 9955, 9956, 9957, 9958, 9959, 9960, 9961, 9962, 9963, 9964, 9965, 9966, 9967, 9968, 9969, 9970, 9971, 9972, 9973, 9974, 9975, 9976, 9977, 9978, 9979, 9980, 9981, 9982, 9983, 9984, 9985, 9986, 9987, 9988, 9989, 9990, 9991, 9992, 9993, 9994, 9995, 9996, 9997, 9998, 9999, 10000, 10001, 10002, 10003, 10004, 10005, 10006, 10007, 10008, 10009, 10010, 10011, 10012, 10013, 10014, 10015, 10016, 10017, 10018, 10019, 10020, 10021, 10022, 10023, 10024, 10025, 10026, 10027, 10028, 10029, 10030, 10031, 10032, 10033, 10034, 10035, 10036, 10037, 10038, 10039, 10040, 10041, 10042, 10043, 10044] with [pkA]

theorem pk_B4 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 22592 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22444 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [10045, 10046, 10047, 10048, 10049, 10050, 10051, 10052, 10053, 10054, 10055, 10056, 10057, 10058, 10059, 10060, 10061, 10062, 10063, 10064, 10065, 10066, 10067, 10068, 10069, 10070, 10071, 10072, 10073, 10074, 10075, 10076, 10077, 10078, 10079, 10080, 10081, 10082, 10083, 10084, 10085, 10086, 10087, 10088, 10089, 10090, 10091, 10092, 10093, 10094, 10095, 10096, 10097, 10098, 10099, 10100, 10101, 10102, 10103, 10104, 10105, 10106, 10107, 10108, 10109, 10110, 10111, 10112, 10113, 10114, 10115, 10116, 10117, 10118] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B4x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 22592 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22813 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  glam87_rreach [10045, 10046, 10047, 10048, 10049, 10050, 10051, 10052, 10053, 10054, 10055, 10056, 10057, 10058, 10059, 10060, 10061, 10062, 10063, 10064, 10065, 10066, 10067, 10068, 10069, 10070, 10071, 10072, 10073, 10074, 10075, 10076, 10077, 10078, 10079, 10080, 10081, 10082, 10083, 10084, 10085, 10086, 10087, 10088, 10089, 10090, 10091, 10092, 10093, 10094, 10095, 10096, 10097, 10098, 10099, 10100, 10101, 10102, 10103, 10104, 10105, 10106, 10107, 10108, 10109, 10110, 10111, 10112, 10113, 10114, 10115, 10116, 10117, 10118] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B2 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 22592 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22444 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [10045, 10046, 10047, 10048, 10049, 10050, 10051, 10052, 10053, 10054, 10055, 10056, 10057, 10058, 10059, 10060, 10061, 10062, 10063, 10064, 10065, 10066, 10067, 10068, 10069, 10070, 10071, 10072, 10073, 10074, 10075, 10076, 10088, 10089, 10090, 10091, 10092, 10093, 10094, 10104, 10105, 10106, 10107, 10108, 10109, 10110, 10111, 10112, 10113, 10114, 10115, 10116, 10117, 10118] with [wr2, pw0, pw1, REPc]

theorem pk_B2x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 22592 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22813 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  glam87_rreach [10045, 10046, 10047, 10048, 10049, 10050, 10051, 10052, 10053, 10054, 10055, 10056, 10057, 10058, 10059, 10060, 10061, 10062, 10063, 10064, 10065, 10066, 10067, 10068, 10069, 10070, 10071, 10072, 10073, 10074, 10075, 10076, 10088, 10089, 10090, 10091, 10092, 10093, 10094, 10104, 10105, 10106, 10107, 10108, 10109, 10110, 10111, 10112, 10113, 10114, 10115, 10116, 10117, 10118] with [wr2, pw0, pw1, REPc]

set_option maxRecDepth 100000 in
theorem pk_exit (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (nr a b e : Nat) :
    Reach (callState s 22813 (wd nr :: wd a :: wd b :: wd e :: wd ret :: tail) M)
      (callState s ret tail M) 16 := by
  glam87_rreach [10119, 10120, 10121, 10122, 10123] with [hj]

/-- One iteration, loop continues. -/
theorem pk_iter (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 22444 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22444 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
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
    Reach (callState s 22444 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 22813 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

end

end MlDsaOptGlam87.Proofs.G5PK
