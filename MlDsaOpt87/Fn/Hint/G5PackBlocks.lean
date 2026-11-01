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
    Reach (callState s 17404 (wd nr :: wd F :: wd B :: wd ret :: tail) M)
      (callState s 17413 (wd nr :: wd F :: wd B :: wd (8192 + B) :: wd ret :: tail) M) 19 := by
  opt87_reach [7784, 7785, 7786, 7787, 7788, 7789, 7790]

theorem pk_A (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (nr wp fp e : Nat)
    (hwp : wp + 512 ≤ 90656) :
    Reach (callState s 17413 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17561 (pkA M wp :: wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M) 327 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7791, 7792, 7793, 7794, 7795, 7796, 7797, 7798, 7799, 7800, 7801, 7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812, 7813, 7814, 7815, 7816, 7817, 7818, 7819, 7820, 7821, 7822, 7823, 7824, 7825, 7826, 7827, 7828, 7829, 7830, 7831, 7832, 7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845, 7846, 7847, 7848, 7849, 7850, 7851, 7852, 7853, 7854, 7855, 7856, 7857, 7858, 7859, 7860, 7861, 7862, 7863, 7864, 7865, 7866, 7867, 7868, 7869, 7870, 7871, 7872, 7873, 7874, 7875, 7876, 7877, 7878, 7879, 7880, 7881, 7882, 7883, 7884, 7885, 7886, 7887, 7888, 7889, 7890, 7891, 7892, 7893, 7894, 7895, 7896, 7897, 7898, 7899, 7900] with [pkA]

theorem pk_B4 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 17561 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17413 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7933, 7934, 7935, 7936, 7937, 7938, 7939, 7940, 7941, 7942, 7943, 7944, 7945, 7946, 7947, 7948, 7949, 7950, 7951, 7952, 7953, 7954, 7955, 7956, 7957, 7958, 7959, 7960, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B4x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 17561 (x :: wd 4 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17782 (wd 4 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr4 M x fp)) 249 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt87_reach [7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7933, 7934, 7935, 7936, 7937, 7938, 7939, 7940, 7941, 7942, 7943, 7944, 7945, 7946, 7947, 7948, 7949, 7950, 7951, 7952, 7953, 7954, 7955, 7956, 7957, 7958, 7959, 7960, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974] with [wr4, wr2, pw0, pw1, pw2, pw3, REPc]

theorem pk_B2 (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 17561 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17413 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7944, 7945, 7946, 7947, 7948, 7949, 7950, 7960, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974] with [wr2, pw0, pw1, REPc]

theorem pk_B2x (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) (x : UInt256) (wp fp e : Nat)
    (hfp : fp + 1568 ≤ 90656) (hwe : 512 + wp = e) (he : e < 2 ^ 64) :
    Reach (callState s 17561 (x :: wd 2 :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17782 (wd 2 :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wr2 M x fp)) 185 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  subst hwe
  opt87_reach [7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7944, 7945, 7946, 7947, 7948, 7949, 7950, 7960, 7961, 7962, 7963, 7964, 7965, 7966, 7967, 7968, 7969, 7970, 7971, 7972, 7973, 7974] with [wr2, pw0, pw1, REPc]

set_option maxRecDepth 100000 in
theorem pk_exit (hs : Ctx s) (htail : tail.length ≤ 960)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16) (M : ByteArray)
    (nr a b e : Nat) :
    Reach (callState s 17782 (wd nr :: wd a :: wd b :: wd e :: wd ret :: tail) M)
      (callState s ret tail M) 16 := by
  opt87_reach [7975, 7976, 7977, 7978, 7979] with [hj]

/-- One iteration, loop continues. -/
theorem pk_iter (hs : Ctx s) (htail : tail.length ≤ 960) (M : ByteArray) {nr : Nat}
    (hnr : nr = 2 ∨ nr = 4) (wp fp e : Nat) (hwp : wp + 512 ≤ 90656) (hfp : fp + 1568 ≤ 90656)
    (hwe : 512 + wp < e) (he : e < 2 ^ 64) :
    Reach (callState s 17413 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17413 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
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
    Reach (callState s 17413 (wd nr :: wd fp :: wd wp :: wd e :: wd ret :: tail) M)
      (callState s 17782 (wd nr :: wd (32 + fp) :: wd (512 + wp) :: wd e :: wd ret :: tail)
        (wrN nr M (pkA M wp) fp)) (cI nr) := by
  have hA := pk_A hs (ret := ret) htail M nr wp fp e hwp
  rcases hnr with rfl | rfl
  · simp only [wrN, cI, show (2 : Nat) ≤ 2 from le_rfl, if_true]
    exact (hA.trans (pk_B2x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)
  · simp only [wrN, cI, show ¬ (4 : Nat) ≤ 2 by decide, if_false]
    exact (hA.trans (pk_B4x hs htail M _ wp fp e hfp hwe he)).mono (by norm_num)

end

end MlDsaOpt87.Proofs.G5PK
