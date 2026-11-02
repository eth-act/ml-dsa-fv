import MlDsaOptGlam44.Fn.Hint.PackBlocks
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Hint/PackIter.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# `pack` (WP10): one loop iteration from the generated blocks
-/

set_option linter.unusedVariables false

namespace MlDsaOptGlam44.Proofs.PK

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs MlDsaOpt44.Proofs
open MlDsaOptGlam44.Proofs.Infra

def q1o0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk1o0 (M) wp fp 

def q1o1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk1o1 (M) wp fp 

def q2o0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk2o0 (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp)

def q2o1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk2o1 (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp)

def q2w0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk2w0 (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp)

def q2w1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk2w1 (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp)

def q2w2 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk2w2 (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp)

def q2w3 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk2w3 (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp)

def qm2 (M : ByteArray) (wp fp : Nat) : ByteArray :=
  (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (q2w0 M wp fp).toNat 32) (fp)) (Data.Bytes.natToBytesPadded (q2w1 M wp fp).toNat 32) (768 + fp)) (Data.Bytes.natToBytesPadded (q2w2 M wp fp).toNat 32) (1536 + fp)) (Data.Bytes.natToBytesPadded (q2w3 M wp fp).toNat 32) (2304 + fp))

def q3o0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk3o0 ((qm2 M wp fp)) wp fp (q2o0 M wp fp) (q2o1 M wp fp)

def q3o1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk3o1 ((qm2 M wp fp)) wp fp (q2o0 M wp fp) (q2o1 M wp fp)

def q4o0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk4o0 ((qm2 M wp fp)) wp fp (q3o0 M wp fp) (q3o1 M wp fp)

def q4o1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk4o1 ((qm2 M wp fp)) wp fp (q3o0 M wp fp) (q3o1 M wp fp)

def q4w0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk4w0 ((qm2 M wp fp)) wp fp (q3o0 M wp fp) (q3o1 M wp fp)

def q4w1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk4w1 ((qm2 M wp fp)) wp fp (q3o0 M wp fp) (q3o1 M wp fp)

def q4w2 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk4w2 ((qm2 M wp fp)) wp fp (q3o0 M wp fp) (q3o1 M wp fp)

def q4w3 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk4w3 ((qm2 M wp fp)) wp fp (q3o0 M wp fp) (q3o1 M wp fp)

def qm4 (M : ByteArray) (wp fp : Nat) : ByteArray :=
  (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (qm2 M wp fp) (Data.Bytes.natToBytesPadded (q4w0 M wp fp).toNat 32) (32 + fp)) (Data.Bytes.natToBytesPadded (q4w1 M wp fp).toNat 32) (800 + fp)) (Data.Bytes.natToBytesPadded (q4w2 M wp fp).toNat 32) (1568 + fp)) (Data.Bytes.natToBytesPadded (q4w3 M wp fp).toNat 32) (2336 + fp))

def q5o0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk5o0 ((qm4 M wp fp)) wp fp (q4o0 M wp fp) (q4o1 M wp fp)

def q6w0 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk6w0 ((qm4 M wp fp)) wp fp (q5o0 M wp fp)

def q6w1 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk6w1 ((qm4 M wp fp)) wp fp (q5o0 M wp fp)

def q6w2 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk6w2 ((qm4 M wp fp)) wp fp (q5o0 M wp fp)

def q6w3 (M : ByteArray) (wp fp : Nat) : UInt256 :=
  pk6w3 ((qm4 M wp fp)) wp fp (q5o0 M wp fp)

def qm6 (M : ByteArray) (wp fp : Nat) : ByteArray :=
  (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (qm4 M wp fp) (Data.Bytes.natToBytesPadded (q6w0 M wp fp).toNat 32) (64 + fp)) (Data.Bytes.natToBytesPadded (q6w1 M wp fp).toNat 32) (832 + fp)) (Data.Bytes.natToBytesPadded (q6w2 M wp fp).toNat 32) (1600 + fp)) (Data.Bytes.natToBytesPadded (q6w3 M wp fp).toNat 32) (2368 + fp))

theorem pk_iter {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (wp fp : Nat) (hwp : 43264 ≤ wp) (hwp2 : wp + 1024 ≤ 51456)
    (hfp : 59904 ≤ fp) (hfp2 : fp + 96 ≤ 59904 + 768)
    (hlt : wp + 1024 < 51456) :
    Reach (callState s 22645 (wd 4 :: wd fp :: wd wp :: wd 51456 :: wd ret :: tail) M)
      (callState s 22645 (wd 4 :: wd (96 + fp) :: wd (1024 + wp) :: wd 51456 :: wd ret :: tail)
        (qm6 M wp fp)) 1384 :=
  (((((pk_b1 hs (ret := ret) htail (M) wp fp  hwp hwp2 hfp hfp2).trans (pk_b2 hs (ret := ret) htail (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b3 hs (ret := ret) htail (qm2 M wp fp) wp fp (q2o0 M wp fp) (q2o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b4 hs (ret := ret) htail (qm2 M wp fp) wp fp (q3o0 M wp fp) (q3o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b5 hs (ret := ret) htail (qm4 M wp fp) wp fp (q4o0 M wp fp) (q4o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b6 hs (ret := ret) htail (qm4 M wp fp) wp fp (q5o0 M wp fp) hwp hwp2 hfp hfp2 hlt)

theorem pk_iterx {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (wp fp : Nat) (hwp : 43264 ≤ wp) (hwp2 : wp + 1024 ≤ 51456)
    (hfp : 59904 ≤ fp) (hfp2 : fp + 96 ≤ 59904 + 768)
    (hlt : wp + 1024 = 51456) :
    Reach (callState s 22645 (wd 4 :: wd fp :: wd wp :: wd 51456 :: wd ret :: tail) M)
      (callState s 23720 (wd 4 :: wd (96 + fp) :: wd (1024 + wp) :: wd 51456 :: wd ret :: tail)
        (qm6 M wp fp)) 1384 :=
  (((((pk_b1 hs (ret := ret) htail (M) wp fp  hwp hwp2 hfp hfp2).trans (pk_b2 hs (ret := ret) htail (M) wp fp (q1o0 M wp fp) (q1o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b3 hs (ret := ret) htail (qm2 M wp fp) wp fp (q2o0 M wp fp) (q2o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b4 hs (ret := ret) htail (qm2 M wp fp) wp fp (q3o0 M wp fp) (q3o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b5 hs (ret := ret) htail (qm4 M wp fp) wp fp (q4o0 M wp fp) (q4o1 M wp fp) hwp hwp2 hfp hfp2)).trans (pk_b6x hs (ret := ret) htail (qm4 M wp fp) wp fp (q5o0 M wp fp) hwp hwp2 hfp hfp2 hlt)


end MlDsaOptGlam44.Proofs.PK
