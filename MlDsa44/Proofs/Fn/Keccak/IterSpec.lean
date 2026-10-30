import MlDsa44.Proofs.Fn.Keccak.RoundSpec
/-!
# One iteration of the Yul model computes two Keccak rounds

`iterY M r` holds `round (round A RC[r]) RC[r+1]` at `ST`, keeps the round
constants and writes only below `RC`.
-/

namespace MlDsa44.Proofs.KeccakModel

open EvmSemantics
open EvmSemantics.EVM

/-- Peel a chain of `mstoreY`s whose addresses lie in `[lo, hi)`. -/
macro "frame_chain" : tactic => `(tactic| (
  repeat (first
    | exact Infra.FrameExcept.refl _ _
    | refine FrameExcept.trans' ?_ (FrameExcept.mstoreY _ _ (by norm_num) (by norm_num)))))

theorem half1_frame (M : ByteArray) : FrameExcept M (half1 M) [(800, 1760)] := by
  simp only [half1, row1_0, row1_1, row1_2, row1_3, row1_4, chi5Y, thetaY]
  frame_chain

theorem half2_frame (M : ByteArray) : FrameExcept M (half2 M) [(0, 1760)] := by
  simp only [half2, row2_0, row2_1, row2_2, row2_3, row2_4, chi5Y, thetaY]
  frame_chain

theorem iotaY_frame (M : ByteArray) {dst lo hi : Nat} (rcA : UInt256) (hlo : lo ≤ dst)
    (hhi : dst + 32 ≤ hi) : FrameExcept M (iotaY M dst rcA) [(lo, hi)] :=
  FrameExcept.mstoreY _ _ hlo hhi

theorem rcAddr1_toNat {r : Nat} (hr : r < 24) : (rcAddr1 r).toNat = RC + 32 * r := by
  unfold rcAddr1
  rw [EvmProof.Word.word_toNat_add, EvmProof.Word.shiftLeft_toNat _ (by norm_num),
    EvmProof.Word.word_toNat_ofNat, EvmProof.Word.word_toNat_ofNat]
  simp only [RC]
  omega

theorem rcAddr2_toNat {r : Nat} (hr : r < 24) : (rcAddr2 r).toNat = RC + 32 * (r + 1) := by
  unfold rcAddr2
  rw [EvmProof.Word.word_toNat_add, EvmProof.Word.shiftLeft_toNat _ (by norm_num),
    EvmProof.Word.word_toNat_add, EvmProof.Word.word_toNat_ofNat, EvmProof.Word.word_toNat_ofNat,
    EvmProof.Word.word_toNat_ofNat]
  simp only [RC]
  omega

theorem mloadY_rc {M M' : ByteArray} {lo hi : Nat} (hrc : RCTable M)
    (hf : FrameExcept M M' [(lo, hi)]) (hhi : hi ≤ RC) {i : Nat} (hi24 : i < 24) :
    mloadY M' (RC + 32 * i) = L (Crypto.Keccak.RC[i]!) := by
  rw [mloadY_frame hf (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
    right; show hi ≤ _; omega)]
  exact mloadY_of_word (hrc i hi24)

theorem lanes_mloadY {M : ByteArray} {base : Nat} {A : Array UInt64} (hA : LanesAt M base A)
    (k : Nat) (hk : k < 25) : mloadY M (base + 32 * k) = L A[k]! :=
  mloadY_of_word (hA.2 k hk)

theorem iter_spec {M : ByteArray} {A : Array UInt64} {r : Nat} (hA : LanesAt M ST A)
    (hrc : RCTable M) (hr : r + 1 < 24) :
    LanesAt (iterY M r) ST
        (Crypto.Keccak.round (Crypto.Keccak.round A Crypto.Keccak.RC[r]!)
          Crypto.Keccak.RC[r + 1]!) ∧
      RCTable (iterY M r) ∧ FrameExcept M (iterY M r) [(ST, RC)] := by
  have hrc1 : mloadY (half1 M) (rcAddr1 r).toNat = L Crypto.Keccak.RC[r]! := by
    rw [rcAddr1_toNat (by omega)]
    exact mloadY_rc hrc (half1_frame M) (by simp [RC]) (by omega)
  have hl := fun k hk => lanes_mloadY hA k hk
  simp only [ST, Nat.zero_add] at hl
  have hB := round1_spec M (rcAddr1 r) _
    (hl 0 (by decide)) (hl 1 (by decide)) (hl 2 (by decide)) (hl 3 (by decide))
    (hl 4 (by decide)) (hl 5 (by decide)) (hl 6 (by decide)) (hl 7 (by decide))
    (hl 8 (by decide)) (hl 9 (by decide)) (hl 10 (by decide)) (hl 11 (by decide))
    (hl 12 (by decide)) (hl 13 (by decide)) (hl 14 (by decide)) (hl 15 (by decide))
    (hl 16 (by decide)) (hl 17 (by decide)) (hl 18 (by decide)) (hl 19 (by decide))
    (hl 20 (by decide)) (hl 21 (by decide)) (hl 22 (by decide)) (hl 23 (by decide))
    (hl 24 (by decide)) hrc1
  rw [← arr25 hA.1] at hB
  set B := Crypto.Keccak.round A Crypto.Keccak.RC[r]!
  set M7 := iotaY (half1 M) 800 (rcAddr1 r)
  have hf7 : FrameExcept M M7 [(800, 1760)] :=
    FrameExcept.trans' (half1_frame M) (iotaY_frame _ _ (by norm_num) (by norm_num))
  have hrc2 : mloadY (half2 M7) (rcAddr2 r).toNat = L Crypto.Keccak.RC[r + 1]! := by
    rw [rcAddr2_toNat (by omega)]
    exact mloadY_rc hrc (FrameExcept.trans' (Infra.FrameExcept.mono hf7 (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
      exact ⟨(0, 1760), by simp, by norm_num, le_rfl⟩)) (half2_frame M7)) (by simp [RC]) hr
  have hl' := fun k hk => lanes_mloadY hB k hk
  have hC := round2_spec M7 (rcAddr2 r) _
    (hl' 0 (by decide)) (hl' 1 (by decide)) (hl' 2 (by decide)) (hl' 3 (by decide))
    (hl' 4 (by decide)) (hl' 5 (by decide)) (hl' 6 (by decide)) (hl' 7 (by decide))
    (hl' 8 (by decide)) (hl' 9 (by decide)) (hl' 10 (by decide)) (hl' 11 (by decide))
    (hl' 12 (by decide)) (hl' 13 (by decide)) (hl' 14 (by decide)) (hl' 15 (by decide))
    (hl' 16 (by decide)) (hl' 17 (by decide)) (hl' 18 (by decide)) (hl' 19 (by decide))
    (hl' 20 (by decide)) (hl' 21 (by decide)) (hl' 22 (by decide)) (hl' 23 (by decide))
    (hl' 24 (by decide)) hrc2
  rw [← arr25 hB.1] at hC
  have hf : FrameExcept M (iterY M r) [(0, 1760)] := by
    refine FrameExcept.trans' (FrameExcept.trans' (Infra.FrameExcept.mono hf7 ?_)
      (half2_frame M7)) (iotaY_frame _ _ (by norm_num) (by norm_num))
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
    exact ⟨(0, 1760), by simp, by norm_num, le_rfl⟩
  refine ⟨hC, Infra.RCTable.frame hrc hf (by simp [RC]), by simpa [ST, RC] using hf⟩

end MlDsa44.Proofs.KeccakModel
