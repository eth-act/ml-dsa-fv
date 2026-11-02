import MlDsaOpt44.Fn.Sponge.MuBlocks
import MlDsaOpt44.Fn.Sponge.MuFinal
import MlDsaOpt44.Fn.Sponge.Spr
import MlDsaOpt44.Fn.Sponge.Trabs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
/-!
# `mu0`: composition of the blocks, the ten `spr` calls and the `trabs` call
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra
open MlDsa44

theorem spr_at {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (ret' : Nat) (extra : List UInt256) (hext : extra.length ≤ 4)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret' = true) (hsm : ret' < 2 ^ 16)
    (M : ByteArray) (v : Nat) :
    Reach (callState s 12425 (wd v :: wd ret' :: (extra ++ tail)) M)
      (callState s ret' (wd (sprNet v) :: (extra ++ tail)) M) 120 :=
  call_iff.mp (spr_call_any hs (hr.callee (B' := Stack.spr) (extra := extra)
    (by simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf]; omega) hj hsm) M v)

theorem mu_step (m : ByteArray) (Q : Nat → Nat) (i j r sh a : Nat) (hj : j = i + 1) (ha : a = 32 * i)
    (hQ : Q i = (word m a ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    MachineState.writeBytes (storeWords m 0 Q i) (Data.Bytes.natToBytesPadded
      ((word (storeWords m 0 Q i) a ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) a = storeWords m 0 Q j := by
  subst hj ha
  rw [storeWords_succ, word_storeWords_out (Or.inr (by omega)), ← hQ, show 0 + i * 32 = 32 * i by ring]

set_option maxHeartbeats 4000000 in
theorem mu0_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (m : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (mlenOf s.executionEnv.calldata ≤ 69 → ∀ tr : ByteArray, tr.size = 64 →
        (∀ x, x < 8 → word m (TRL + 32 * x) = le64 tr (8 * x)) →
        ∀ x, x < 25 → word m' (KS + 32 * x) =
          if x < 17 then word m (KS + 32 * x) ^^^
            spread (le64 (muBlock tr s.executionEnv.calldata) (8 * x)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
      (69 < mlenOf s.executionEnv.calldata → m' = m) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.mu0 [wd sh] ret tail m [] m' Gas.mu0 := by
  have hcd' : 3732 ≤ s.executionEnv.calldata.size := hcd
  by_cases hml : mlenOf s.executionEnv.calldata ≤ 69
  swap
  · refine ⟨m, fun h => absurd h hml, fun _ => rfl, FrameExcept.refl _ _, ?_⟩
    rw [call_iff, Entry.mu0, Gas.mu0]
    exact ((mu0_skip hs hr m hsh hcd' (Nat.lt_of_not_le hml)).mono (by norm_num)).of_eq rfl rfl
  have hml' : (s.executionEnv.calldata.size - 3732) ≤ 69 := hml
  have r0 := mu0_b0 hs hr m hsh hcd' hml'
  have c0 := spr_at hs hr 12633 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) m (word m 64768)
  have r1 := mu0_b1 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 0) (r := sprNet (word m 64768)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 0 1 (sprNet (word m 64768)) sh 0 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 0) (a := 64800) (Or.inr (by norm_num))] at r1
  have c1 := spr_at hs hr 12653 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 1) (word m 64800)
  have r2 := mu0_b2 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 1) (r := sprNet (word m 64800)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 1 2 (sprNet (word m 64800)) sh 32 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 1) (a := 64832) (Or.inr (by norm_num))] at r2
  have c2 := spr_at hs hr 12675 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 2) (word m 64832)
  have r3 := mu0_b3 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 2) (r := sprNet (word m 64832)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 2 3 (sprNet (word m 64832)) sh 64 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 2) (a := 64864) (Or.inr (by norm_num))] at r3
  have c3 := spr_at hs hr 12697 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 3) (word m 64864)
  have r4 := mu0_b4 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 3) (r := sprNet (word m 64864)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 3 4 (sprNet (word m 64864)) sh 96 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 3) (a := 64896) (Or.inr (by norm_num))] at r4
  have c4 := spr_at hs hr 12719 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 4) (word m 64896)
  have r5 := mu0_b5 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 4) (r := sprNet (word m 64896)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 4 5 (sprNet (word m 64896)) sh 128 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 4) (a := 64928) (Or.inr (by norm_num))] at r5
  have c5 := spr_at hs hr 12741 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 5) (word m 64928)
  have r6 := mu0_b6 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 5) (r := sprNet (word m 64928)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 5 6 (sprNet (word m 64928)) sh 160 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 5) (a := 64960) (Or.inr (by norm_num))] at r6
  have c6 := spr_at hs hr 12763 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 6) (word m 64960)
  have r7 := mu0_b7 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 6) (r := sprNet (word m 64960)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 6 7 (sprNet (word m 64960)) sh 192 rfl rfl rfl, word_storeWords_out (m := m) (base := 0) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (k := 6) (a := 64992) (Or.inr (by norm_num))] at r7
  have c7 := spr_at hs hr 12785 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 7) (word m 64992)
  have r8 := mu0_b8 hs hr (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 7) (r := sprNet (word m 64992)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  rw [mu_step m (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 7 8 (sprNet (word m 64992)) sh 224 rfl rfl rfl] at r8
  obtain ⟨m9, h9post, h9frame, h9call⟩ := trabs_call_aux hs
    (hr.callee (B' := Stack.trabs) (ret' := 12844) (extra := [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret])
      (by simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf, List.length_cons, List.length_nil]; omega)
      (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 8) (off := 3730) (sh := sh) (n4 := 3) (lm := 115792089237316195417293883273301227089434195242432897623355228563449095127040) (kp := 256)
    (by norm_num) hsh (by norm_num) (by norm_num) (by simp [KS]) (by simp [KS]) (by norm_num)
  have t9 := call_iff.mp h9call
  have r9 := mu0_b9 hs hr m9 (mlen := (s.executionEnv.calldata.size - 3732)) hsh
  have c9 := spr_at hs hr 12870 [wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp) (by simp only [Infra.isValidJumpDest_lit])
    (by norm_num) m9 (65280 &&& word s.executionEnv.calldata 3730 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 3730 /
              452312848583266388373324160190187140051835877600158453279131187530910662656)
  have r10 := mu0_b10 hs hr m9 (r := sprNet (65280 &&& word s.executionEnv.calldata 3730 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 3730 /
              452312848583266388373324160190187140051835877600158453279131187530910662656))
    (mlen := (s.executionEnv.calldata.size - 3732)) hsh hml'
  have c10 := spr_at hs hr 12905 [wd (66 + (s.executionEnv.calldata.size - 3732)), wd (s.executionEnv.calldata.size - 3732), wd sh, wd ret] (by simp)
    (by simp only [Infra.isValidJumpDest_lit]) (by norm_num) (MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded ((word m9 256 ^^^ sprNet (65280 &&& word s.executionEnv.calldata 3730 / 6901746346790563787434755862277025452451108972170386555162524223799296 ||| word s.executionEnv.calldata 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256) (31 * 2 ^ ((7 &&& 66 + (s.executionEnv.calldata.size - 3732)) * 8))
  have r11 := mu0_b11 hs hr (MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded ((word m9 256 ^^^ sprNet (65280 &&& word s.executionEnv.calldata 3730 / 6901746346790563787434755862277025452451108972170386555162524223799296 ||| word s.executionEnv.calldata 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256) (r := sprNet (31 * 2 ^ ((7 &&& 66 + (s.executionEnv.calldata.size - 3732)) * 8)))
    (p := 66 + (s.executionEnv.calldata.size - 3732)) (mlen := (s.executionEnv.calldata.size - 3732)) hsh (by omega)
  have htot := (((((((((((((((r0.trans c0).trans (r1.trans c1)).trans (r2.trans c2)).trans (r3.trans c3)).trans (r4.trans c4)).trans (r5.trans c5)).trans (r6.trans c6)).trans (r7.trans c7)).trans r8).trans t9).trans r9).trans c9).trans r10).trans c10).trans r11)
  refine ⟨(MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded ((word m9 256 ^^^ sprNet (65280 &&& word s.executionEnv.calldata 3730 / 6901746346790563787434755862277025452451108972170386555162524223799296 ||| word s.executionEnv.calldata 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256) (Data.Bytes.natToBytesPadded ((sprNet (31 * 2 ^ ((7 &&& 66 + (s.executionEnv.calldata.size - 3732)) * 8)) * 2 ^ sh ^^^ word (MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded ((word m9 256 ^^^ sprNet (65280 &&& word s.executionEnv.calldata 3730 / 6901746346790563787434755862277025452451108972170386555162524223799296 ||| word s.executionEnv.calldata 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256) (0 + (66 + (s.executionEnv.calldata.size - 3732)) / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + (66 + (s.executionEnv.calldata.size - 3732)) / 8 * 32)) (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes (MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded ((word m9 256 ^^^ sprNet (65280 &&& word s.executionEnv.calldata 3730 / 6901746346790563787434755862277025452451108972170386555162524223799296 ||| word s.executionEnv.calldata 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256) (Data.Bytes.natToBytesPadded ((sprNet (31 * 2 ^ ((7 &&& 66 + (s.executionEnv.calldata.size - 3732)) * 8)) * 2 ^ sh ^^^ word (MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded ((word m9 256 ^^^ sprNet (65280 &&& word s.executionEnv.calldata 3730 / 6901746346790563787434755862277025452451108972170386555162524223799296 ||| word s.executionEnv.calldata 3730 / 452312848583266388373324160190187140051835877600158453279131187530910662656) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256) (0 + (66 + (s.executionEnv.calldata.size - 3732)) / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + (66 + (s.executionEnv.calldata.size - 3732)) / 8 * 32)) 512 ^^^ 7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512), fun _ tr htr hTRL x hx => ?_, fun h => absurd h (by omega), ?_, ?_⟩
  · rw [show KS + 32 * x = 32 * x by simp [KS]]
    refine mu0_value hsh htr hcd' hml' (m8 := storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 8) (m9 := m9)
      (fun x hx => by simpa [TRL] using hTRL x hx) (fun y => ?_) (fun y hy => ?_) rfl rfl rfl hx
    · by_cases hy : y < 8
      · rw [if_pos hy]
        have h := word_storeWords_get (m := m) (base := 0) (k := 8) (i := y) (v := (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (modL_lt _) hy
        beta_reduce at h
        rw [Nat.zero_add] at h
        exact h
      · rw [if_neg hy]; exact word_storeWords_out (Or.inr (by omega))
    · have h := h9post y hy
      simp only [KS, Nat.zero_add] at h
      rw [h]
      by_cases hy' : 8 ≤ y ∧ y < 20
      · rw [if_pos (by omega), if_pos hy', show (32 * y - 256) / 32 = y - 8 by omega]
      · rw [if_neg (by omega), if_neg hy']
  · have f8 : FrameExcept m (storeWords m 0 (fun x => (word m (32 * x) ^^^ sprNet (word m (64768 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 8) [(0, 800)] :=
      storeWords_mono_frame (le_refl _) (by norm_num)
    refine ((((f8.trans h9frame).trans (FrameExcept.mstore _ _ _)).trans
      (FrameExcept.mstore _ _ _)).trans (FrameExcept.mstore _ _ _)).mono ?_
    intro r hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    refine ⟨(KS, KS + 800), by simp, ?_⟩
    simp only [KS]
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> omega
  · rw [call_iff, Entry.mu0, Gas.mu0]
    exact (htot.mono (by simp only [Gas.trabs]; norm_num)).of_eq rfl rfl

end MlDsaOpt44.Proofs.WP4
