import MlDsaOpt44.Fn.Sponge.Defs
import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/Ginit.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `ginit`: one block lemma per stored lane, chained
-/

namespace MlDsaOptGlam44.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

theorem wb_congr {M : ByteArray} {e v a a' : Nat} (he : e = v) (ha : a = a') :
    MachineState.writeBytes M (Data.Bytes.natToBytesPadded e 32) a =
      MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) a' := by
  subst he ha; rfl

theorem padTop_eq : padTop = 2 ^ 252 := by
  unfold padTop spread; decide +kernel

theorem or_modL (a b : Nat) :
    (a ||| b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 |||
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.or_mod_two_pow (n := 256)

theorem xor_modL (a b : Nat) :
    (a ^^^ b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 ^^^
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.xor_mod_two_pow (n := 256)

theorem and_modL (a b : Nat) :
    (a &&& b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 &&&
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.and_mod_two_pow (n := 256)

theorem xor_left_comm' (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

set_option hygiene false in
/-- Close the value goal of a `ginit` lane block. -/
macro "ginit_value" : tactic => `(tactic| (
  have hkL : keep % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = keep :=
    Nat.mod_eq_of_lt hk
  have hlL : l4 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = l4 :=
    Nat.mod_eq_of_lt hl
  have hnL : (115792089237316195423570985008687907853269984665640564039457584007913129639935 - keep) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      115792089237316195423570985008687907853269984665640564039457584007913129639935 - keep :=
    Nat.mod_eq_of_lt (by omega)
  simp only [ginitWord, padTop_eq, complemented, RHO1, KS, List.mem_cons, List.mem_nil_iff,
    Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
    or_false, or_true, false_or, if_true, if_false, Nat.lt_irrefl, ↓reduceIte,
    or_modL, xor_modL, and_modL, Nat.mod_mod, word_mod, hkL, hlL, hnL,
    Nat.xor_zero, Nat.zero_xor, Nat.zero_or, Nat.or_zero, Nat.zero_mod, Nat.mul_comm, Nat.xor_comm,
    Nat.xor_assoc, xor_left_comm', Nat.and_comm, Nat.or_comm]))

set_option maxRecDepth 100000 in
theorem ginit_lane0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18001 (wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 0))
      (callState s 18024 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 1)) 57 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7347, 7348, 7349, 7350, 7351, 7352, 7353, 7354, 7355, 7356, 7357, 7358, 7359, 7360, 7361, 7362, 7363, 7364, 7365] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 0]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18024 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 1))
      (callState s 18048 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 2)) 58 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7366, 7367, 7368, 7369, 7370, 7371, 7372, 7373, 7374, 7375, 7376, 7377, 7378, 7379, 7380, 7381, 7382, 7383] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 1]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18048 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 2))
      (callState s 18072 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 3)) 58 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7384, 7385, 7386, 7387, 7388, 7389, 7390, 7391, 7392, 7393, 7394, 7395, 7396, 7397, 7398, 7399, 7400, 7401] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 2]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18072 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 3))
      (callState s 18094 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 4)) 52 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7402, 7403, 7404, 7405, 7406, 7407, 7408, 7409, 7410, 7411, 7412, 7413, 7414, 7415, 7416, 7417] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 3]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18094 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 4))
      (callState s 18104 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 5)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7418, 7419, 7420, 7421, 7422, 7423, 7424, 7425] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 4]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18104 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 5))
      (callState s 18114 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 6)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7426, 7427, 7428, 7429, 7430, 7431, 7432, 7433] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 5]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18114 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 6))
      (callState s 18124 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 7)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7434, 7435, 7436, 7437, 7438, 7439, 7440, 7441] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 6]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18124 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 7))
      (callState s 18134 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 8)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7442, 7443, 7444, 7445, 7446, 7447, 7448, 7449] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 7]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18134 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 8))
      (callState s 18146 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 9)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7450, 7451, 7452, 7453, 7454, 7455, 7456, 7457] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 8]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane9 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18146 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 9))
      (callState s 18158 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 10)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7458, 7459, 7460, 7461, 7462, 7463, 7464, 7465] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 9]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane10 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18158 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 10))
      (callState s 18170 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 11)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7466, 7467, 7468, 7469, 7470, 7471, 7472, 7473] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 10]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane11 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18170 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 11))
      (callState s 18182 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 12)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7474, 7475, 7476, 7477, 7478, 7479, 7480, 7481] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 11]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane12 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18182 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 12))
      (callState s 18194 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 13)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7482, 7483, 7484, 7485, 7486, 7487, 7488, 7489] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 12]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane13 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18194 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 13))
      (callState s 18206 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 14)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7490, 7491, 7492, 7493, 7494, 7495, 7496, 7497] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 13]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane14 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18206 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 14))
      (callState s 18218 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 15)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7498, 7499, 7500, 7501, 7502, 7503, 7504, 7505] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 14]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane15 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18218 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 15))
      (callState s 18230 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 16)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7506, 7507, 7508, 7509, 7510, 7511, 7512, 7513] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 15]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane16 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18230 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 16))
      (callState s 18276 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 17)) 32 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7514, 7515, 7516, 7517, 7518, 7519, 7520, 7521, 7522, 7523] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 16]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane17 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18276 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 17))
      (callState s 18288 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 18)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7524, 7525, 7526, 7527, 7528, 7529, 7530, 7531] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 17]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane18 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18288 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 18))
      (callState s 18300 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 19)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7532, 7533, 7534, 7535, 7536, 7537, 7538, 7539] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 18]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane19 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18300 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 19))
      (callState s 18312 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 20)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7540, 7541, 7542, 7543, 7544, 7545, 7546, 7547] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 19]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane20 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18312 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 20))
      (callState s 18360 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 21)) 38 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7548, 7549, 7550, 7551, 7552, 7553, 7554, 7555, 7556, 7557, 7558, 7559] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 20]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane21 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18360 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 21))
      (callState s 18372 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 22)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7560, 7561, 7562, 7563, 7564, 7565, 7566, 7567] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 21]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane22 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18372 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 22))
      (callState s 18384 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 23)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7568, 7569, 7570, 7571, 7572, 7573, 7574, 7575] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 22]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane23 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18384 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 23))
      (callState s 18396 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 24)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 23]
  glam44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane24 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 18396 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 24))
      (callState s ret tail (storeWords m 0 (ginitWord m keep amult cmult l4) 25)) 41 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  refine reach_block hs [7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 24]
  glam44_block [word_storeWords_out, hj]
  refine wb_congr ?_ (by norm_num); ginit_value

theorem ginitWord_lt (m : ByteArray) {keep amult cmult l4 : Nat} (hk : keep < 2 ^ 256)
    (hl : l4 < 2 ^ 256) (x : Nat) : ginitWord m keep amult cmult l4 x < 2 ^ 256 := by
  have hw := word_lt m (KS + 32 * x)
  have h0 : ∀ a b : Nat, a % 2 ^ 256 ^^^ b % 2 ^ 256 < 2 ^ 256 := fun a b =>
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  unfold ginitWord
  refine Nat.or_lt_two_pow ?_ (Nat.lt_of_le_of_lt Nat.and_le_left hw)
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_) ?_) ?_
  · split
    · exact h0 _ _
    · norm_num
  · split <;> omega
  · split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  · split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  · split <;> omega

theorem ginit_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (ha : amult < 2 ^ 256) (hc : cmult < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.ginit [wd l4, wd cmult, wd amult, wd keep] ret tail m [] m' Gas.ginit := by
  refine ⟨storeWords m 0 (ginitWord m keep amult cmult l4) 25, fun x hx => ?_,
    storeWords_mono_frame (by simp [KS]) (by simp [KS]), ?_⟩
  · have := word_storeWords_get (m := m) (base := 0) (ginitWord_lt (amult := amult) (cmult := cmult) m hk hl x) hx
    simpa [KS] using this
  · rw [call_iff, Entry.ginit, Gas.ginit]
    exact ((((((((((((((((((((((((ginit_lane0 hs hr m hk hl).trans (ginit_lane1 hs hr m hk hl)).trans (ginit_lane2 hs hr m hk hl)).trans (ginit_lane3 hs hr m hk hl)).trans (ginit_lane4 hs hr m hk hl)).trans (ginit_lane5 hs hr m hk hl)).trans (ginit_lane6 hs hr m hk hl)).trans (ginit_lane7 hs hr m hk hl)).trans (ginit_lane8 hs hr m hk hl)).trans (ginit_lane9 hs hr m hk hl)).trans (ginit_lane10 hs hr m hk hl)).trans (ginit_lane11 hs hr m hk hl)).trans (ginit_lane12 hs hr m hk hl)).trans (ginit_lane13 hs hr m hk hl)).trans (ginit_lane14 hs hr m hk hl)).trans (ginit_lane15 hs hr m hk hl)).trans (ginit_lane16 hs hr m hk hl)).trans (ginit_lane17 hs hr m hk hl)).trans (ginit_lane18 hs hr m hk hl)).trans (ginit_lane19 hs hr m hk hl)).trans (ginit_lane20 hs hr m hk hl)).trans (ginit_lane21 hs hr m hk hl)).trans (ginit_lane22 hs hr m hk hl)).trans (ginit_lane23 hs hr m hk hl)).trans (ginit_lane24 hs hr m hk hl)


end MlDsaOptGlam44.Proofs.WP4
