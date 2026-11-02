import MlDsaOpt87.Layout
import MlDsaOpt44.Math.Bswap
import MlDsaOpt44.Math.SpongeBits
import MlDsaOpt44.Math.SpongeBytes
set_option warningAsError true
/-!
# Replicated-lane lemmas for the 87 `sib` prologue

Copies of the few `MlDsaOpt44/Main/Mu/Lemmas.lean` facts the prologue needs.
That module imports `MlDsaOpt44.Main.Base`, whose `avoids_tac` (44 layout)
would shadow 87's in every importer of `Fn/Ball.lean`.
-/

namespace MlDsaOpt87.Proofs.Ball4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs (pack4_div_mod pack4_lt' cpl_lt cpl_eq)

/-- One more `MSTORE` inside the frame range. -/
theorem r4_frame_wr {m m' : ByteArray} {lo hi v b : Nat} (hb1 : lo ≤ b) (hb2 : b + 32 ≤ hi)
    (h : FrameExcept m m' [(lo, hi)]) :
    FrameExcept m (MachineState.writeBytes m' (Data.Bytes.natToBytesPadded v 32) b) [(lo, hi)] := by
  apply (h.trans (FrameExcept.mstore m' b v)).mono
  intro r hr
  refine ⟨(lo, hi), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

theorem r4_testBit_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {j : Nat} (hj : j < 256) :
    (pack4 v).testBit j = (v (j / 64)).testBit (j % 64) := by
  rw [← pack4_div_mod h (k := j / 64) (by omega), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [Nat.mod_lt j (by omega : 64 > 0), decide_true, Bool.true_and]
  congr 1; omega

theorem r4_rep_eq_pack4 (v : Nat) : rep v = pack4 fun _ => v := by
  unfold rep REP pack4; ring

theorem r4_rep_lt {v : Nat} (hv : v < 2 ^ 64) : rep v < 2 ^ 256 := by
  rw [r4_rep_eq_pack4]; exact pack4_lt' fun _ _ => hv

theorem r4_rep_xor {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : rep a ^^^ rep b = rep (a ^^^ b) := by
  have hab : a ^^^ b < 2 ^ 64 := Nat.xor_lt_two_pow ha hb
  apply eq_of_testBit_lt (Nat.xor_lt_two_pow (r4_rep_lt ha) (r4_rep_lt hb)) (r4_rep_lt hab)
  intro j hj
  rw [Nat.testBit_xor, r4_rep_eq_pack4, r4_rep_eq_pack4, r4_rep_eq_pack4,
    r4_testBit_pack4 (fun _ _ => ha) hj, r4_testBit_pack4 (fun _ _ => hb) hj,
    r4_testBit_pack4 (fun _ _ => hab) hj, Nat.testBit_xor]

theorem r4_not_rep {v : Nat} (hv : v < 2 ^ 64) : 2 ^ 256 - 1 - rep v = rep (2 ^ 64 - 1 - v) := by
  unfold rep REP pack4; norm_num; omega

theorem r4_rep_cpl_xor (x : Nat) {v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) :
    rep (cpl x v) ^^^ rep w = rep (cpl x (v ^^^ w)) := by
  rw [r4_rep_xor (cpl_lt hv) hw, cpl_eq hv, cpl_eq (Nat.xor_lt_two_pow hv hw)]
  split
  · rw [Nat.xor_assoc, Nat.xor_comm M64 w, ← Nat.xor_assoc]
  · rfl

theorem r4_not_rep_cpl {x v : Nat} (hx : x ∈ complemented) (hv : v < 2 ^ 64) :
    2 ^ 256 - 1 - rep (cpl x v) = rep v := by
  rw [r4_not_rep (cpl_lt hv)]; unfold cpl; rw [if_pos hx]; congr 1; omega

theorem r4_word_lt_lit (m : ByteArray) (a : Nat) :
    word m a < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := word_lt m a

theorem r4_xor_mod_lit {u v : Nat}
    (hu : u < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hv : v < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    (u ^^^ v) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = u ^^^ v := by
  have h := Nat.xor_lt_two_pow (n := 256) (by norm_num; exact hu) (by norm_num; exact hv)
  norm_num at h
  exact Nat.mod_eq_of_lt h

end MlDsaOpt87.Proofs.Ball4
