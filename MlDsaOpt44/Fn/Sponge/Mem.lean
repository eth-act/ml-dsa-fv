import MlDsaOpt44.Layout
set_option warningAsError true
/-!
# Memory helpers for the sponge-glue loops (`storeWords` frames, XOR lemmas)
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

theorem word_storeWords_out {m : ByteArray} {base : Nat} {v : Nat → Nat} {k a : Nat}
    (h : a + 32 ≤ base ∨ base + 32 * k ≤ a) : word (storeWords m base v k) a = word m a :=
  FrameExcept.word (FrameExcept.storeWords m base v k) (by
    simp only [avoids_cons, avoids_nil, and_true]; omega)

theorem word_storeWords_get {m : ByteArray} {base : Nat} {v : Nat → Nat} {k i : Nat}
    (hv : v i < 2 ^ 256) (hi : i < k) : word (storeWords m base v k) (base + 32 * i) = v i :=
  word_storeWords hv k hi

theorem xor_lt256 {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) : a ^^^ b < 2 ^ 256 :=
  Nat.xor_lt_two_pow ha hb

theorem storeWords_mono_frame {m : ByteArray} {base : Nat} {v : Nat → Nat} {k : Nat}
    {lo hi : Nat} (hlo : lo ≤ base) (hhi : base + 32 * k ≤ hi) :
    FrameExcept m (storeWords m base v k) [(lo, hi)] :=
  (FrameExcept.storeWords m base v k).mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨(lo, hi), by simp, hlo, hhi⟩)

end MlDsaOpt44.Proofs.WP4
