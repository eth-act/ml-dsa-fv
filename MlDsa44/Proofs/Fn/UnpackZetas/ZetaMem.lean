import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# Memory written by `initZetas`

`zmem m j`: memory after the first `j` iterations of
`mstore(ZETA + 32 brv8(i), ζ^i mod q)` (in the form `evm_block` leaves it).
Since `bitRev8` is an involution on `[0, 256)`, after 256 iterations the
table is `ZetaTable`, and only `[ZETA, ZETA + POLY)` changed.
-/

namespace MlDsa44.Proofs.UnpackZetas

open EvmSemantics
open Infra

def zmem (m : ByteArray) : Nat → ByteArray
  | 0 => m
  | j + 1 => MachineState.writeBytes (zmem m j)
      (Data.Bytes.natToBytesPadded (1753 ^ j % 8380417) 32) (2528 + Fips204.bitRev8 j * 32)

theorem bitRev8_lt : ∀ k, k < 256 → Fips204.bitRev8 k < 256 := by decide +kernel

theorem bitRev8_bitRev8 : ∀ k, k < 256 → Fips204.bitRev8 (Fips204.bitRev8 k) = k := by
  decide +kernel

theorem zmem_word (m : ByteArray) :
    ∀ n, n ≤ 256 → ∀ j, j < n →
      word (zmem m n) (2528 + Fips204.bitRev8 j * 32) = 1753 ^ j % 8380417
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, hn, j, hj => by
    have hv : 1753 ^ n % 8380417 < 2 ^ 256 :=
      Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    simp only [zmem]
    by_cases hjn : j = n
    · subst hjn; exact word_mstore _ _ _ hv
    · have hne : Fips204.bitRev8 j ≠ Fips204.bitRev8 n := fun h => hjn (by
        rw [← bitRev8_bitRev8 j (by omega), h, bitRev8_bitRev8 n (by omega)])
      rw [word_mstore_disjoint _ _ (by omega)]
      exact zmem_word m n (by omega) j (by omega)

theorem zmem_table (m : ByteArray) : ZetaTable (zmem m 256) := by
  intro k hk
  have h := zmem_word m 256 le_rfl (Fips204.bitRev8 k) (bitRev8_lt k hk)
  rw [bitRev8_bitRev8 k hk] at h
  rw [show ZETA + 32 * k = 2528 + k * 32 by simp only [ZETA]; omega, h]
  simp only [Fips204.zetas, Fips204.zeta, Fips204.q]

theorem zmem_frame (m : ByteArray) :
    ∀ n, n ≤ 256 → FrameExcept m (zmem m n) [(ZETA, ZETA + POLY)]
  | 0, _ => FrameExcept.refl m _
  | n + 1, hn => by
    have hr := bitRev8_lt n (by omega)
    simp only [zmem]
    apply FrameExcept.mono (FrameExcept.trans (zmem_frame m n (by omega)) (FrameExcept.mstore _ _ _))
    intro r hr'
    refine ⟨(ZETA, ZETA + POLY), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr'
    rcases hr' with rfl | rfl <;> simp only [ZETA, POLY] <;> omega

end MlDsa44.Proofs.UnpackZetas
