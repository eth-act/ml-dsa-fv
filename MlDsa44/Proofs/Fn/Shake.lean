import MlDsa44.Proofs.Fn.Shake.Absorb
/-!
# `shake`: SHAKE128/256 sponge over memory

Yul: `function shake(rate, ptr, len, out, blocks)`. Zero the state, absorb
`len / rate` full blocks from `[ptr, …)`, copy the remainder into `PADB`
(zeroed as six words), add the `0x1F … 0x80` padding, absorb it, then write
`blocks` output blocks to `out` (the last lane store overhangs by 24 bytes).
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas: the exact cost (every path is data independent once `rate`, `len`
-- and `blocks` are fixed; only the `MCOPY` word count depends on `len % rate`).
namespace Gas

/-- Zeroing, `len / rate` full-block absorbs, the padded block (with its
`MCOPY` of `len % rate` bytes), and `blocks` squeeze blocks of which all but
the first permute first. -/
def shake (rate len blocks : Nat) : Nat :=
  2408 + 3 * ((len % rate + 31) / 32) + (len / rate + 1) * (xorBlock rate + keccakF) +
    len / rate * 101 + (blocks - 1) * (keccakF + 80) +
    blocks * (rate / 8 * (storeLE64 + 99) + 62)

end Gas

theorem shake_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {m : ByteArray} {rate ptr len out blocks : Nat}
    (hrate : rate = 136 ∨ rate = 168) (hblocks : 1 ≤ blocks ∧ blocks ≤ 6)
    (hrc : RCTable m)
    (hin : ZETA ≤ ptr) (hinPad : ptr + len ≤ PADB ∨ PADB + 192 ≤ ptr)
    (hout : ZETA ≤ out) (houtPad : out + blocks * rate + 32 ≤ PADB ∨ PADB + 192 ≤ out)
    (hdisj : ptr + len ≤ out ∨ out + blocks * rate + 32 ≤ ptr)
    (hmem : ptr + len + 32 ≤ 32 * s.activeWords.toNat ∧
      out + blocks * rate + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', BytesAt m' out (Fips202.squeeze rate
          (Fips202.absorb rate (Fips202.pad rate 0x1F (MachineState.readPadded m ptr len)))
          blocks) ∧
      FrameExcept m m' [(ST, RC), (PADB, PADB + 192), (out, out + blocks * rate + 24)] ∧
      Call s Entry.shake [wd rate, wd ptr, wd len, wd out, wd blocks] ret tail m [] m'
        (Gas.shake rate len blocks) := by
  have hrp : 0 < rate := by omega
  have hmsz := EvmProof.Memory.readPadded_size m ptr len
  -- full blocks come straight from memory
  obtain ⟨M, hL, hrcM, hF, hR⟩ := Shake.absorb_phase hs hr hrc (out := out) (blocks := blocks)
    hrate hin hmem.1
    (padded := Fips202.pad rate 0x1F (MachineState.readPadded m ptr len)) (fun i hi => by
      have := Nat.div_mul_le_self len rate
      rw [Shake.byteAt_pad_lt _ _ _ (by omega), Shake.byteAt_readPadded, if_pos (by omega)])
  -- the padded block
  obtain ⟨M', hL', hrc', hF', hR'⟩ := Shake.pad_phase hs hr (out := out) (blocks := blocks)
    hrate hin hinPad hmem.1 hL hrcM hF
  rw [← Shake.absorbPre_succ, ← Shake.absorb_eq _ _ _ hrp
    (by rw [Shake.pad_size _ _ hrp, hmsz])] at hL'
  -- squeeze
  obtain ⟨Mf, hB, hFf, hRf⟩ := Shake.squeeze_phase hs hr (ptr := ptr) (len := len)
    (last := 78464 + (rate - 1)) (rem := len - len / rate * rate) (full := len / rate)
    hrate hblocks hout hmem.2 hL' hrc'
  refine ⟨Mf, hB, Shake.frame_cover (Infra.FrameExcept.trans (Infra.FrameExcept.trans hF hF')
    hFf) (by frame_omega), ?_⟩
  rw [Infra.call_iff, Entry.shake]
  exact (((hR.trans hR').trans hRf).of_eq (by simp) (by simp)).mono
    (Nat.le_of_eq (by unfold Gas.shake; ring))

end MlDsa44.Proofs
