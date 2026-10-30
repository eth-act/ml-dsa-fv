import MlDsa44.Proofs.Fn.Ntt
import MlDsa44.Proofs.Fn.Unpack
import MlDsa44.Proofs.Fn.Decode.HintLoop
import MlDsa44.Proofs.Fn.Decode.ZLoop
/-!
# Signature decoding: `decodeHint` and `decodeZ`

Calldata layout: `pk = [0, 1312)`, `σ = [1312, 3732)` with `c̃ = [1312, 1344)`,
`z = [1344, 3648)` (four 576-byte polynomials, 18 bits per coefficient) and
`h = [3648, 3732)` (`ω = 80` index bytes, then `k = 4` counts).

Yul:
* `decodeHint() -> good`: zero `HB`, then Algorithm 21 with every
  `return ⊥` turned into `good := 0` and the scan clamped so it stays
  bounded; set bytes go to `HB + 256 i + y`;
* `decodeZ() -> good`: for each `z[i]`, unpack, check `β < raw < 2γ₁ − β`
  (`‖z‖∞ < γ₁ − β`), store `(γ₁ − raw) mod q` at `ZH + POLY i`, then NTT.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budgets: exact worst cases, proved by the contracts below.
namespace Gas

/-- Worst case: one outer iteration runs all 80 indices with every order check
failing, the other three take the out-of-range branch. -/
def decodeHint : Nat := 16340

/-- Exact cost when every coefficient fails the norm check (the `good := 0`
branch costs 7 more gas per coefficient). -/
def decodeZ : Nat := 4 * (256 * (unpack + 176) + ntt + 117) + 48

end Gas

/-- The signature field of EIP-8355 calldata. -/
def sigOf (cd : ByteArray) : ByteArray := cd.extract 1312 3732

/-- The public-key field of EIP-8355 calldata. -/
def pkOf (cd : ByteArray) : ByteArray := cd.extract 0 1312

/-- `z` as decoded by `sigDecode`. -/
def zOf (cd : ByteArray) : Array Fips204.Poly := (Fips204.sigDecode (sigOf cd)).2.1

/-- The hint field of the signature. -/
def hintBytesOf (cd : ByteArray) : ByteArray := cd.extract 3648 3732

theorem decodeHint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.decodeHint ret tail) (m : ByteArray) (hcd : 3732 ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ i, i < 4 → ∀ j, j < 256 → byteAt m' (HB + 256 * i + j) ≤ 1) ∧
      (∀ h, Fips204.hintBitUnpack (hintBytesOf s.executionEnv.calldata) = some h →
        HintAt m' h) ∧
      FrameExcept m m' [(HB, HB + 0x400)] ∧
      Call s Entry.decodeHint [] ret tail m
        [flag (Fips204.hintBitUnpack (hintBytesOf s.executionEnv.calldata)).isSome] m'
        Gas.decodeHint := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.decodeHint, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : 2535 ≤ s.activeWords.toNat := hs.sized
  have hmem : 77280 ≤ 32 * s.activeWords.toNat := by omega
  -- zero `HB`
  let I : Nat → State := fun j =>
    callState s 3791 (wd j :: wd 1 :: wd ret :: tail) (Infra.storeWords m 76256 (fun _ => 0) j)
  have hz : Infra.Reach (callState s 3786 (wd 0 :: wd ret :: tail) m)
      (callState s 3826 (wd 0 :: wd 0 :: wd 1 :: wd ret :: tail) (Decode.zeroHB m))
      (8 + 32 * 71 + 33) :=
    ((Decode.hint_entry hs htl m).trans
      (Infra.Reach.loop (I := I) 32 (fun j hj => Decode.hint_zero hs htl m hj haw hmem))).trans
      (Decode.hint_zeroExit hs htl _)
  -- the outer loop, four iterations
  obtain ⟨M1, hi1, hl1, hu1, r1⟩ := Decode.hint_outer (ret := ret) hs htl haw hmem hcd Decode.hs0
    (Decode.inv_zero m) (by simp [Decode.hs0]) (i := 0) (by norm_num)
  obtain ⟨M2, hi2, hl2, hu2, r2⟩ := Decode.hint_outer (ret := ret) hs htl haw hmem hcd _
    hi1 hu1 (i := 1) (by norm_num)
  obtain ⟨M3, hi3, hl3, hu3, r3⟩ := Decode.hint_outer (ret := ret) hs htl haw hmem hcd _
    hi2 hu2 (i := 2) (by norm_num)
  obtain ⟨M4, hi4, hl4, hu4, r4⟩ := Decode.hint_outer (ret := ret) hs htl haw hmem hcd _
    hi3 hu3 (i := 3) (by norm_num)
  generalize hst4 : (Decode.outerStep (Decode.yOf s) (Decode.outerStep (Decode.yOf s) (Decode.outerStep (Decode.yOf s) (Decode.outerStep (Decode.yOf s) Decode.hs0 0) 1) 2) 3) = st4 at hi4 hl4 hu4 r4
  -- the final scan
  have hfin := Decode.hint_final (ret := ret) hs htl hcd M4 (a := st4.index) st4.good
    (80 - st4.index) (by omega)
  rw [show st4.index + (80 - st4.index) = 80 by omega] at hfin
  have hout := Decode.hint_outerExit (ret := ret) hs htl M4 (flag st4.good) (a := st4.index)
  have hex := Decode.hint_finExit hs htl M4
    (flag (st4.good && (List.range' st4.index (80 - st4.index)).all (fun idx => Decode.yOf s idx == 0)))
    (a := st4.index) hr
  have hrun := (((((hz.trans r1).trans r2).trans r3).trans r4).trans hout).trans (hfin.trans hex)
  -- the spec
  have hspec := Decode.hintBitUnpack_eq (hintBytesOf s.executionEnv.calldata)
  have hy : (fun j => (hintBytesOf s.executionEnv.calldata)[j]!.toNat) = Decode.yOf s := by
    unfold Decode.yOf hintBytesOf; rfl
  rw [hy] at hspec
  have hgood : Decode.hintGood (Decode.yOf s) =
      (st4.good && (List.range' st4.index (80 - st4.index)).all (fun idx => Decode.yOf s idx == 0)) := by
    rw [← hst4]; rfl
  have hall : (Decode.outerAll (Decode.yOf s)).H = st4.H := by rw [← hst4]; rfl
  obtain ⟨hwf, hat, hfr⟩ := hi4
  refine ⟨M4, fun i hi j hj => ?_, fun h hh => ?_, hfr, ?_⟩
  · have h1 := hat i hi j hj
    rcases (hwf.2 i hi).2 j hj with h | h <;> rw [h] at h1 <;> omega
  · rw [hspec] at hh
    split at hh
    · cases hh; rw [hall]; exact hat
    · cases hh
  · rw [Infra.call_iff, Entry.decodeHint, Gas.decodeHint]
    have hres : (Fips204.hintBitUnpack (hintBytesOf s.executionEnv.calldata)).isSome =
        (st4.good && (List.range' st4.index (80 - st4.index)).all (fun idx => Decode.yOf s idx == 0)) := by
      rw [hspec, ← hgood]; split <;> simp_all
    rw [hres]
    refine (hrun.mono ?_).of_eq (by simp) (by simp)
    exact Decode.hint_cost (Nat.zero_le _) hl2 hl3 hl4 hu4

theorem decodeZ_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.decodeZ ret tail) {m : ByteArray} (hz : ZetaTable m)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ i, i < 4 →
        PolyAt m' (ZH + POLY * i)
          (Fips204.ntt ((zOf s.executionEnv.calldata)[i]!.map (· % (Fips204.q : Int)))) ∧
        Reduced (Fips204.ntt ((zOf s.executionEnv.calldata)[i]!.map (· % (Fips204.q : Int))))) ∧
      FrameExcept m m' [(ZH, ZH + 4 * POLY)] ∧
      Call s Entry.decodeZ [] ret tail m
        [flag (Fips204.normBelow (zOf s.executionEnv.calldata)
          (Fips204.gamma1 - Fips204.beta))] m'
        Gas.decodeZ := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth
    have h128 : Stack.decodeZ = 128 := rfl
    omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : 2535 ≤ s.activeWords.toNat := hs.sized
  have hmem : 43520 ≤ 32 * s.activeWords.toNat := by omega
  obtain ⟨M, hpolys, -, hfr, hreach⟩ :=
    Decode.z_outer_loop hs hr htl haw hmem hcd hz 4 le_rfl
  have he := Decode.z_entry (ret := ret) hs htl m
  have hx := Decode.z_exit hs htl M (flag (Decode.zAll s.executionEnv.calldata 4)) hr
  have hnorm : Fips204.normBelow (zOf s.executionEnv.calldata) (Fips204.gamma1 - Fips204.beta) =
      Decode.zAll s.executionEnv.calldata 4 := Decode.normBelow_eq hcd
  have hfz : ∀ i, Decode.fz s.executionEnv.calldata i =
      (zOf s.executionEnv.calldata)[i]!.map (· % (Fips204.q : Int)) := fun _ => rfl
  refine ⟨M, fun i hi => ?_, hfr, ?_⟩
  · rw [← hfz]; exact hpolys i hi
  · rw [Infra.call_iff, Entry.decodeZ, hnorm]
    exact ((he.trans (hreach.trans hx)).mono (Decode.z_cost Gas.decodeZ rfl)).of_eq (by simp) (by simp)

end MlDsa44.Proofs
