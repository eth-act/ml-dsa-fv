import MlDsa44.Proofs.Fn.Decode.ZBlocks
import MlDsa44.Proofs.Math.Decode.Z
import MlDsa44.Proofs.Fn.Ntt
import MlDsa44.Proofs.Fn.Unpack
set_option warningAsError true
/-!
# The loops of `decodeZ`

The inner loop stores `(γ₁ − raw) mod q` for the 256 coefficients of `z[i]`
(one `unpack` call each); the outer loop then runs `ntt` on the polynomial.
-/

namespace MlDsa44.Proofs.Decode

open EvmSemantics
open EvmSemantics.EVM

/-- `z[i]` reduced into `[0, q)`, as stored before the NTT. -/
def fz (cd : ByteArray) (i : Nat) : Fips204.Poly :=
  (Fips204.sigDecode (cd.extract 1312 3732)).2.1[i]!.map (· % (Fips204.q : Int))

/-- The word the inner loop stores for coefficient `j` of `z[i]`. -/
def zval (cd : ByteArray) (i j : Nat) : Nat := (131072 + (8380417 - rawZ cd i j)) % 8380417

theorem fz_size (cd : ByteArray) {i : Nat} (hi : i < 4) : (fz cd i).size = 256 := by
  unfold fz; rw [Array.size_map, sigDecode_z_get cd hi, bitUnpack_size]

theorem fz_get {cd : ByteArray} (hcd : 3732 ≤ cd.size) {i j : Nat} (hi : i < 4) (hj : j < 256) :
    (fz cd i)[j]! = ((131072 : Int) - rawZ cd i j) % 8380417 := by
  have hs : j < ((Fips204.sigDecode (cd.extract 1312 3732)).2.1[i]!).size := by
    rw [sigDecode_z_get cd hi, bitUnpack_size]; exact hj
  unfold fz
  rw [getElem!_pos _ j (by rw [Array.size_map]; exact hs), Array.getElem_map,
    ← getElem!_pos _ j hs, sigDecode_z_coeff hcd hi hj]
  rfl

theorem polyAt_fz {cd : ByteArray} (hcd : 3732 ≤ cd.size) {i : Nat} (hi : i < 4) (M : ByteArray)
    (base : Nat) :
    PolyAt (Infra.storeWords M base (fun j => (131072 + (8380417 - rawZ cd i j)) % 8380417) 256)
      base (fz cd i) := by
  refine ⟨fz_size cd hi, fun j hj => ?_⟩
  rw [Infra.word_storeWords (v := fun j => (131072 + (8380417 - rawZ cd i j)) % 8380417)
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) 256 hj,
    fz_get hcd hi hj]
  have := rawZ_lt cd i j
  omega

theorem reduced_fz {cd : ByteArray} (hcd : 3732 ≤ cd.size) {i : Nat} (hi : i < 4) :
    Reduced (fz cd i) := by
  intro j hj
  rw [fz_get hcd hi hj]
  show _ ∧ _ < (8380417 : Int)
  omega

section
variable {s : State} {ret : Nat} {tail : List UInt256}

/-- Per-polynomial cost: outer head, 256 inner iterations, `ntt`. -/
def zIter : Nat := 43 + 256 * (65 + Gas.unpack + 111) + 46 + Gas.ntt + 28

theorem zIter_succ (n : Nat) :
    n * zIter + (43 + (256 * (65 + Gas.unpack + 111) + (46 + (Gas.ntt + 28)))) =
      (n + 1) * zIter := by
  rw [Nat.add_mul, Nat.one_mul]
  unfold zIter
  omega

theorem z_cost (g : Nat) (hg : g = 4 * (256 * (Gas.unpack + 176) + Gas.ntt + 117) + 48) :
    8 + (4 * zIter + 40) ≤ g := by
  subst hg
  unfold zIter
  omega

/-- The inner loop over the 256 coefficients of `z[i]`. -/
theorem z_inner (hs : Ctx s) (hr : RetOK Stack.decodeZ ret tail) (htl : tail.length ≤ 960)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 43520 ≤ 32 * s.activeWords.toNat)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (M : ByteArray) {i : Nat} (hi : i < 4) (g : Bool) :
    Infra.Reach
      (callState s 4024 (wd 0 :: wd (10720 + i * 8192) :: wd i :: flag g :: wd ret :: tail) M)
      (callState s 4024 (wd 256 :: wd (10720 + i * 8192) :: wd i ::
        flag (g && (List.range 256).all (okZ s.executionEnv.calldata i)) :: wd ret :: tail)
        (Infra.storeWords M (10720 + i * 8192)
          (fun j => (131072 + (8380417 - rawZ s.executionEnv.calldata i j)) % 8380417) 256))
      (256 * (65 + Gas.unpack + 111)) := by
  let cd := s.executionEnv.calldata
  let V : Nat → Nat := fun j => (131072 + (8380417 - rawZ cd i j)) % 8380417
  let I : Nat → State := fun j =>
    callState s 4024 (wd j :: wd (10720 + i * 8192) :: wd i ::
      flag (g && (List.range j).all (okZ cd i)) :: wd ret :: tail)
      (Infra.storeWords M (10720 + i * 8192) V j)
  have hbody : ∀ j, j < 256 → Infra.Reach (I j) (I (j + 1)) (65 + Gas.unpack + 111) := by
    intro j hj
    let G := flag (g && (List.range j).all (okZ cd i))
    let Mj := Infra.storeWords M (10720 + i * 8192) V j
    have h1 := z_call (ret := ret) (i := i) hs htl Mj G hj
    have hcall := Infra.call_iff.mp (unpack_call hs
      (hr.callee (B' := Stack.unpack) (ret' := 4055)
        (extra := [wd j, wd (10720 + i * 8192), wd i, G, wd ret])
        (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
      Mj (off := 1344 + 576 * i) (n := 576) (i := j) (c := 18) ⟨by decide, by decide⟩
      (by omega) (by omega))
    have h12 := h1.trans (hcall.of_eq (by simp [Entry.unpack]) rfl)
    by_cases hok : 78 < rawZ cd i j ∧ rawZ cd i j < 262066
    · have h3 := z_storeOK (ret := ret) hs htl M G (rawZ cd i) hi hj hok haw hmem
      refine ((h12.trans (h3.of_eq ?_ rfl)).mono (by omega)).of_eq rfl ?_
      · rfl
      · have : okZ cd i j = true := by simp [okZ, hok]
        simp [I, G, List.range_succ, List.all_append, this, V]
    · have h3 := z_storeBad (ret := ret) hs htl M G (rawZ cd i) hi hj hok (rawZ_lt cd i j) haw hmem
      refine ((h12.trans (h3.of_eq ?_ rfl)).mono le_rfl).of_eq rfl ?_
      · rfl
      · have : okZ cd i j = false := by simp [okZ, hok]
        have hf : flag (g && (List.range (j + 1)).all (okZ cd i)) = wd 0 := by
          simp [List.range_succ, List.all_append, this, flag]
        simp only [I, hf]
        rfl
  have h := Infra.Reach.loop (I := I) 256 hbody
  exact h.of_eq (by simp [I]) rfl

/-- The outer loop after `n` polynomials. -/
theorem z_outer_loop (hs : Ctx s) (hr : RetOK Stack.decodeZ ret tail) (htl : tail.length ≤ 960)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 43520 ≤ 32 * s.activeWords.toNat)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) {m : ByteArray} (hz : ZetaTable m) :
    ∀ n, n ≤ 4 → ∃ M,
      (∀ i, i < n → PolyAt M (ZH + POLY * i) (Fips204.ntt (fz s.executionEnv.calldata i)) ∧
        Reduced (Fips204.ntt (fz s.executionEnv.calldata i))) ∧
      ZetaTable M ∧ FrameExcept m M [(ZH, ZH + 4 * POLY)] ∧
      Infra.Reach (callState s 4005 (wd 0 :: wd 1 :: wd ret :: tail) m)
        (callState s 4005 (wd n :: flag (zAll s.executionEnv.calldata n) :: wd ret :: tail) M)
        (n * zIter)
  | 0, _ => ⟨m, fun _ h => absurd h (Nat.not_lt_zero _), hz, Infra.FrameExcept.refl _ _,
      (Infra.Reach.refl _).of_eq rfl (by simp [zAll, flag])⟩
  | n + 1, hn => by
    obtain ⟨M, hpolys, hzM, hfr, hreach⟩ := z_outer_loop hs hr htl haw hmem hcd hz n (by omega)
    have hn4 : n < 4 := by omega
    let base := 10720 + n * 8192
    let V : Nat → Nat := fun j => (131072 + (8380417 - rawZ s.executionEnv.calldata n j)) % 8380417
    let M' := Infra.storeWords M base V 256
    let G := flag (zAll s.executionEnv.calldata n && (List.range 256).all (okZ s.executionEnv.calldata n))
    have h1 := z_outer (ret := ret) hs htl M (flag (zAll s.executionEnv.calldata n)) hn4
    have h2 := z_inner hs hr htl haw hmem hcd M hn4 (zAll s.executionEnv.calldata n)
    have h3 := z_innerExit (ret := ret) (i := n) hs htl M' G
    -- `M'` holds `fz s.executionEnv.calldata n`
    have hfM' : FrameExcept M M' [(base, base + 32 * 256)] := Infra.FrameExcept.storeWords M base V 256
    have hzM' : ZetaTable M' :=
      Infra.ZetaTable.frame hzM hfM' (by simp [Infra.Avoids, ZETA, POLY, base])
    obtain ⟨M'', hpoly, hred, hfr'', hcall⟩ := ntt_call hs
      (hr.callee (B' := Stack.ntt) (ret' := 4118) (extra := [wd base, wd n, G, wd ret])
        (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
      (polyAt_fz hcd hn4 M base) (reduced_fz hcd hn4) hzM'
      (by simp only [ZETA, POLY, base]; omega) (by simp only [POLY, base]; omega)
    have h4 := z_afterNtt (ret := ret) (i := n) hs htl M'' G
    have hcallR : Infra.Reach
        (callState s 3107 (wd base :: wd 4118 :: wd base :: wd n :: G :: wd ret :: tail) M')
        (callState s 4118 (wd base :: wd n :: G :: wd ret :: tail) M'') Gas.ntt :=
      (Infra.call_iff.mp hcall).of_eq (by simp [Entry.ntt]; rfl) (by simp)
    have hall : zAll s.executionEnv.calldata (n + 1) = (zAll s.executionEnv.calldata n && (List.range 256).all (okZ s.executionEnv.calldata n)) := by
      unfold zAll
      rw [List.range_succ (n := n), List.all_append]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
    refine ⟨M'', fun i hi => ?_, Infra.ZetaTable.frame hzM' hfr''
        (by simp [Infra.Avoids, ZETA, POLY, base]), ?_, ?_⟩
    · by_cases hin : i = n
      · subst hin
        refine ⟨?_, hred⟩
        rw [show ZH + POLY * i = base by simp only [ZH, POLY, base]; omega]
        exact hpoly
      · have ⟨hp, hr'⟩ := hpolys i (by omega)
        refine ⟨?_, hr'⟩
        refine Infra.PolyAt.frame (Infra.PolyAt.frame hp hfM' ?_) hfr'' ?_ <;>
          simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, ZH, POLY, base] <;> omega
    · refine Infra.FrameExcept.mono (Infra.FrameExcept.trans hfr
        (Infra.FrameExcept.trans hfM' hfr'')) ?_
      intro r hr
      refine ⟨(ZH, ZH + 4 * POLY), by simp, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [ZH, POLY, base] <;> omega
    · simp only [hall]
      have ha := hcallR.trans h4
      have hb := h3.trans ha
      have hc := h2.trans hb
      have hd := h1.trans hc
      have h := hreach.trans hd
      refine (h.mono (le_of_eq ?_)).of_eq rfl ?_
      · exact zIter_succ n
      · simp only [G]

end

end MlDsa44.Proofs.Decode
