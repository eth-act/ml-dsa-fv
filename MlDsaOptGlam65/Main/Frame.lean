import MlDsaOptGlam65.Main.Inv
import MlDsaOpt65.Main.Frame  -- glam: frame lemmas of the shared v4 predicates
import MlDsaOptGlam44.Main.Frame  -- glam: and of glam 44's tables (`TblAt`, `RC1Table`)
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/Frame.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Transporting memory facts across calls (ML-DSA-65)

Every predicate of the main-flow invariants reads a fixed footprint;
`X.frame` transports it across a `FrameExcept m m' rs` whose ranges avoid
that footprint (`Avoids rs lo hi`, discharged by `avoids_tac` on the layout
constants). `ZeroOn` is the ML-DSA-44 constant (re-exported), so its transport
lemmas here are applied explicitly (`ZeroOn.frame hz h ha`), not by dot notation. As `MlDsaOpt44/Main/Frame.lean`, with the two-table footprints of
ML-DSA-65 (`ZH … ZH + 0x4000`, `ACC … ACC + 0x4000`, `HP … HP + 0x4000`).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- Close `Avoids rs lo hi` for literal layout ranges. -/
macro "avoids_tac" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true,
    KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW, ABUF, FL, ZH, ZH2, BASES, IDX, ACC, HP,
    FIN, RHO1, CB, TRL, MU, BK, TT, SP, TOP, KZ]
  omega))

theorem word_frame {m m' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m m' rs)
    {lo hi : Nat} (ha : Avoids rs lo hi) {a : Nat} (h1 : lo ≤ a) (h2 : a + 32 ≤ hi) :
    word m' a = word m a :=
  FrameExcept.word h (ha.mono h1 h2)

theorem ZeroOn.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {lo hi : Nat}
    (hz : ZeroOn m lo hi) (h : FrameExcept m m' rs) (ha : Avoids rs lo hi) : ZeroOn m' lo hi :=
  fun a h1 h2 => by rw [FrameExcept.byteAt h (ha.mono h1 (by omega))]; exact hz a h1 h2

theorem ZeroOn.mono {m : ByteArray} {lo hi lo' hi' : Nat} (hz : ZeroOn m lo hi)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : ZeroOn m lo' hi' :=
  fun a ha hb => hz a (by omega) (by omega)

set_option linter.unusedVariables false in  -- glam: trivial table
theorem RC4Table.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : RC4Table m)
    (h : FrameExcept m m' rs) (ha : Avoids rs RC4 (RC4 + 768)) : RC4Table m' := trivial  -- glam: no iota table

set_option linter.unusedVariables false in  -- glam: trivial table
theorem RC1Table.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : RC1Table m)
    (h : FrameExcept m m' rs) (ha : Avoids rs RC1 (RC1 + 768)) : RC1Table m' := trivial  -- glam: no iota table

theorem TblAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : TblAt m)
    (h : FrameExcept m m' rs) (ha : Avoids rs TBL (TBL + 7936)) : TblAt m' := fun i hi => by
  rw [word_frame h ha (by omega) (by omega)]; exact hr i hi

theorem HPAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : HPAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs HP (HP + 0x4000)) : HPAt m' cd :=
  ⟨fun g hg t ht => by rw [word_frame h ha (by omega) (by omega)]; exact hr.1 g hg t ht,
   fun hh hhh r hr' t ht => by
    rw [word_frame h ha (a := hpAddr r t) (by unfold hpAddr; omega) (by unfold hpAddr; omega)]
    exact hr.2 hh hhh r hr' t ht⟩

theorem ZAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : ZAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs ZH (ZH + 0x4000)) : ZAt m' cd := fun t ht => by
  rw [word_frame h ha (a := ZH + 32 * t) (by omega) (by omega),
    word_frame h ha (a := ZH2 + 32 * t) (by unfold ZH2 ZH; omega) (by unfold ZH2 ZH; omega)]
  exact hr t ht

theorem zhLane_frame {m m' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m m' rs)
    (ha : Avoids rs ZH (ZH + 0x4000)) {k t : Nat} (hk : k < 5) (ht : t < 256) :
    zhLane m' k t = zhLane m k t := by
  unfold zhLane
  rw [word_frame h ha (a := zhAddr k t) (by unfold zhAddr; omega) (by unfold zhAddr; omega)]

theorem ZHatAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : ZHatAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs ZH (ZH + 0x4000)) : ZHatAt m' cd :=
  fun k hk t ht => by rw [zhLane_frame h ha hk ht]; exact hr k hk t ht

theorem Rho1At.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : Rho1At m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs RHO1 (RHO1 + 320)) : Rho1At m' cd :=
  ⟨fun x hx => by rw [word_frame h ha (a := RHO1 + 32 * x) (by omega) (by omega)]; exact hr.1 x hx,
   fun x hx => by
    rw [word_frame h ha (a := RHO1 + 32 * (4 + x)) (by omega) (by omega)]; exact hr.2 x hx⟩

theorem AccAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : AccAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs ACC (ACC + 0x4000)) : AccAt m' cd := fun hA =>
  ⟨fun g hg k hk t ht => by
    rw [word_frame h ha (a := ACC + 0x2000 * g + 32 * t) (by omega) (by omega)]
    exact (hr hA).1 g hg k hk t ht,
   fun r hr' t ht => by
    rw [word_frame h ha (a := accAddr r t) (by unfold accAddr; omega) (by unfold accAddr; omega)]
    exact (hr hA).2 r hr' t ht⟩

theorem CbAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : CbAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs CB (CB + 1088)) : CbAt m' cd := fun x hx => by
  rw [word_frame h ha (a := CB + 32 * x) (by omega) (by omega)]; exact hr x hx

theorem TrlAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : TrlAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs TRL (TRL + 256)) : TrlAt m' cd := fun x hx => by
  rw [word_frame h ha (a := TRL + 32 * x) (by omega) (by omega)]; exact hr x hx

theorem MuAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : MuAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs MU (MU + 256)) : MuAt m' cd := fun hm x hx => by
  rw [word_frame h ha (a := MU + 32 * x) (by omega) (by omega)]; exact hr hm x hx

theorem FinMu.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : FinMu m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs FIN (FIN + 256)) : FinMu m' cd := fun x hx => by
  rw [word_frame h ha (a := FIN + 32 * x) (by omega) (by omega)]; exact hr x hx

theorem CRep.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {c : Fips204.Poly} (hr : CRep m c)
    (h : FrameExcept m m' rs) (ha : Avoids rs CW (CW + 8192)) (hb : Avoids rs BASES (BASES + 2048))
    (hn : Avoids rs NNEG (NNEG + 32)) : CRep m' c := by
  obtain ⟨h1, h2, ps, h3, h4, h5, h6⟩ := hr
  refine ⟨fun t ht => ?_, ?_, ps, h3, h4, h5, fun i hi => ?_⟩
  · rw [word_frame h ha (a := CW + 32 * t) (by omega) (by omega)]; exact h1 t ht
  · rw [word_frame h hn (a := NNEG) (by omega) (by omega)]; exact h2
  · have : i < 49 := hi
    rw [word_frame h hb (a := BASES + 32 * i) (by omega) (by omega)]; exact h6 i hi

theorem SibFresh.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : SibFresh m)
    (h : FrameExcept m m' rs) (ha : Avoids rs CW (CW + 8192)) (hbs : Avoids rs BASES (BASES + 2048))
    (hb : Avoids rs IDX (IDX + 256)) (hn : Avoids rs NNEG (NNEG + 64)) : SibFresh m' :=
  ⟨ZeroOn.frame hr.1 h ha, ZeroOn.frame hr.2.1 h hbs, ZeroOn.frame hr.2.2.1 h hb,
    ZeroOn.frame hr.2.2.2 h hn⟩

end MlDsaOptGlam65.Proofs
