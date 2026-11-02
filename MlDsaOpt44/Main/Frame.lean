import MlDsaOpt44.Main.Inv
set_option warningAsError true
/-!
# Transporting memory facts across calls

Every predicate of the main-flow invariants reads a fixed footprint;
`X.frame` transports it across a `FrameExcept m m' rs` whose ranges avoid
that footprint (`Avoids rs lo hi`, discharged by `avoids_tac` on the layout
constants).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- Close `Avoids rs lo hi` for literal layout ranges. -/
macro "avoids_tac" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true,
    KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW, ABUF, FL, ZH, BASES, IDX, ACC, HP, FIN,
    RHO1, CB, TRL, MU, BK, TT, SP, TOP, KZ, SB, LIM, SC, SAVE0, SAVE1]
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

theorem RC4Table.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : RC4Table m)
    (h : FrameExcept m m' rs) (ha : Avoids rs RC4 (RC4 + 768)) : RC4Table m' := fun i hi => by
  rw [word_frame h ha (by omega) (by omega)]; exact hr i hi

theorem RC1Table.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : RC1Table m)
    (h : FrameExcept m m' rs) (ha : Avoids rs RC1 (RC1 + 768)) : RC1Table m' := fun i hi => by
  rw [word_frame h ha (by omega) (by omega)]; exact hr i hi

theorem TblAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : TblAt m)
    (h : FrameExcept m m' rs) (ha : Avoids rs TBL (TBL + 7936)) : TblAt m' := fun i hi => by
  rw [word_frame h ha (by omega) (by omega)]; exact hr i hi

theorem HPAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : HPAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs HP (HP + 8192)) : HPAt m' cd :=
  ⟨fun t ht => by rw [word_frame h ha (by omega) (by omega)]; exact hr.1 t ht,
   fun hh hhh t ht r hr' => by rw [word_frame h ha (by omega) (by omega)]; exact hr.2 hh hhh t ht r hr'⟩

theorem ZAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : ZAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs ZH (ZH + 8192)) : ZAt m' cd := fun t ht => by
  rw [word_frame h ha (by omega) (by omega)]; exact hr t ht

theorem ZHatAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : ZHatAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs ZH (ZH + 8192)) : ZHatAt m' cd := fun k hk t ht => by
  rw [word_frame h ha (a := ZH + 32 * t) (by omega) (by omega)]; exact hr k hk t ht

theorem Rho1At.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : Rho1At m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs RHO1 (RHO1 + 256)) : Rho1At m' cd := fun x hx => by
  rw [word_frame h ha (a := RHO1 + 32 * x) (by omega) (by omega),
    word_frame h ha (a := RHO1 + 32 * (4 + x)) (by omega) (by omega)]
  exact hr x hx

theorem AccAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : AccAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs ACC (ACC + 8192)) : AccAt m' cd :=
  fun hA r hr' t ht => by
    rw [word_frame h ha (a := ACC + 32 * t) (by omega) (by omega)]; exact hr hA r hr' t ht

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
  · have : i < 39 := hi
    rw [word_frame h hb (a := BASES + 32 * i) (by omega) (by omega)]; exact h6 i hi

theorem SibFresh.frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : SibFresh m)
    (h : FrameExcept m m' rs) (ha : Avoids rs CW (CW + 8192)) (hb : Avoids rs IDX (IDX + 256))
    (hn : Avoids rs NNEG (NNEG + 64)) : SibFresh m' :=
  ⟨hr.1.frame h ha, hr.2.1.frame h hb, hr.2.2.frame h hn⟩

theorem ColAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {base : Nat} {cd : ByteArray} {col : Nat}
    (hr : ColAt m base cd col) (h : FrameExcept m m' rs) (ha : Avoids rs base (base + 8192)) :
    ColAt m' base cd col := fun hc t ht => by
  rw [word_frame h ha (a := base + 32 * t) (by omega) (by omega)]; exact hr hc t ht

theorem Col3At.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {base : Nat} {cd : ByteArray} {col : Nat}
    (hr : Col3At m base cd col) (h : FrameExcept m m' rs) (ha : Avoids rs base (base + 8192)) :
    Col3At m' base cd col := fun hc t ht r hr' => by
  rw [word_frame h ha (a := base + 32 * t) (by omega) (by omega)]; exact hr hc t ht r hr'

theorem St4At.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {base : Nat}
    {S : Nat → Fips202.SpongeState} (hr : St4At m base S) (h : FrameExcept m m' rs)
    (ha : Avoids rs base (base + 800)) : St4At m' base S := fun x hx => by
  rw [word_frame h ha (a := base + 32 * x) (by omega) (by omega)]; exact hr x hx

theorem ScAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {cd : ByteArray} (hr : ScAt m cd)
    (h : FrameExcept m m' rs) (ha : Avoids rs SC (SC + 800)) : ScAt m' cd := by
  obtain ⟨S, h1, h2, h3, h4⟩ := hr
  exact ⟨S, h1, h2.frame h ha, h3, h4⟩

end MlDsaOpt44.Proofs
