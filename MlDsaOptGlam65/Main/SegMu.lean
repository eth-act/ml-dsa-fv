import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Fn.Keccak
import MlDsaOptGlam65.Fn.Sponge
import MlDsaOptGlam65.Main.Mu.Run
import MlDsaOptGlam65.Main.Frame
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Hand-written: v4's statement (`MlDsaOpt65/Main/SegMu.lean`), the proof adapted to the
42-call schedule's μ (blocks in `Main/Mu/{Cext,Long,Run}`). -/
set_option warningAsError true
/-! # Segment `5017 … 5843`: μ

`|M| ≤ 69` (`CALLDATASIZE < 0x14d3`): the eight `MU` lanes (μ squeezed once by
`mub0` / `cext [MU, 2, 8]`, valid for one-block messages) replicated into
`FIN[0, 8)`. Otherwise (`hash_mu`): μ's sponge after block 0 is slot 2 of the
state image at `MUIMG` (`MuKs`); `MCOPY` restores it into `KS`, `cext [KS, 2, 25]`
extracts it in place, the lanes are replicated for `kf1` (`NOT` on complemented
lanes), block 1 is absorbed (calldata `0x14d3`), the `kf1` / `absorb17` loop
absorbs the further full blocks, the final permutation's lanes `0 … 7` go to
`FIN`. -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra
open MlDsaOptGlam65.Proofs.S6Mu

/-- `avoids_tac` on the 65 layout constants. -/
local macro "avoids65" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true,
    KS, KB, NNEG, TBL, CW, BASES, IDX, ACC, HP, FIN, CB, KZ]
  omega))

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5017 [flag b] m) (callState s 5843 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  -- the invariant from any frame avoiding the Keccak buffers and `FIN`
  have inv6 : ∀ M', FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] →
      FinMu M' s.executionEnv.calldata → RC1Table M' → Inv6 s.executionEnv.calldata M' :=
    fun M' hfr hmu hrc =>
      { rc1 := hrc
        tbl := TblAt.frame hI.tbl hfr (by avoids65)
        hp := HPAt.frame hI.hp hfr (by avoids65)
        acc := AccAt.frame hI.acc hfr (by avoids65)
        cb := CbAt.frame hI.cb hfr (by avoids65)
        fresh := ⟨ZeroOn.frame hI.zCw hfr (by avoids65), ZeroOn.frame hI.zBases hfr (by avoids65),
          ZeroOn.frame hI.zIdx hfr (by avoids65), ZeroOn.frame hI.zNeg hfr (by avoids65)⟩
        fmu := hmu }
  by_cases hsh : mlenOf s.executionEnv.calldata ≤ 69
  · have hlt : s.executionEnv.calldata.size < 5331 := by unfold mlenOf HDR at hsh; omega
    obtain ⟨M', f, fr, r⟩ := mu_short hs b m hfit hlt (fun x hx => by
      rw [hI.mu hsh x hx]; exact MlDsaOpt44.Proofs.le64_lt _ _)
    have hfr : FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] := by
      refine fr.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [KS, KB, KZ, FIN]
    refine ⟨M', inv6 M' hfr (fun x hx => by rw [f x hx, hI.mu hsh x hx]) trivial, ?_⟩
    unfold Gas.pMu; rw [if_pos hsh]; exact r
  · have hlong : 5331 ≤ s.executionEnv.calldata.size := by unfold mlenOf HDR at hsh; omega
    obtain ⟨M0, hI0, r1⟩ := mu_setup hs hcd b hI.muks hI.rc1 hlong
    have hL := muMsgW_size s.executionEnv.calldata hcd
    set L := (muMsgW s.executionEnv.calldata).size with hLdef
    have hn1 : 1 ≤ L / 136 := by omega
    obtain ⟨M, hIn, r2⟩ := mu_loop hs hcd b hI0 (L / 136 - 1)
      (by rw [show 1 + (L / 136 - 1) = L / 136 by omega]; exact Nat.mul_div_le _ _)
    rw [show 1 + (L / 136 - 1) = L / 136 by omega] at hIn r2
    obtain ⟨M', hmu, hrc, hfr, r3⟩ := mu_finish hs b hIn
    refine ⟨M', inv6 M' hfr hmu hrc, ((r1.trans r2).trans r3).mono ?_⟩
    have hk : (mlenOf s.executionEnv.calldata - 70) / 136 = L / 136 - 1 := by
      unfold mlenOf HDR; omega
    unfold Gas.pMu
    rw [if_neg hsh, hk]
    generalize (L / 136 - 1) * (Gas.kf1 + Gas.absorb17 + 88) = P
    generalize Gas.kf1 = k1
    omega

end MlDsaOptGlam65.Proofs
