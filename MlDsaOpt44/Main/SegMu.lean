import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Keccak
import MlDsaOpt44.Fn.Sponge
import MlDsaOpt44.Main.Mu.Proof
set_option warningAsError true
/-! # Segment `5075 … 5876`: μ

`|M| ≤ 69`: μ's lanes in `MU` (squeezed from the SIMD slot), replicated into
`FIN[0, 8)`. Otherwise (`hash_mu`): μ's sponge after block 0 is slot 1 of the
saved image `SC`; it is copied to `KS`, extracted in place (`cext`, 25 lanes),
replicated for `kf1`, and the remaining blocks are absorbed by the `kf1` /
`absorb17` loop; the final permutation's lanes 0 … 7 go to `FIN`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5075 [flag b] m) (callState s 5876 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hl : 3732 ≤ s.executionEnv.calldata.size := hcd
  -- the invariant from any frame avoiding the Keccak buffers and `FIN`
  have inv6 : ∀ M', FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] →
      FinMu M' s.executionEnv.calldata → RC1Table M' → Inv6 s.executionEnv.calldata M' :=
    fun M' hfr hmu hrc =>
      { rc4 := hI.rc4.frame hfr (by avoids_tac)
        rc1 := hrc
        tbl := hI.tbl.frame hfr (by avoids_tac)
        hp := hI.hp.frame hfr (by avoids_tac)
        acc := hI.acc.frame hfr (by avoids_tac)
        cb := fun x hx => by
          rw [word_frame hfr (lo := CB) (hi := CB + 544) (by avoids_tac) (by omega) (by omega)]
          exact hI.cb x hx
        sc := hI.sc.frame hfr (by avoids_tac)
        fresh := SibFresh.frame ⟨hI.zCw, hI.zIdx, hI.zNeg⟩ hfr (by avoids_tac) (by avoids_tac)
          (by avoids_tac)
        fmu := hmu }
  by_cases hsh : mlenOf s.executionEnv.calldata ≤ 69
  · have hlt : s.executionEnv.calldata.size < 3802 := by unfold mlenOf at hsh; omega
    obtain ⟨M', f, fr, r⟩ := mu_short hs b m hfit hlt (fun x hx => by
      rw [hI.mu hsh x hx]; exact le64_lt _ _)
    have hfr : FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] := by
      refine fr.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [KS, KB, KZ, FIN]
    refine ⟨M', inv6 M' hfr (fun x hx => by rw [f x hx, hI.mu hsh x hx])
      (hI.rc1.frame fr (by avoids_tac)), ?_⟩
    unfold Gas.pMu; rw [if_pos hsh]; exact r
  · have hlong : 3802 ≤ s.executionEnv.calldata.size := by unfold mlenOf at hsh; omega
    obtain ⟨M0, hI0, r1⟩ := mu_setup hs hcd b hI.sc hI.rc1 hlong
    have hL := muMsgW_size s.executionEnv.calldata hcd
    set L := (muMsgW s.executionEnv.calldata).size with hLdef
    have hn1 : 1 ≤ L / 136 := by omega
    obtain ⟨M, hIn, r2⟩ := mu_loop hs hcd b hI0 (L / 136 - 1)
      (by rw [show 1 + (L / 136 - 1) = L / 136 by omega]; exact Nat.mul_div_le _ _)
    rw [show 1 + (L / 136 - 1) = L / 136 by omega] at hIn r2
    obtain ⟨M', hmu, hrc, hfr, r3⟩ := mu_finish hs b hIn
    refine ⟨M', inv6 M' hfr hmu hrc, ((r1.trans r2).trans r3).mono ?_⟩
    have hk : (mlenOf s.executionEnv.calldata - 70) / 136 + 1 = L / 136 - 1 + 1 := by
      unfold mlenOf; omega
    unfold Gas.pMu
    rw [if_neg hsh, hk, Nat.add_mul, Nat.one_mul]
    generalize (L / 136 - 1) * (Gas.kf1 + Gas.absorb17 + 88) = P
    generalize Gas.kf1 = k1
    generalize Gas.absorb17 = a17
    generalize Gas.cext 25 = c25
    omega

end MlDsaOpt44.Proofs
