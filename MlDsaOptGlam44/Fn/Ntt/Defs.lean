import MlDsaOpt44.Fn.Ntt.V4.Top
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/-!
# Support for the glam `ntt` / `intt` proofs

The 4 + 4 kernels (`scripts/opt_ntt_glam.py`) run v4's butterflies, bias
interval, Shoup and Montgomery products and fused UseHint word, so the lane
semantics and per-layer lemmas of the v4 proofs apply unchanged
(`MlDsaOpt44/Fn/Ntt/V4/{Defs,Sem,Step}.lean`, `Math/NttV4.lean`); the
generated files (`gen_nttg.py`) use them directly. Here: the glam table
(`TblAt`, `nttRecG`) survives the passes.
-/

namespace MlDsaOptGlam44.Proofs.NttG

open MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.Ntt4
open MlDsaOptGlam44.Proofs

theorem tblG_frame {m m' : ByteArray} {P : Nat} (htbl : TblAt m)
    (hf : FrameExcept m m' [(P, P + 8192)]) (hP : 11776 ≤ P) : TblAt m' := by
  intro i hi
  rw [FrameExcept.word hf (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; unfold TBL; omega)]
  exact htbl i hi

end MlDsaOptGlam44.Proofs.NttG
