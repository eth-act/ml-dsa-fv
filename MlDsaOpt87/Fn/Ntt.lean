import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
import MlDsaOpt87.Fn.Ntt.Top
import MlDsaOpt87.Fn.Ntt2.Top
import MlDsa.Bridge44
set_option warningAsError true
/-!
# Four-lane NTT and inverse NTT (ML-DSA-87)

The kernels are byte-identical to ML-DSA-44 up to jump targets
(`MlDsaOpt44/Fn/Ntt.lean` explains the algorithm and the bounds). The 44 proof
(`MlDsaOpt44/Fn/Ntt/*`) is pinned to one polynomial address per kernel, so it is
ported twice with `scripts/proofgen_port.py 87` (pure files `Defs`, `Sem`,
`Step`, `Model` are imported from 44):

* `Fn/Ntt/*` (namespace `NttW`): `ntt` at `ZH = 0x8000`, `intt` at `ACC = 0xc900`;
* `Fn/Ntt2/*` (namespace `NttW2`): `ntt` at `ZH2 = 0xa000`, `intt` at `ACC + 0x2000 = 0xe900`.

The contracts below take the address `p` as an argument restricted to these two
values, which are exactly the call sites of `MlDsaOpt/87/opt.asm`:
`ntt` from `main` at pcs 3118–3127 (`ZH`) and 3129–3138 (`ZH2`); `intt` from `hash_mu` at pcs
6646–6655 (`ACC`) and 6685–6694 (`ACC + 0x2000`). They are stated against the parametric
`MlDsa.Fips204.ntt` / `nttInv` (equal to the ML-DSA-44 ones by `MlDsa/Bridge44.lean`).

**Regeneration** (from the repository root; then re-apply the `-- port:` hand edits):

```
python3 scripts/proofgen_port.py 87 --sub 43264=51456 --sub 44288=52480 \
    --sub 66080=91680 --sub 60000=70000 \
    MlDsaOpt44/Fn/Ntt/Ctl.lean \
    MlDsaOpt44/Fn/Ntt/FwdA.lean \
    MlDsaOpt44/Fn/Ntt/FwdB.lean \
    MlDsaOpt44/Fn/Ntt/FwdC.lean \
    MlDsaOpt44/Fn/Ntt/InvA.lean \
    MlDsaOpt44/Fn/Ntt/InvB.lean \
    MlDsaOpt44/Fn/Ntt/InvC.lean \
    MlDsaOpt44/Fn/Ntt/Passes.lean \
    MlDsaOpt44/Fn/Ntt/Top.lean
python3 scripts/proofgen_port.py 87 --sub 32768=40960 --sub 33792=41984 \
    --sub 43264=59648 --sub 44288=60672 --sub 66080=91680 --sub 60000=70000 \
    --sub NttW=NttW2 --path Fn/Ntt/=Fn/Ntt2/ \
    MlDsaOpt44/Fn/Ntt/Ctl.lean \
    MlDsaOpt44/Fn/Ntt/FwdA.lean \
    MlDsaOpt44/Fn/Ntt/FwdB.lean \
    MlDsaOpt44/Fn/Ntt/FwdC.lean \
    MlDsaOpt44/Fn/Ntt/InvA.lean \
    MlDsaOpt44/Fn/Ntt/InvB.lean \
    MlDsaOpt44/Fn/Ntt/InvC.lean \
    MlDsaOpt44/Fn/Ntt/Passes.lean \
    MlDsaOpt44/Fn/Ntt/Top.lean
```

Hand edits: in both `Top.lean` the named base (`ZH`/`ACC`) becomes the literal
base and two closing `rfl`s are dropped (`-- port: literal base`). In every
`Fn/Ntt2/*` file the `open` after `namespace …NttW2` must also open
`MlDsaOpt44.Proofs.NttW` (the second command emits only `open MlDsaOpt44.Proofs`,
because `NttW2` has no 44 twin); the files also carry `-- port: second instance` on
renamed imports/namespaces (not needed with `--path`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- **ntt**: `[p, ret]` with `p ∈ {ZH, ZH2}`, in place on the four lane polynomials at `p`. -/
theorem ntt_call {s : State} (hs : Ctx s) {p : Nat} (hp : p = ZH ∨ p = ZH2) {ret : Nat}
    {tail : List UInt256} (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (p + 32 * t)) k < 2 ^ 25) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (p + 32 * t)) k < 2 ^ 28 ∧
          ((lane (word m' (p + 32 * t)) k : Int) - (Fips204.ntt (lanesPoly m p k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(p, p + 8192)] ∧
      Call s Entry.ntt [wd p] ret tail m [] m' Gas.ntt := by
  rw [Bridge44.ntt_eq, Bridge44.q_eq]
  rcases hp with rfl | rfl
  · exact NttW.ntt_full hs hr m htbl
  · exact NttW2.ntt_full hs hr m htbl

/-- **intt**: `[p, ret]` with `p ∈ {ACC, ACC + 0x2000}`, in place on the four lane
polynomials at `p`. -/
theorem intt_call {s : State} (hs : Ctx s) {p : Nat} (hp : p = ACC ∨ p = ACC + 0x2000)
    {ret : Nat} {tail : List UInt256} (hr : RetOK Stack.intt ret tail) (m : ByteArray)
    (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (p + 32 * t)) k < 2 ^ 58) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (p + 32 * t)) k < 2 ^ 27 ∧
          ((lane (word m' (p + 32 * t)) k : Int) - (Fips204.nttInv (lanesPoly m p k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(p, p + 8192)] ∧
      Call s Entry.intt [wd p] ret tail m [] m' Gas.intt := by
  rw [Bridge44.nttInv_eq, Bridge44.q_eq]
  rcases hp with rfl | rfl
  · exact NttW.intt_full hs hr m htbl
  · exact NttW2.intt_full hs hr m htbl

end MlDsaOpt87.Proofs
