import MlDsaOptGlam87.Infra
import MlDsaOptGlam87.Fn.Kf4.Main
import MlDsaOptGlam87.Fn.Kf1.Main
import MlDsaOptGlam87.Main
import MlDsaOptGlam87.Fn.Ball
import MlDsaOptGlam87.Fn.Blk
import MlDsaOptGlam87.Fn.Csum
import MlDsaOptGlam87.Fn.Decode
import MlDsaOptGlam87.Fn.Fix
import MlDsaOptGlam87.Fn.Group
import MlDsaOptGlam87.Fn.Hint
import MlDsaOptGlam87.Fn.Keccak
import MlDsaOptGlam87.Fn.Ntt
import MlDsaOptGlam87.Fn.Sponge
import MlDsaOptGlam87.Fn.TBuild
/-! Proofs about the Glamsterdam variant of the gas-optimised ML-DSA-87
bytecode (`MlDsaOpt/87/glam/opt.hex`, EIP-8024 and EIP-7954): the four final
theorems over `Fork.Amsterdam` (`MlDsa87.Amsterdam`), the artifact infrastructure
on `EvmProof.XInstr` paths and the Keccak kernel contracts (their model and
round algebra are shared with `MlDsaOptGlam44`). Open items: `checks/Axioms.lean`. -/
