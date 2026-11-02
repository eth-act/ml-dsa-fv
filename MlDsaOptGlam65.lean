import MlDsaOptGlam65.Infra
import MlDsaOptGlam65.Fn.Kf4.Main
import MlDsaOptGlam65.Fn.Kf1.Main
import MlDsaOptGlam65.Main
import MlDsaOptGlam65.Fn.Ball
import MlDsaOptGlam65.Fn.Blk
import MlDsaOptGlam65.Fn.Csum
import MlDsaOptGlam65.Fn.Decode
import MlDsaOptGlam65.Fn.Fix
import MlDsaOptGlam65.Fn.Group
import MlDsaOptGlam65.Fn.Hint
import MlDsaOptGlam65.Fn.Keccak
import MlDsaOptGlam65.Fn.Ntt
import MlDsaOptGlam65.Fn.Pack65
import MlDsaOptGlam65.Fn.Sponge
import MlDsaOptGlam65.Fn.TBuild
/-! Proofs about the Glamsterdam variant of the gas-optimised ML-DSA-65
bytecode (`MlDsaOpt/65/glam/opt.hex`, EIP-8024 and EIP-7954): the four final
theorems over `Fork.Amsterdam` (`MlDsa65.Amsterdam`), the artifact infrastructure
on `EvmProof.XInstr` paths and the Keccak kernel contracts (their model and
round algebra are shared with `MlDsaOptGlam44`). Open items: `checks/Axioms.lean`. -/
