import MlDsa44.Spec
import MlDsa44.Proofs.Artifact
import EvmProof
set_option warningAsError true
/-!
# Memory map, representation predicates and subroutine contracts

Shared vocabulary for every proof about the frozen reference bytecode.

* The memory map mirrors `scripts/gen_reference.py` (`REGIONS`).
* `Entry.*` are the entry `JUMPDEST`s of the compiled Yul functions
  (`lake exe mldsa44tool layout MlDsa44/Reference/reference.yul`).
* `Call` is the contract form for one subroutine call. The classic backend's
  caller pushes the return address, then one zero slot per return value,
  then the arguments (first argument on top), and jumps to the entry; the
  callee returns with the results on top of the caller's stack.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

/-! ## Memory map -/

def ST : Nat := 0x0000
def BT : Nat := 0x0320
def CT : Nat := 0x0640
def RC : Nat := 0x06E0
def ZETA : Nat := 0x09E0
def POLY : Nat := 0x2000
def ZH : Nat := 0x29E0
def CH : Nat := 0xA9E0
def AP : Nat := 0xC9E0
def ACC : Nat := 0xE9E0
def TP : Nat := 0x109E0
def HB : Nat := 0x129E0
def XOF : Nat := 0x12DE0
def SEEDA : Nat := 0x13200
def SEEDC : Nat := 0x13240
def PADB : Nat := 0x13280
def W1 : Nat := 0x13340
def PK : Nat := 0x13680
def MSGIN : Nat := 0x13BC0

/-- Memory words needed by every fixed region, including squeeze overhangs. -/
def fixedWords : Nat := (MSGIN + 288) / 32

/-! ## Subroutine entry points -/

namespace Entry
def keccakF : Nat := 4
def bswap64 : Nat := 2490
def loadLE64 : Nat := 2572
def storeLE64 : Nat := 2597
def xorBlock : Nat := 2621
def shake : Nat := 2680
def brv8 : Nat := 2956
def initZetas : Nat := 3003
def zeroPoly : Nat := 3067
def ntt : Nat := 3107
def nttInv : Nat := 3255
def unpack : Nat := 3456
def rejSample : Nat := 3523
def sampleInBall : Nat := 3637
def decodeHint : Nat := 3786
def decodeZ : Nat := 4000
def useHint : Nat := 4139
def encodeRow : Nat := 4260
def computeRow : Nat := 4415
end Entry

/-! ## Memory reading -/

/-- Byte `a` of memory, zero past the end (EVM memory semantics). -/
def byteAt (m : ByteArray) (a : Nat) : Nat := if h : a < m.size then m[a].toNat else 0

/-- The 32-byte big-endian word at `a`. -/
def word (m : ByteArray) (a : Nat) : Nat := (MachineState.readWord m a).toNat

/-- `m'` agrees with `m` outside the half-open byte ranges `rs`. -/
def FrameExcept (m m' : ByteArray) (rs : List (Nat × Nat)) : Prop :=
  ∀ a, (∀ r ∈ rs, a < r.1 ∨ r.2 ≤ a) → byteAt m' a = byteAt m a

/-- The bytes `b` are stored at `base`. -/
def BytesAt (m : ByteArray) (base : Nat) (b : ByteArray) : Prop :=
  ∀ i, i < b.size → byteAt m (base + i) = b[i]!.toNat

/-- Keccak lanes, one per word at `base`. -/
def LanesAt (m : ByteArray) (base : Nat) (A : Array UInt64) : Prop :=
  A.size = 25 ∧ ∀ i, i < 25 → word m (base + 32 * i) = (A[i]!).toNat

/-- A polynomial with coefficients in `[0, q)`, one per word at `base`. -/
def PolyAt (m : ByteArray) (base : Nat) (p : Fips204.Poly) : Prop :=
  p.size = 256 ∧ ∀ i, i < 256 → (word m (base + 32 * i) : Int) = p[i]!

/-- Coefficients of `p` lie in `[0, q)`. -/
def Reduced (p : Fips204.Poly) : Prop :=
  ∀ i, i < 256 → (0 : Int) ≤ p[i]! ∧ p[i]! < (Fips204.q : Int)

/-- The Keccak round constants at `RC`. -/
def RCTable (m : ByteArray) : Prop :=
  ∀ i, i < 24 → word m (RC + 32 * i) = (Crypto.Keccak.RC[i]!).toNat

/-- `zetas[k]` at `ZETA + 32 k`. -/
def ZetaTable (m : ByteArray) : Prop :=
  ∀ k, k < 256 → (word m (ZETA + 32 * k) : Int) = Fips204.zetas k

/-- Hint bits, one byte per coefficient, at `HB + 256 i + j`. -/
def HintAt (m : ByteArray) (h : Array Fips204.Poly) : Prop :=
  ∀ i, i < 4 → ∀ j, j < 256 → (byteAt m (HB + 256 * i + j) : Int) = h[i]![j]!

/-! ## Call contracts -/

/-- `s` at program counter `pc` with the given stack and memory. -/
def callState (s : State) (pc : Nat) (stack : List UInt256) (memory : ByteArray) : State :=
  { s with pc := UInt256.ofNat pc, stack, memory }

/-- Invariant facts about every intermediate state of a run of the frozen
bytecode after memory has been sized. -/
structure Ctx (s : State) : Prop where
  code : s.executionEnv.code = referenceBytecode
  fork : s.fork = .Osaka
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false
  running : s.halt = .Running
  sized : fixedWords ≤ s.activeWords.toNat

/-- A caller-supplied return address and stack tail that a call can use. -/
structure RetOK (ret : Nat) (tail : List UInt256) : Prop where
  jumpdest : Decode.isValidJumpDest referenceBytecode ret = true
  small : ret < 2 ^ 16
  depth : tail.length ≤ 960

/-- A Boolean returned in a stack word. -/
def flag (b : Bool) : UInt256 := UInt256.ofNat (if b then 1 else 0)

/-- The word `UInt256.ofNat n`, shorthand for contract arguments. -/
abbrev wd (n : Nat) : UInt256 := UInt256.ofNat n

/-- Calling the subroutine at `entry` with `args` returns to `ret` with
`results` above `tail`, turning memory `pre` into `post`, for at most `gas`.
On entry the stack holds the arguments, one zero slot per result, the return
address, then `tail`. -/
def Call (s : State) (entry : Nat) (args : List UInt256) (ret : Nat)
    (tail : List UInt256) (pre : ByteArray) (results : List UInt256)
    (post : ByteArray) (gas : Nat) : Prop :=
  ∃ g : EvmProof.GasSteps
      (callState s entry
        (args ++ List.replicate results.length (UInt256.ofNat 0) ++ UInt256.ofNat ret :: tail)
        pre)
      (callState s ret (results ++ tail) post),
    g.cost ≤ gas

end MlDsa44.Proofs
