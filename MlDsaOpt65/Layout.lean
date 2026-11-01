import MlDsa65.Spec
import MlDsaOpt44.Layout
import MlDsaOpt65.Infra
set_option warningAsError true
/-!
# Memory map, entry points, stack budgets and spec-level data (ML-DSA-65)

Vocabulary for every proof about `MlDsaOpt/65/opt.hex`
(`MlDsaOpt/65/layout.txt`, generator `scripts/gen_opt.py 65`). Memory is sized
once at entry to `memWords = 2833` words (`MSTORE` at `0x16200`) and never
grows. The calling convention, the representations and the contract form are
those of `MlDsaOpt44/Layout.lean`.

**Shared vocabulary.** Everything that does not depend on the parameter set
(the representations `lane`, `pack4`, `rep`, `spread`, `compress`, `il`, `cpl`,
`KS4`, `KS1`, the iota and zeta tables, `Call`, and the memory-map constants
whose value is the same in all three artifacts: `KS … FL`, `ZH`, `TT`) is the
`MlDsaOpt44.Proofs` constant, re-exported here, so the ML-DSA-44 lemmas about
it apply verbatim. Constants whose value differs (`BASES` and above, `SP`,
`TOP`, the calldata offsets, the entry pcs) are redefined below; inside
`MlDsaOpt65.Proofs` they shadow the ML-DSA-44 ones.

**Spec-level data** is stated against the parametric `MlDsa.Fips204` at
`Params.mldsa65` (the parameter-free functions `ntt`, `nttInv`, `rejNTTPoly`, `H`, …
equal their `MlDsa44.Fips204` twins by `MlDsa/Bridge44.lean`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

export MlDsaOpt44.Proofs (KS KB RC4 RC1 MISC NNEG CNT HAVE6 TBL CW ABUF FL ZH TT
  Call call_iff M64 lane pack4 REP rep spread compress il complemented cpl laneOf permN orList
  le64 be16 lanesPoly ZeroOn KS4 KS1 Sized4 RC4Table RC1Table zm nttRec TblAt negacyclic)

/-- The parameter set. -/
abbrev P : Params := .mldsa65

/-! ## Memory map (byte offsets) that differs from ML-DSA-44 -/

/-- `ẑ`: two words of four lanes per coefficient (polynomials 0–3, then 4). -/
def ZH2 : Nat := 0xa000
def BASES : Nat := 0xc000
def IDX : Nat := 0xc800
/-- `A·ẑ` accumulators: row group 0 (rows 0–3) at `ACC`, row group 1 (rows 4, 5) at `ACC + 0x2000`. -/
def ACC : Nat := 0xc900
def HP : Nat := 0x10900
/-- μ ‖ w1Encode lanes (replicated), 8 + 96 words. -/
def FIN : Nat := 0x14900
def RHO1 : Nat := 0x15600
def CB : Nat := 0x15800
def TRL : Nat := 0x15d00
def MU : Nat := 0x15e00
def BK : Nat := 0x15f00
/-- `2^13 S'(t) + n_neg(t)`, row-packed, one 8 KB table per row group (overlay of ZH). -/
def SP : Nat := 0x8000
/-- One past the highest byte; the entry store at `TOP − 32` sizes memory. -/
def TOP : Nat := 0x16220

/-! ## Calldata offsets -/

/-- `|pk| + |σ|`: calldata shorter than this returns 0. -/
def HDR : Nat := 5261
/-- c̃ (48 bytes) in calldata. -/
def CTOFF : Nat := 1952
/-- z in calldata (5 × 640 bytes). -/
def Z0 : Nat := 2000
/-- The hint bytes (ω + k = 61) in calldata. -/
def H0 : Nat := 5200

/-! ## Subroutine entry points (`MlDsaOpt/65/layout.txt`) -/

namespace Entry
def absorb17 : Nat := 7461
def sib : Nat := 8057
def dhint : Nat := 8288
def dz : Nat := 8975
def blk : Nat := 9857
def pass3 : Nat := 11032
def gfix : Nat := 11314
def ginit : Nat := 11644
def trabs : Nat := 12084
def cext : Nat := 12705
def spr : Nat := 12979
def mu0 : Nat := 13194
def fix : Nat := 13567
def group : Nat := 14256
def tbuild : Nat := 14521
def csum : Nat := 15329
def usehint : Nat := 16134
def pack : Nat := 16473
def ntt : Nat := 16856
def intt : Nat := 18123
def kf1 : Nat := 19604
def kf4 : Nat := 20991
end Entry

/-! ## Stack budgets (as for ML-DSA-44) -/

namespace Stack
def leaf : Nat := 64
def kf4 : Nat := leaf
def kf1 : Nat := leaf
def blk : Nat := leaf
def ntt : Nat := leaf
def intt : Nat := leaf
def pass3 : Nat := leaf
def tbuild : Nat := leaf
def csum : Nat := leaf
def usehint : Nat := leaf
def pack : Nat := leaf
def dz : Nat := leaf
def dhint : Nat := leaf
def sib : Nat := leaf
def spr : Nat := leaf
def ginit : Nat := leaf
def absorb17 : Nat := leaf
def trabs : Nat := leaf
def cext : Nat := leaf
def mu0 : Nat := max trabs spr + 64
def fix : Nat := max kf4 blk + 64
def gfix : Nat := fix + 64
def group : Nat := max ginit (max kf4 (max blk (max gfix pass3))) + 64
end Stack

/-! ## Spec-level data of a calldata string -/

def pkOf (cd : ByteArray) : ByteArray := cd.extract 0 CTOFF
def sigOf (cd : ByteArray) : ByteArray := cd.extract CTOFF HDR
def msgOf (cd : ByteArray) : ByteArray := cd.extract HDR cd.size
def rhoOf (cd : ByteArray) : ByteArray := cd.extract 0 32
def ctOf (cd : ByteArray) : ByteArray := cd.extract CTOFF Z0
def mlenOf (cd : ByteArray) : Nat := cd.size - HDR

/-- The 20-bit packed field `t` of `z_k` (`raw`); `z_k[t] = γ1 − raw`. -/
def rawZ (cd : ByteArray) (k t : Nat) : Nat :=
  Fips204.bitsToInteger (cd.extract (Z0 + 640 * k) (Z0 + 640 * (k + 1))) (20 * t) 20

/-- The lane `dz` stores for `z_k[t]`: `γ1 + q − raw ≡ z_k[t] (mod q)`. -/
def zLane (cd : ByteArray) (k t : Nat) : Nat := 2 ^ 19 + Fips204.q - rawZ cd k t

/-- The 10-bit field `i` of `t1_r`. -/
def t1v (cd : ByteArray) (r i : Nat) : Nat :=
  Fips204.bitsToInteger (cd.extract (32 + 320 * r) (32 + 320 * (r + 1))) (10 * i) 10

def zPolys (cd : ByteArray) : Array Fips204.Poly := (Fips204.sigDecode P (sigOf cd)).2.1
def hintOf (cd : ByteArray) : Option (Array Fips204.Poly) :=
  Fips204.hintBitUnpack P (cd.extract H0 HDR)
def cOf (cd : ByteArray) : Option Fips204.Poly := Fips204.sampleInBall P (ctOf cd)
def aOf (cd : ByteArray) (r s : Nat) : Option Fips204.Poly :=
  Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])
def t1Of (cd : ByteArray) (r : Nat) : Fips204.Poly := (Fips204.pkDecode P (pkOf cd)).2[r]!
def trOf (cd : ByteArray) : ByteArray := Fips204.H (pkOf cd) 64
def muOf (cd : ByteArray) : ByteArray :=
  Fips204.H (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) 64
/-- The SampleInBall stream `H(c̃)` (272 bytes, two SHAKE256 blocks). -/
def cStream (cd : ByteArray) : ByteArray := Fips204.H (ctOf cd) Fips204.sampleInBallLimit

/-! ## Validity flags and the implementation-shaped verification result -/

def okZ (cd : ByteArray) : Bool := Fips204.normBelow (zPolys cd) (P.gamma1 - P.beta)
def okH (cd : ByteArray) : Bool := (hintOf cd).isSome
def okC (cd : ByteArray) : Bool := (cOf cd).isSome
def okA (cd : ByteArray) : Bool :=
  (List.range 6).all fun r => (List.range 5).all fun s => (aOf cd r s).isSome

def hintD (cd : ByteArray) : Array Fips204.Poly :=
  (hintOf cd).getD (Array.replicate 6 Fips204.zeroPoly)
def cD (cd : ByteArray) : Fips204.Poly := (cOf cd).getD Fips204.zeroPoly
def aD (cd : ByteArray) (r s : Nat) : Fips204.Poly := (aOf cd r s).getD Fips204.zeroPoly

/-- `NTT(z_s mod q)`. -/
def zHat (cd : ByteArray) (s : Nat) : Fips204.Poly :=
  Fips204.ntt ((zPolys cd)[s]!.map (· % (Fips204.q : Int)))

/-- Row `r` of `Â ∘ ẑ` (NTT domain, reduced). -/
def azRow (cd : ByteArray) (r : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t =>
    ((List.range 5).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum % (Fips204.q : Int)

/-- Row `r` of `w' = NTT⁻¹(Â ẑ) − c · t1 · 2^d`, computed in the normal domain. -/
def wRow (cd : ByteArray) (r : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t =>
    ((Fips204.nttInv (azRow cd r))[t]! - 2 ^ 13 * negacyclic (cD cd) (t1Of cd r) t) %
      (Fips204.q : Int)

def w1Of (cd : ByteArray) : Array Fips204.Poly :=
  (Array.range 6).map fun r => (Array.range 256).map fun t =>
    Fips204.useHint P (hintD cd)[r]![t]! (wRow cd r)[t]!

/-- The final hash input `μ ‖ w1Encode(w1)` (64 + 768 bytes). -/
def finBytes (cd : ByteArray) : ByteArray := muOf cd ++ Fips204.w1Encode P (w1Of cd)

/-- The verification result in the bytecode's data flow: flags accumulated in
the order the code ANDs them, then the commitment hash comparison (48 bytes). -/
def optAccepts (cd : ByteArray) : Bool :=
  (((okZ cd && okH cd) && okA cd) && okC cd) && (ctOf cd == Fips204.H (finBytes cd) 48)

end MlDsaOpt65.Proofs
