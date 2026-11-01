import MlDsa87.Spec
import MlDsaOpt44.Layout
import MlDsaOpt87.Infra
set_option warningAsError true
/-!
# Memory map, entry points, stack budgets and spec-level data (ML-DSA-87)

Vocabulary for every proof about `MlDsaOpt/87/opt.hex`
(`MlDsaOpt/87/layout.txt`, generator `scripts/gen_opt.py 87`). Memory is sized
once at entry to `memWords = 2897` words (`MSTORE` at `0x16a00`) and never
grows. The calling convention, the representations and the contract form are
those of `MlDsaOpt44/Layout.lean`.

**Shared vocabulary.** Everything that does not depend on the parameter set
(the representations `lane`, `pack4`, `rep`, `spread`, `compress`, `il`, `cpl`,
`KS4`, `KS1`, the iota and zeta tables, `Call`, and the memory-map constants
whose value is the same in all three artifacts: `KS … FL`, `ZH`, `TT`) is the
`MlDsaOpt44.Proofs` constant, re-exported here, so the ML-DSA-44 lemmas about
it apply verbatim. Constants whose value differs (`BASES` and above, `SP`,
`TOP`, the calldata offsets, the entry pcs) are redefined below; inside
`MlDsaOpt87.Proofs` they shadow the ML-DSA-44 ones.

**Spec-level data** is stated against the parametric `MlDsa.Fips204` at
`Params.mldsa87` (the parameter-free functions `ntt`, `nttInv`, `rejNTTPoly`, `H`, …
equal their `MlDsa44.Fips204` twins by `MlDsa/Bridge44.lean`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

export MlDsaOpt44.Proofs (KS KB RC4 RC1 MISC NNEG CNT HAVE6 TBL CW ABUF FL ZH TT
  Call call_iff M64 lane pack4 REP rep spread compress il complemented cpl laneOf permN orList
  le64 be16 lanesPoly ZeroOn KS4 KS1 Sized4 RC4Table RC1Table zm nttRec TblAt negacyclic)

/-- The parameter set. -/
abbrev P : Params := .mldsa87

/-! ## Memory map (byte offsets) that differs from ML-DSA-44 -/

/-- `ẑ`: two words of four lanes per coefficient (polynomials 0–3, then 4–6). -/
def ZH2 : Nat := 0xa000
def BASES : Nat := 0xc000
def IDX : Nat := 0xc800
/-- `A·ẑ` accumulators: row group 0 (rows 0–3) at `ACC`, row group 1 (rows 4–7) at `ACC + 0x2000`. -/
def ACC : Nat := 0xc900
def HP : Nat := 0x10900
/-- μ ‖ w1Encode lanes (replicated), 8 + 128 words. -/
def FIN : Nat := 0x14900
def RHO1 : Nat := 0x15a00
def CB : Nat := 0x15c00
def TRL : Nat := 0x16100
def MU : Nat := 0x16200
def BK : Nat := 0x16300
/-- `2^13 S'(t) + n_neg(t)`, row-packed, one 8 KB table per row group (overlay of ZH). -/
def SP : Nat := 0x8000
/-- One past the highest byte of the regions the main flow reads or keeps
(`MISC … BK`). Only `kf1`'s third buffer `KZ` lies above; the entry store at
`KZ + 800 − 32 = 0x16a00` sizes memory. -/
def TOP : Nat := 0x16620
/-- `kf1`'s third state buffer (scratch, clobbered by every `kf1` call). -/
def KZ : Nat := 0x16700

/-! ## Calldata offsets -/

/-- `|pk| + |σ|`: calldata shorter than this returns 0. -/
def HDR : Nat := 7219
/-- c̃ (64 bytes) in calldata. -/
def CTOFF : Nat := 2592
/-- z in calldata (7 × 640 bytes). -/
def Z0 : Nat := 2656
/-- The hint bytes (ω + k = 83) in calldata. -/
def H0 : Nat := 7136

/-! ## Subroutine entry points (`MlDsaOpt/87/layout.txt`) -/

namespace Entry
def absorb17 : Nat := 7488
def sib : Nat := 8084
def dhint : Nat := 8967
def dz : Nat := 9890
def blk : Nat := 10772
def pass3 : Nat := 11947
def pass3m : Nat := 12229
def pass3k14 : Nat := 12528
def gfix : Nat := 12615
def ginit : Nat := 12945
def trabs : Nat := 13300
def cext : Nat := 13921
def spr : Nat := 14195
def fix : Nat := 14410
def group : Nat := 15099
def tbuild : Nat := 15364
def csum : Nat := 16172
def usehint : Nat := 17065
def pack : Nat := 17336
def ntt : Nat := 17719
def intt : Nat := 18986
def kf1 : Nat := 20467
def kf4 : Nat := 22461
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
def pass3m : Nat := leaf
def pass3k14 : Nat := leaf
def tbuild : Nat := leaf
def csum : Nat := leaf
def usehint : Nat := leaf
def pack : Nat := leaf
def dz : Nat := leaf
def dhint : Nat := leaf
/-- `sib` squeezes `H(c̃)` with `kf1` (ML-DSA-87 has no free SIMD slot for it). -/
def sib : Nat := kf1 + 64
def spr : Nat := leaf
def ginit : Nat := leaf
def absorb17 : Nat := leaf
def trabs : Nat := leaf
def cext : Nat := leaf
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
  (List.range 8).all fun r => (List.range 7).all fun s => (aOf cd r s).isSome

def hintD (cd : ByteArray) : Array Fips204.Poly :=
  (hintOf cd).getD (Array.replicate 8 Fips204.zeroPoly)
def cD (cd : ByteArray) : Fips204.Poly := (cOf cd).getD Fips204.zeroPoly
def aD (cd : ByteArray) (r s : Nat) : Fips204.Poly := (aOf cd r s).getD Fips204.zeroPoly

/-- `NTT(z_s mod q)`. -/
def zHat (cd : ByteArray) (s : Nat) : Fips204.Poly :=
  Fips204.ntt ((zPolys cd)[s]!.map (· % (Fips204.q : Int)))

/-- Row `r` of `Â ∘ ẑ` (NTT domain, reduced). -/
def azRow (cd : ByteArray) (r : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t =>
    ((List.range 7).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum % (Fips204.q : Int)

/-- Row `r` of `w' = NTT⁻¹(Â ẑ) − c · t1 · 2^d`, computed in the normal domain. -/
def wRow (cd : ByteArray) (r : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t =>
    ((Fips204.nttInv (azRow cd r))[t]! - 2 ^ 13 * negacyclic (cD cd) (t1Of cd r) t) %
      (Fips204.q : Int)

def w1Of (cd : ByteArray) : Array Fips204.Poly :=
  (Array.range 8).map fun r => (Array.range 256).map fun t =>
    Fips204.useHint P (hintD cd)[r]![t]! (wRow cd r)[t]!

/-- The final hash input `μ ‖ w1Encode(w1)` (64 + 1024 bytes). -/
def finBytes (cd : ByteArray) : ByteArray := muOf cd ++ Fips204.w1Encode P (w1Of cd)

/-- The verification result in the bytecode's data flow: flags accumulated in
the order the code ANDs them (`c` is sampled before `A`), then the commitment
hash comparison (64 bytes). -/
def optAccepts (cd : ByteArray) : Bool :=
  (((okZ cd && okH cd) && okC cd) && okA cd) && (ctOf cd == Fips204.H (finBytes cd) 64)

end MlDsaOpt87.Proofs
