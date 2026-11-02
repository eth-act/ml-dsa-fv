import MlDsa44.Spec
import MlDsaOpt44.Infra
set_option warningAsError true
/-!
# Memory map, representations, calling convention and spec-level data

Shared vocabulary for every proof about `MlDsaOpt/44/opt.hex`.

* **Memory map**: `MlDsaOpt/44/layout.txt` (generator `Layout` class in
  `scripts/gen_opt.py`). Memory is sized once at entry to `memWords = 2616`
  words (`MSTORE` at `0x146e0`, the last word of `SB`) and never grows.
* **Calling convention** (hand-written, `Gen.call`): the caller pushes the
  return address, then the arguments in order (last argument on top), and
  jumps to the entry `JUMPDEST`. The callee consumes its arguments and returns
  by `JUMP` with its results in place of the return address. So the entry
  stack is `args ++ wd ret :: tail` (`args` listed top first) and the exit
  state is at `pc = ret` (the caller's `JUMPDEST`, not yet executed) with
  stack `results ++ tail`. Gas is counted from the entry `JUMPDEST` up to and
  including the returning `JUMP`.
* **Representations** (see `docs/opt.md`):
  - polynomials four per word, 64-bit lanes (`lane x k`), lane `k` = bits
    `[64k, 64k + 64)`;
  - 4-way bit-interleaved Keccak states (`il`, `spread`), bit `b` of slot `k`
    at `4b + k`, used by `kf4`;
  - replicated single Keccak states (`rep v = v · (1 + 2^64 + 2^128 + 2^192)`),
    used by `kf1`;
  - lane complementing: lanes `complemented` are stored inverted (`cpl`).
* **Spec-level data** of a calldata string `cd` (`pkOf`, `zLane`, `hintOf`,
  `cOf`, `aOf`, `trOf`, `muOf`, …) and the implementation-shaped verification
  result `optAccepts` that `Bridge.lean` equates with `MlDsa44.accepts`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-! ## Memory map (byte offsets) -/

def KS : Nat := 0x0000
def KB : Nat := 0x0400
def RC4 : Nat := 0x0800
def RC1 : Nat := 0x0b00
def MISC : Nat := 0x0e00
/-- Number of `−1` coefficients of `c` (written by `sib`). -/
def NNEG : Nat := 0x0fa0
/-- Number of nonzero coefficients placed so far (written by `sib`). -/
def CNT : Nat := 0x0fc0
/-- Sixth-squeeze flag of the current SIMD group (`group`, `fix`). -/
def HAVE6 : Nat := 0x0fe0
def TBL : Nat := 0x1000
def CW : Nat := 0x3000
def ABUF : Nat := 0x5000
def FL : Nat := 0x7a00
def ZH : Nat := 0x8000
def BASES : Nat := 0xa000
def IDX : Nat := 0xa800
def ACC : Nat := 0xa900
def HP : Nat := 0xc900
def FIN : Nat := 0xe900
def RHO1 : Nat := 0xf600
def CB : Nat := 0xf800
def TRL : Nat := 0xfd00
def MU : Nat := 0xfe00
def BK : Nat := 0xff00
/-- `c · t1` window tables (overlay ABUF/FL/ZH after ExpandA). -/
def TT : Nat := 0x5000
/-- `2^13 S'(t) + n_neg(t)`, row-packed (overlay). -/
def SP : Nat := 0x6800
/-- One past the highest byte of the regions `MISC … BK`. Above lie `kf1`'s
third buffer `KZ` and the side buffers `SB`; the entry store at
`SB + 16384 − 32 = 0x146e0` sizes memory. -/
def TOP : Nat := 0x10220
/-- `kf1`'s third state buffer (scratch, clobbered by every `kf1` call). -/
def KZ : Nat := 0x10300
/-- Two 8 KB side buffers of the fused accumulation (`SB`, `SB + 8192`). -/
def SB : Nat := 0x10700
/-- SampleInBall's stream limit (byte offset of the lane where `c`'s second
block is squeezed on demand). -/
def LIM : Nat := 0x0f80
/-- kf4 state images (25 words each) in the dead part of `FIN` (`FIN + 256 +
800 i`): the window's paused states, and (`SC`) the states of `c` (slot 0) and
μ (slot 1) after their SIMD squeeze. -/
def SAVE0 : Nat := 0xea00
def SAVE1 : Nat := 0xed20
def SC : Nat := 0xf040

/-! ## Calldata offsets -/

/-- `|pk| + |σ|`: calldata shorter than this returns 0. -/
def HDR : Nat := 3732
/-- c̃ in calldata. -/
def CTOFF : Nat := 1312
/-- z in calldata (4 × 576 bytes). -/
def Z0 : Nat := 1344
/-- The hint bytes (ω + k = 84) in calldata. -/
def H0 : Nat := 3648

/-! ## Subroutine entry points (`MlDsaOpt/44/opt.asm` labels) -/

namespace Entry
def absorb17 : Nat := 6644
def sib : Nat := 7240
def dhint : Nat := 7740
def dz : Nat := 8219
def blk : Nat := 9025
/-- `blk` on lanes 0 … 11 only (candidates 0 … 31 of the block). -/
def blkh : Nat := 10203
/-- The rest of block 4 (lanes 12 … 20), made by `gfix` on demand. -/
def blkt : Nat := 10212
def pass3f4 : Nat := 10229
def gfix : Nat := 10501
def ginit : Nat := 10911
def kmove : Nat := 11324
def lmerge : Nat := 11451
def trabs : Nat := 11702
def cext : Nat := 12151
def spr : Nat := 12425
def mub0 : Nat := 12640
def fix : Nat := 13206
def group : Nat := 13723
def tbuild : Nat := 13954
def csum : Nat := 14762
def pack : Nat := 15459
def ntt : Nat := 16548
def intt : Nat := 17722
def kf1 : Nat := 20535
def kf4 : Nat := 22529
end Entry

/-! ## Stack budgets

Slots below the caller's tail a subroutine (and everything it calls) may use:
64 for a leaf, plus 64 per level of calls beneath it (real usage is below 25
slots per frame). -/

namespace Stack
def leaf : Nat := 64
def kf4 : Nat := leaf
def kf1 : Nat := leaf
def blk : Nat := leaf
def ntt : Nat := leaf
def intt : Nat := leaf
def pass3f4 : Nat := leaf
def tbuild : Nat := leaf
def csum : Nat := leaf
def pack : Nat := leaf
def dz : Nat := leaf
def dhint : Nat := leaf
def spr : Nat := leaf
def ginit : Nat := leaf
def absorb17 : Nat := leaf
def trabs : Nat := leaf
def cext : Nat := leaf
def kmove : Nat := leaf
def lmerge : Nat := leaf
def sib : Nat := max kf4 cext + 64
def mub0 : Nat := max trabs spr + 64
def fix : Nat := max kf4 blk + 64
def gfix : Nat := max blk fix + 64
def group : Nat := max ginit (max kf4 (max blk gfix)) + 64
end Stack

/-! ## Call contracts -/

/-- Calling the subroutine at `entry` with `args` (top of stack first) returns
to `ret` with `results` in place of the return address, turning memory `pre`
into `post`, for at most `gas`. -/
def Call (s : State) (entry : Nat) (args : List UInt256) (ret : Nat)
    (tail : List UInt256) (pre : ByteArray) (results : List UInt256)
    (post : ByteArray) (gas : Nat) : Prop :=
  Reach (callState s entry (args ++ wd ret :: tail) pre) (callState s ret (results ++ tail) post) gas

theorem call_iff {s : State} {entry : Nat} {args : List UInt256} {ret : Nat}
    {tail : List UInt256} {pre : ByteArray} {results : List UInt256} {post : ByteArray}
    {gas : Nat} :
    Call s entry args ret tail pre results post gas ↔
      Reach (callState s entry (args ++ wd ret :: tail) pre)
        (callState s ret (results ++ tail) post) gas := Iff.rfl

/-! ## Words, lanes and bit-level representations -/

/-- `2^64 − 1`. -/
def M64 : Nat := 2 ^ 64 - 1

/-- Lane `k` (bits `[64k, 64k + 64)`) of a word. -/
def lane (x k : Nat) : Nat := x / 2 ^ (64 * k) % 2 ^ 64

/-- Four 64-bit lanes as one word. -/
def pack4 (v : Nat → Nat) : Nat := v 0 + 2 ^ 64 * v 1 + 2 ^ 128 * v 2 + 2 ^ 192 * v 3

/-- `1 + 2^64 + 2^128 + 2^192`. -/
def REP : Nat := pack4 fun _ => 1

/-- A 64-bit value replicated into all four lanes. -/
def rep (v : Nat) : Nat := v * REP

/-- Bit `b` of a 64-bit value moved to bit `4b`. -/
def spread (v : Nat) : Nat := ((List.range 64).map fun b => v / 2 ^ b % 2 * 2 ^ (4 * b)).sum

/-- Inverse of `spread`: bit `4b` of a word moved to bit `b`. -/
def compress (w : Nat) : Nat := ((List.range 64).map fun b => w / 2 ^ (4 * b) % 2 * 2 ^ b).sum

/-- Four 64-bit values bit-interleaved: bit `b` of `v k` at bit `4b + k`. -/
def il (v : Nat → Nat) : Nat :=
  spread (v 0) + 2 * spread (v 1) + 4 * spread (v 2) + 8 * spread (v 3)

/-- Lanes stored inverted (lane-complementing transform, `COMPLEMENTED`). -/
def complemented : List Nat := [1, 2, 8, 12, 17, 20]

/-- Lane `x`'s stored form of the 64-bit value `v`. -/
def cpl (x v : Nat) : Nat := if x ∈ complemented then 2 ^ 64 - 1 - v else v

/-- Lane `x` of a sponge state. -/
def laneOf (S : Fips202.SpongeState) (x : Nat) : Nat := (S[x]!).toNat

/-- Iterated permutation. -/
def permN (n : Nat) (S : Fips202.SpongeState) : Fips202.SpongeState :=
  Nat.iterate EvmSemantics.Crypto.Keccak.permute n S

/-- OR of a list of words. -/
def orList (l : List Nat) : Nat := l.foldl (· ||| ·) 0

/-- Little-endian 64-bit value of the 8 bytes of `b` at `a` (zero past the end). -/
def le64 (b : ByteArray) (a : Nat) : Nat := ((List.range 8).map fun i => byteAt b (a + i) * 256 ^ i).sum

/-- 16-bit big-endian value of memory bytes `a`, `a + 1`. -/
def be16 (m : ByteArray) (a : Nat) : Nat := byteAt m a * 256 + byteAt m (a + 1)

/-- The 64-bit lanes of 256 words at `base` as a polynomial (lane `k`). -/
def lanesPoly (m : ByteArray) (base k : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t => (lane (word m (base + 32 * t)) k : Int)

/-- `m` is zero on `[lo, hi)`. -/
def ZeroOn (m : ByteArray) (lo hi : Nat) : Prop := ∀ a, lo ≤ a → a < hi → byteAt m a = 0

/-! ## Keccak states in memory -/

/-- Four states, bit-interleaved and lane-complemented, in `KS` (`kf4`). -/
def KS4 (m : ByteArray) (S : Nat → Fips202.SpongeState) : Prop :=
  ∀ x, x < 25 → word m (KS + 32 * x) = il fun k => cpl x (laneOf (S k) x)

/-- `KS4` at another base: a kf4 state image (25 words at `base`). -/
def St4At (m : ByteArray) (base : Nat) (S : Nat → Fips202.SpongeState) : Prop :=
  ∀ x, x < 25 → word m (base + 32 * x) = il fun k => cpl x (laneOf (S k) x)

/-- One state, lane-replicated and lane-complemented, in `KS` (`kf1`). -/
def KS1 (m : ByteArray) (S : Fips202.SpongeState) : Prop :=
  ∀ x, x < 25 → word m (KS + 32 * x) = rep (cpl x (laneOf S x))

/-- Sponge-state arrays of the right size. -/
def Sized4 (S : Nat → Fips202.SpongeState) : Prop := ∀ k, k < 4 → (S k).size = 25

/-- The iota constants for `kf4` (interleaved) and `kf1` (replicated). -/
def RC4Table (m : ByteArray) : Prop :=
  ∀ i, i < 24 → word m (RC4 + 32 * i) = il fun _ => (EvmSemantics.Crypto.Keccak.RC[i]!).toNat

def RC1Table (m : ByteArray) : Prop :=
  ∀ i, i < 24 → word m (RC1 + 32 * i) = rep (EvmSemantics.Crypto.Keccak.RC[i]!).toNat

/-! ## NTT zeta records at `TBL` (`scripts/opt_ntt.py`, `Kernel.records`) -/

/-- Montgomery form `ζ^{brv8 m} · 2^32 mod q`. -/
def zm (j : Nat) : Nat := (Fips204.zetas j).toNat * 2 ^ 32 % Fips204.q

/-- Record word `i < 248`: 8 pass-B records of 7 words, then 64 pass-C
records of 3 words. -/
def nttRec (i : Nat) : Nat :=
  if i < 56 then
    let b := i / 7
    let u := i % 7
    if u = 0 then zm (8 + b) else if u = 1 then zm (16 + 2 * b) else if u = 2 then zm (17 + 2 * b)
    else zm (32 + 4 * b + (u - 3))
  else
    let b := (i - 56) / 3
    let u := (i - 56) % 3
    if u = 0 then zm (64 + b) else if u = 1 then zm (128 + 2 * b) else zm (129 + 2 * b)

def TblAt (m : ByteArray) : Prop := ∀ i, i < 248 → word m (TBL + 32 * i) = nttRec i

/-- `SP`'s constant offset: `csum` stores `spOff − (2^13 S' + n_neg)` per
lane, which carries UseHint's rounding term `γ2 − 1` (v4). -/
def spOff : Nat := 128 * Fips204.q + Fips204.gamma2 - 1

/-! ## Spec-level data of a calldata string -/

def pkOf (cd : ByteArray) : ByteArray := cd.extract 0 1312
def sigOf (cd : ByteArray) : ByteArray := cd.extract 1312 3732
def msgOf (cd : ByteArray) : ByteArray := cd.extract 3732 cd.size
def rhoOf (cd : ByteArray) : ByteArray := cd.extract 0 32
def ctOf (cd : ByteArray) : ByteArray := cd.extract 1312 1344
def mlenOf (cd : ByteArray) : Nat := cd.size - 3732

/-- The 18-bit packed field `t` of `z_k` (`raw`); `z_k[t] = γ1 − raw`. -/
def rawZ (cd : ByteArray) (k t : Nat) : Nat :=
  Fips204.bitsToInteger (cd.extract (Z0 + 576 * k) (Z0 + 576 * (k + 1))) (18 * t) 18

/-- The lane `dz` stores for `z_k[t]`: `γ1 + 9q − raw ≡ z_k[t] (mod q)` (v4: the
forward NTT's bias `8q` is added by the decoder). -/
def zLane (cd : ByteArray) (k t : Nat) : Nat := 2 ^ 17 + 9 * Fips204.q - rawZ cd k t

/-- Lower and upper bound of the forward NTT's input lanes (`zLane`: `γ1 + 9q − raw`,
`raw < 2^18`). -/
def zLo : Nat := 2 ^ 17 + 9 * Fips204.q - (2 ^ 18 - 1)
def zHi : Nat := 2 ^ 17 + 9 * Fips204.q

/-- The 10-bit field `i` of `t1_r`. -/
def t1v (cd : ByteArray) (r i : Nat) : Nat :=
  Fips204.bitsToInteger (cd.extract (32 + 320 * r) (32 + 320 * (r + 1))) (10 * i) 10

def zPolys (cd : ByteArray) : Array Fips204.Poly := (Fips204.sigDecode (sigOf cd)).2.1
def hintOf (cd : ByteArray) : Option (Array Fips204.Poly) :=
  Fips204.hintBitUnpack (cd.extract H0 HDR)
def cOf (cd : ByteArray) : Option Fips204.Poly := Fips204.sampleInBall (ctOf cd)
def aOf (cd : ByteArray) (r s : Nat) : Option Fips204.Poly :=
  Fips204.rejNTTPoly (rhoOf cd ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])
def t1Of (cd : ByteArray) (r : Nat) : Fips204.Poly := (Fips204.pkDecode (pkOf cd)).2[r]!
def trOf (cd : ByteArray) : ByteArray := Fips204.H (pkOf cd) 64
def muOf (cd : ByteArray) : ByteArray :=
  Fips204.H (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) 64
/-- The SampleInBall stream `H(c̃)` (272 bytes, two SHAKE256 blocks). -/
def cStream (cd : ByteArray) : ByteArray := Fips204.H (ctOf cd) Fips204.sampleInBallLimit

/-! ## Validity flags and the implementation-shaped verification result -/

def okZ (cd : ByteArray) : Bool := Fips204.normBelow (zPolys cd) (Fips204.gamma1 - Fips204.beta)
def okH (cd : ByteArray) : Bool := (hintOf cd).isSome
def okC (cd : ByteArray) : Bool := (cOf cd).isSome
def okA (cd : ByteArray) : Bool :=
  (List.range 4).all fun r => (List.range 4).all fun s => (aOf cd r s).isSome

def hintD (cd : ByteArray) : Array Fips204.Poly :=
  (hintOf cd).getD (Array.replicate 4 Fips204.zeroPoly)
def cD (cd : ByteArray) : Fips204.Poly := (cOf cd).getD Fips204.zeroPoly
def aD (cd : ByteArray) (r s : Nat) : Fips204.Poly := (aOf cd r s).getD Fips204.zeroPoly

/-- `NTT(z_s mod q)`. -/
def zHat (cd : ByteArray) (s : Nat) : Fips204.Poly :=
  Fips204.ntt ((zPolys cd)[s]!.map (· % (Fips204.q : Int)))

/-- Row `r` of `Â ∘ ẑ` (NTT domain, reduced). -/
def azRow (cd : ByteArray) (r : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t =>
    ((List.range 4).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum % (Fips204.q : Int)

/-- Coefficient `t` of the negacyclic product `c · f` in `Z[X]/(X^256 + 1)`. -/
def negacyclic (c f : Fips204.Poly) (t : Nat) : Int :=
  ((List.range 256).map fun p =>
    if p ≤ t then c[p]! * f[t - p]! else -(c[p]! * f[t + 256 - p]!)).sum

/-- Row `r` of `w' = NTT⁻¹(Â ẑ) − c · t1 · 2^d`, computed in the normal domain. -/
def wRow (cd : ByteArray) (r : Nat) : Fips204.Poly :=
  (Array.range 256).map fun t =>
    ((Fips204.nttInv (azRow cd r))[t]! - 2 ^ 13 * negacyclic (cD cd) (t1Of cd r) t) %
      (Fips204.q : Int)

def w1Of (cd : ByteArray) : Array Fips204.Poly :=
  (Array.range 4).map fun r => (Array.range 256).map fun t =>
    Fips204.useHint (hintD cd)[r]![t]! (wRow cd r)[t]!

/-- The final hash input `μ ‖ w1Encode(w1)` (832 bytes). -/
def finBytes (cd : ByteArray) : ByteArray := muOf cd ++ Fips204.w1Encode (w1Of cd)

/-- The verification result in the bytecode's data flow: flags accumulated in
the order the code ANDs them, then the commitment hash comparison. -/
def optAccepts (cd : ByteArray) : Bool :=
  (((okZ cd && okH cd) && okA cd) && okC cd) && (ctOf cd == Fips204.H (finBytes cd) 32)

end MlDsaOpt44.Proofs
