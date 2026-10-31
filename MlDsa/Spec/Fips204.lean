import MlDsa44.Spec.Fips202
import MlDsa.Spec.Params
set_option warningAsError true
/-!
# FIPS 204 ML-DSA verification, parametric in the parameter set

A literal transcription of the FIPS 204 algorithms reachable from
`ML-DSA.Verify` (Algorithm 3), for any `P : Params` (Table 1). Algorithm
numbers refer to FIPS 204 (August 2024). Polynomials are `Array Int` of
length 256; elements of `ℤ_q` are integers in `[0, q)` obtained with `% q`.

This is the ML-DSA-44 transcription `MlDsa44.Fips204` with the per-set
constants `k, ℓ, η, τ, λ, γ₁, γ₂, ω` taken from `P`; definitions that do not
mention them are unchanged. `MlDsa.Bridge44` proves that `verify Params.mldsa44`
is `MlDsa44.Fips204.verify`. SHAKE is `MlDsa44.Fips202`.

The only deviation the standard permits and this transcription uses is the
bounded XOF output of Appendix C (Table 3). Table 3 gives one limit for all
three parameter sets (the SampleInBall figure is computed for the largest
`τ = 60`): RejNTTPoly reads at most `rejNTTPolyLimit = 1008 ≥ 894` bytes of G
and SampleInBall at most `sampleInBallLimit = 272 ≥ 221` bytes of H.
Exceeding a limit returns `none`, which makes verification return `false`.
Both limits are whole XOF blocks (6 × 168 and 2 × 136 bytes).
-/

namespace MlDsa.Fips204

/-! ## Parameters shared by all sets (FIPS 204 Table 1) -/

def q : Nat := 8380417
def zeta : Nat := 1753
def d : Nat := 13

/-- `bitlen b` for `b ≥ 1`. -/
def bitlen (b : Nat) : Nat := Nat.log2 b + 1

/-- Public-key and signature byte lengths (Algorithms 22, 26; Table 2). -/
def pkLen (P : Params) : Nat := 32 + 32 * P.k * (bitlen (q - 1) - d)
def sigLen (P : Params) : Nat :=
  P.lambda / 4 + P.l * 32 * (1 + bitlen (P.gamma1 - 1)) + P.omega + P.k

/-- Appendix C limits, rounded up to whole XOF blocks. -/
def rejNTTPolyLimit : Nat := 1008
def sampleInBallLimit : Nat := 272

abbrev Poly := Array Int

def zeroPoly : Poly := Array.replicate 256 0

/-! ## §3.7 Hash functions -/

def H (str : ByteArray) (len : Nat) : ByteArray := MlDsa44.Fips202.shake256 str len
def G (str : ByteArray) (len : Nat) : ByteArray := MlDsa44.Fips202.shake128 str len

/-! ## §7.1 Conversion between data types -/

/-- `BytesToBits(v)[i]` (Algorithm 13): little-endian bit order. -/
def bit (v : ByteArray) (i : Nat) : Nat := v[i / 8]!.toNat / 2 ^ (i % 8) % 2

/-- `BitsToInteger((z[start], …, z[start + c − 1]), c)` (Algorithm 10). -/
def bitsToInteger (v : ByteArray) (start c : Nat) : Nat :=
  ((List.range c).map fun j => bit v (start + j) * 2 ^ j).sum

/-- Algorithm 14. -/
def coeffFromThreeBytes (b0 b1 b2 : Nat) : Option Int :=
  let b2' := if b2 > 127 then b2 - 128 else b2
  let z := 2 ^ 16 * b2' + 2 ^ 8 * b1 + b0
  if z < q then some z else none

/-- Algorithm 16, `SimpleBitPack(w, b)` with BitsToBytes (Algorithm 12). -/
def simpleBitPack (w : Poly) (b : Nat) : ByteArray :=
  let c := bitlen b
  let z : Nat → Nat := fun i => w[i / c]!.toNat / 2 ^ (i % c) % 2
  ByteArray.mk <| (Array.range (32 * c)).map fun j =>
    UInt8.ofNat ((List.range 8).map (fun t => z (8 * j + t) * 2 ^ t)).sum

/-- Algorithm 18, `SimpleBitUnpack(v, b)`. -/
def simpleBitUnpack (v : ByteArray) (b : Nat) : Poly :=
  let c := bitlen b
  (Array.range 256).map fun i => (bitsToInteger v (i * c) c : Int)

/-- Algorithm 19, `BitUnpack(v, a, b)`. -/
def bitUnpack (v : ByteArray) (a b : Nat) : Poly :=
  let c := bitlen (a + b)
  (Array.range 256).map fun i => (b : Int) - bitsToInteger v (i * c) c

/-- Algorithm 21, `HintBitUnpack(y)`. -/
def hintBitUnpack (P : Params) (y : ByteArray) : Option (Array Poly) := Id.run do
  let mut h : Array Poly := Array.replicate P.k zeroPoly
  let mut index := 0
  for i in [0:P.k] do
    let bound := y[P.omega + i]!.toNat
    if bound < index || bound > P.omega then return none
    let first := index
    -- `while Index < y[ω + i]`: Index runs from `first` to `bound`.
    for idx in [first:bound] do
      if idx > first then
        if y[idx - 1]!.toNat ≥ y[idx]!.toNat then return none
      h := h.set! i (h[i]!.set! y[idx]!.toNat 1)
    index := bound
  for i in [index:P.omega] do
    if y[i]!.toNat ≠ 0 then return none
  return some h

/-! ## §7.2 Encodings -/

/-- Algorithm 23, `pkDecode(pk)`. -/
def pkDecode (P : Params) (pk : ByteArray) : ByteArray × Array Poly :=
  let w := bitlen (q - 1) - d
  (pk.extract 0 32,
    (Array.range P.k).map fun i =>
      simpleBitUnpack (pk.extract (32 + 32 * w * i) (32 + 32 * w * (i + 1)))
        (2 ^ w - 1))

/-- Algorithm 27, `sigDecode(σ)`. -/
def sigDecode (P : Params) (sig : ByteArray) :
    ByteArray × Array Poly × Option (Array Poly) :=
  let cLen := P.lambda / 4
  let zLen := 32 * (1 + bitlen (P.gamma1 - 1))
  (sig.extract 0 cLen,
    (Array.range P.l).map (fun i =>
      bitUnpack (sig.extract (cLen + zLen * i) (cLen + zLen * (i + 1)))
        (P.gamma1 - 1) P.gamma1),
    hintBitUnpack P
      (sig.extract (cLen + zLen * P.l) (cLen + zLen * P.l + P.omega + P.k)))

/-- Algorithm 28, `w1Encode(w1)`. -/
def w1Encode (P : Params) (w1 : Array Poly) : ByteArray :=
  (List.range P.k).foldl
    (fun out i => out ++ simpleBitPack w1[i]! ((q - 1) / (2 * P.gamma2) - 1)) .empty

/-! ## §7.3 Pseudorandom sampling -/

/-- The first position `p ≥ pos` below `sampleInBallLimit` whose byte is at
most `i`: the `while j > i` rejection loop of Algorithm 29, bounded by
Appendix C. -/
def sampleIndex (s : ByteArray) (i pos : Nat) : Option Nat :=
  if pos < sampleInBallLimit then
    if s[pos]!.toNat ≤ i then some pos else sampleIndex s i (pos + 1)
  else none
termination_by sampleInBallLimit - pos

/-- Algorithm 29, `SampleInBall(ρ)`, on the XOF output `s = H(ρ)`
truncated to `sampleInBallLimit` bytes. -/
def sampleInBallOf (P : Params) (s : ByteArray) : Option Poly := Id.run do
  let mut c : Poly := zeroPoly
  let mut pos := 8
  for i in [256 - P.tau:256] do
    match sampleIndex s i pos with
    | none => return none
    | some p =>
      let j := s[p]!.toNat
      pos := p + 1
      c := c.set! i c[j]!
      c := c.set! j (if bit s (i + P.tau - 256) = 1 then -1 else 1)
  return some c

/-- Algorithm 29, `SampleInBall(ρ)`, reading the bounded prefix of H(ρ).
The seed is the whole `ρ = c̃ ∈ 𝔹^{λ/4}`. -/
def sampleInBall (P : Params) (rho : ByteArray) : Option Poly :=
  sampleInBallOf P (H rho sampleInBallLimit)

/-- Algorithm 30, `RejNTTPoly(ρ)`, on the XOF output `s = G(ρ)` truncated to
`rejNTTPolyLimit` bytes. -/
def rejNTTPolyOf (s : ByteArray) : Option Poly := Id.run do
  let mut a : Poly := zeroPoly
  let mut j := 0
  for t in [0:rejNTTPolyLimit / 3] do
    if j < 256 then
      match coeffFromThreeBytes s[3 * t]!.toNat s[3 * t + 1]!.toNat s[3 * t + 2]!.toNat with
      | some z =>
        a := a.set! j z
        j := j + 1
      | none => pure ()
  return if j < 256 then none else some a

/-- Algorithm 30, `RejNTTPoly(ρ)`, reading the bounded prefix of G(ρ). -/
def rejNTTPoly (rho : ByteArray) : Option Poly :=
  rejNTTPolyOf (G rho rejNTTPolyLimit)

/-- Algorithm 32, `ExpandA(ρ)`: `A[r][s] = RejNTTPoly(ρ ‖ s ‖ r)`. -/
def expandA (P : Params) (rho : ByteArray) : Option (Array (Array Poly)) :=
  (List.range P.k).toArray.mapM fun r =>
    (List.range P.l).toArray.mapM fun s =>
      rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])

/-! ## §7.4 High-order and low-order bits and hints -/

/-- `m mod± α`: the representative in `(−⌈α/2⌉, ⌊α/2⌋]`. -/
def modPm (m : Int) (α : Nat) : Int :=
  let r := m % (α : Int)
  if r > ((α / 2 : Nat) : Int) then r - α else r

/-- Algorithm 36, `Decompose(r)`. -/
def decompose (P : Params) (r : Int) : Int × Int :=
  let rPlus := r % (q : Int)
  let r0 := modPm rPlus (2 * P.gamma2)
  if rPlus - r0 = (q : Int) - 1 then (0, r0 - 1)
  else ((rPlus - r0) / (2 * P.gamma2 : Nat), r0)

/-- Algorithm 40, `UseHint(h, r)`. -/
def useHint (P : Params) (h : Int) (r : Int) : Int :=
  let m : Int := ((q - 1) / (2 * P.gamma2) : Nat)
  let (r1, r0) := decompose P r
  if h = 1 ∧ r0 > 0 then (r1 + 1) % m
  else if h = 1 ∧ r0 ≤ 0 then (r1 - 1) % m
  else r1

/-! ## §7.5 NTT and NTT⁻¹ -/

/-- Algorithm 43, `BitRev8(m)`. -/
def bitRev8 (m : Nat) : Nat :=
  ((List.range 8).map fun i => (m / 2 ^ (7 - i) % 2) * 2 ^ i).sum

/-- `zetas[m] = ζ^BitRev8(m) mod q` (§7.5, Appendix B). -/
def zetas (m : Nat) : Int := ((zeta ^ bitRev8 m % q : Nat) : Int)

/-- Algorithm 41, `NTT(w)`. The two `while` loops run 8 layers
(`len = 128, 64, …, 1`) and `128 / len` blocks per layer. -/
def ntt (w : Poly) : Poly := Id.run do
  let mut wh := w
  let mut m := 0
  let mut len := 128
  for _ in [0:8] do
    let mut start := 0
    for _ in [0:128 / len] do
      m := m + 1
      let z := zetas m
      for j in [start:start + len] do
        let t := z * wh[j + len]! % q
        wh := wh.set! (j + len) ((wh[j]! - t) % q)
        wh := wh.set! j ((wh[j]! + t) % q)
      start := start + 2 * len
    len := len / 2
  return wh

/-- Algorithm 42, `NTT⁻¹(ŵ)`. The two `while` loops run 8 layers
(`len = 1, 2, …, 128`) and `128 / len` blocks per layer. -/
def nttInv (wh : Poly) : Poly := Id.run do
  let mut w := wh
  let mut m := 256
  let mut len := 1
  for _ in [0:8] do
    let mut start := 0
    for _ in [0:128 / len] do
      m := m - 1
      let z := -zetas m
      for j in [start:start + len] do
        let t := w[j]!
        w := w.set! j ((t + w[j + len]!) % q)
        w := w.set! (j + len) ((t - w[j + len]!) % q)
        w := w.set! (j + len) (z * w[j + len]! % q)
      start := start + 2 * len
    len := 2 * len
  let f : Int := 8347681
  for j in [0:256] do
    w := w.set! j (f * w[j]! % q)
  return w

/-! ## §7.6 Arithmetic under NTT -/

/-- Algorithm 44, `AddNTT`. -/
def addNTT (a b : Poly) : Poly := (Array.range 256).map fun i => (a[i]! + b[i]!) % q

/-- Algorithm 45, `MultiplyNTT`. -/
def multiplyNTT (a b : Poly) : Poly := (Array.range 256).map fun i => a[i]! * b[i]! % q

/-- Algorithm 48, `MatrixVectorNTT`. -/
def matrixVectorNTT (P : Params) (M : Array (Array Poly)) (v : Array Poly) : Array Poly :=
  (Array.range P.k).map fun i =>
    (List.range P.l).foldl (fun acc j => addNTT acc (multiplyNTT M[i]![j]! v[j]!)) zeroPoly

/-! ## §6.3 Verification -/

/-- `‖z‖∞ < γ1 − β` for `z ∈ R^ℓ` (integer coefficients). -/
def normBelow (z : Array Poly) (bound : Nat) : Bool :=
  z.all fun p => p.all fun c => c.natAbs < bound

/-- Algorithm 8, `ML-DSA.Verify_internal(pk, M', σ)`. -/
def verifyInternal (P : Params) (pk M' sig : ByteArray) : Bool :=
  let (rho, t1) := pkDecode P pk
  let (cTilde, z, h?) := sigDecode P sig
  match h?, expandA P rho, sampleInBall P cTilde with
  | some h, some A, some c =>
    let tr := H pk 64
    let mu := H (tr ++ M') 64
    let cHat := ntt c
    let zHat := z.map ntt
    let t1Hat := t1.map fun p => ntt (p.map (· * 2 ^ d))
    let az := matrixVectorNTT P A zHat
    let wApprox := (Array.range P.k).map fun i =>
      nttInv ((Array.range 256).map fun j =>
        (az[i]![j]! - (multiplyNTT cHat t1Hat[i]!)[j]!) % q)
    let w1 := (Array.range P.k).map fun i =>
      (Array.range 256).map fun j => useHint P h[i]![j]! wApprox[i]![j]!
    let cTilde' := H (mu ++ w1Encode P w1) (P.lambda / 4)
    normBelow z (P.gamma1 - P.beta) && cTilde == cTilde'
  | _, _, _ => false

/-- Algorithm 3, `ML-DSA.Verify(pk, M, σ, ctx)` with the empty context:
`M' = IntegerToBytes(0, 1) ‖ IntegerToBytes(0, 1) ‖ M`. Inputs of nonstandard
length are rejected (§3.6.2). -/
def verify (P : Params) (pk msg sig : ByteArray) : Bool :=
  pk.size == pkLen P && sig.size == sigLen P &&
    verifyInternal P pk (ByteArray.mk #[0, 0] ++ msg) sig

/-! ## Table 2 sizes and Appendix C limits, checked -/

example : pkLen .mldsa44 = 1312 ∧ sigLen .mldsa44 = 2420 := by decide
example : pkLen .mldsa65 = 1952 ∧ sigLen .mldsa65 = 3309 := by decide
example : pkLen .mldsa87 = 2592 ∧ sigLen .mldsa87 = 4627 := by decide

/-- Table 3 minimums (894 bytes of G, 221 bytes of H) hold; `τ ≤ 64` keeps
the sign bits inside the first 8 bytes of H (Algorithm 29). -/
example : 894 ≤ rejNTTPolyLimit ∧ 221 ≤ sampleInBallLimit := by decide
example : Params.mldsa44.tau ≤ 64 ∧ Params.mldsa65.tau ≤ 64 ∧ Params.mldsa87.tau ≤ 64 := by
  decide

end MlDsa.Fips204
