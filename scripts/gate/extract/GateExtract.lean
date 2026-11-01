import Lean
/-!
# Gate extractor

Imports a built project from its `.olean` files and writes one TSV snapshot of
what it proves. The import runs no code of the imported modules: no
initializers, no environment-extension import hooks (`loadExts := false`).

* `C` one line per constant declared in a recorded module: comparison key,
  name, kind, module, the local and closure digests of its type and value, the
  closure digest of the whole declaration, its axioms, whether it is an
  auxiliary (elaborator/compiler-generated) name, and whether some recorded
  theorem's statement depends on it.
* `X` / `D` / `N` the policy verdict, decided here: every recorded constant whose
  axioms include one outside `--allowed`, every `axiom` declaration, and every
  name or module containing a control character.
* `H` the headline theorems (presence and axioms). `M` the recorded modules with
  their `.olean` paths, `I` each one's project imports (by path).
* `--mode bytes`: only `B` lines, the evaluated bytes of the bytecode literals.
  Evaluation runs the literal's compiled code, so it is a separate process.

Digests are SHA-256 (output truncated to 128 bits). `local` digests an
expression's structure with constant names only; `closure` additionally folds
in, for every constant the expression mentions, the meaning of that constant:
for a theorem its statement, for a definition its type and value, for an
inductive its constructors, recursively through every recorded constant.
Constants outside the recorded modules are digested by name: they come from the
pinned toolchain and `lake-manifest.json`, which the gate requires to be
identical. Private names are digested by their user name, so a pure move keeps
every digest.

Usage: `lake env gate_extract --roots A,B --build-dir DIR [--exclude FILE] [--key-prefix P]
  --allowed propext,... [--headline N,...] --out FILE`
(project = every imported module whose `.olean` resolves under DIR; `--exclude` lists
`.olean` paths recorded by an earlier run)
       `lake env gate_extract --mode bytes --roots A,B --bytecode N,... --out FILE`
-/

open Lean

namespace GateExtract

/-! ## SHA-256 (FIPS 180-4) -/

def K256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let bits := msg.size * 8
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do m := m.push 0
  for i in [0:8] do m := m.push (bits >>> (8 * (7 - i))).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  let mut w : Array UInt32 := Array.replicate 64 0
  for blk in [0:m.size / 64] do
    for t in [0:16] do
      let o := blk * 64 + 4 * t
      w := w.set! t ((m[o]!.toUInt32 <<< 24) ||| (m[o+1]!.toUInt32 <<< 16) |||
        (m[o+2]!.toUInt32 <<< 8) ||| m[o+3]!.toUInt32)
    for t in [16:64] do
      let x := w[t-15]!
      let y := w[t-2]!
      let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
      let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for t in [0:64] do
      let t1 := hh + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) +
        K256[t]! + w[t]!
      let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
      hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + hh]
  let mut out := ByteArray.empty
  for x in h do
    out := out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8
      |>.push x.toUInt8
  return out

def hexOf (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat); if s.length < 2 then "0" ++ s else s)

/-- A digest: SHA-256 over a tag and length-prefixed parts (unambiguous encoding). -/
def node (tag : UInt8) (parts : Array ByteArray) : ByteArray := Id.run do
  let mut b := ByteArray.empty.push tag
  for p in parts do
    let n := p.size
    b := b.push (n >>> 24).toUInt8 |>.push (n >>> 16).toUInt8 |>.push (n >>> 8).toUInt8
      |>.push n.toUInt8
    b := b ++ p
  return sha256 b

def dstr (s : String) : ByteArray := s.toUTF8
def dnat (n : Nat) : ByteArray := (toString n).toUTF8
def dbool (b : Bool) : ByteArray := ByteArray.empty.push (if b then 1 else 0)

/-- Length-prefixed bytes (so that concatenations stay unambiguous). -/
def lp (b : ByteArray) : ByteArray :=
  let n := b.size
  (ByteArray.empty.push (n >>> 24).toUInt8 |>.push (n >>> 16).toUInt8 |>.push (n >>> 8).toUInt8
    |>.push n.toUInt8) ++ b

/-- A name as bytes, component by component (injective; not hashed). -/
def dnameRaw (n : Name) : ByteArray :=
  n.components.foldl (init := ByteArray.empty) fun acc c => match c with
    | .str _ s => acc.push 0x73 ++ lp (dstr s)
    | .num _ k => acc.push 0x6e ++ lp (dnat k)
    | .anonymous => acc

/-- Private names by their user name: the module they live in is not part of their meaning. -/
def dname (n : Name) : ByteArray :=
  match privateToUserName? n with
  | some u => ByteArray.empty.push 0x70 ++ lp (dnameRaw u)
  | none => ByteArray.empty.push 0x67 ++ lp (dnameRaw n)

partial def dlevel : Level → ByteArray
  | .zero => ByteArray.empty.push 10
  | .succ l => ByteArray.empty.push 11 ++ lp (dlevel l)
  | .max a b => ByteArray.empty.push 12 ++ lp (dlevel a) ++ lp (dlevel b)
  | .imax a b => ByteArray.empty.push 13 ++ lp (dlevel a) ++ lp (dlevel b)
  | .param n => ByteArray.empty.push 14 ++ lp (dnameRaw n)
  | .mvar id => ByteArray.empty.push 15 ++ lp (dnameRaw id.name)

def dnames (ns : List Name) : ByteArray := ns.foldl (init := ByteArray.empty.push 16) fun acc n => acc ++ lp (dname n)

structure Ctx where
  env : Environment
  /-- Is this constant declared in a recorded (project) module? -/
  isProject : Name → Bool

structure St where
  sh : Std.HashMap Expr ByteArray := {}
  ch : Std.HashMap Name ByteArray := {}
  inprog : NameSet := {}

abbrev M := ReaderT Ctx (StateT St IO)

/-- Leaf encoding: tag 0 and the leaf's bytes, not hashed. -/
def leaf (tag : UInt8) (b : ByteArray) : ByteArray := (ByteArray.empty.push 0 |>.push tag) ++ b

/-- Structural encoding (binder names, binder info and metadata ignored): a leaf inline
(tag 0), any other node as tag 1 and the SHA-256 of its tag and children's encodings. -/
partial def sh (e : Expr) : M ByteArray := do
  match e with
  | .bvar i => return leaf 20 (dnat i)
  | .fvar id => return leaf 21 (dnameRaw id.name)
  | .mvar id => return leaf 22 (dnameRaw id.name)
  | .sort l => return leaf 23 (dlevel l)
  | .const n us => return leaf 24 (us.foldl (init := lp (dname n)) fun acc u => acc ++ lp (dlevel u))
  | .lit (.natVal n) => return leaf 29 (dnat n)
  | .mdata _ b => return (← sh b)
  | _ => pure ()
  if let some h := (← get).sh[e]? then return h
  let d ← match e with
    | .app f a => pure (node 25 #[← sh f, ← sh a])
    | .lam _ t b _ => pure (node 26 #[← sh t, ← sh b])
    | .forallE _ t b _ => pure (node 27 #[← sh t, ← sh b])
    | .letE _ t v b _ => pure (node 28 #[← sh t, ← sh v, ← sh b])
    | .lit (.strVal s) => pure (node 30 #[dstr s])
    | .proj s i b => pure (node 31 #[dname s, dnat i, ← sh b])
    | _ => pure (node 32 #[])
  let h := ByteArray.empty.push 1 ++ d
  modify fun st => { st with sh := st.sh.insert e h }
  return h

/-- The constants of one mutual block (inductive types with their constructors and
recursors, or mutual definitions): references inside a block are digested by name. -/
def blockOf (env : Environment) (ci : ConstantInfo) : NameSet :=
  let ofInds (inds : List Name) : NameSet := inds.foldl (init := {}) fun s i =>
    let s := s.insert i
    match env.find? i with
    | some (.inductInfo v) => v.ctors.foldl (·.insert ·) s
    | _ => s
  match ci with
  | .inductInfo v => ofInds v.all
  | .ctorInfo v => match env.find? v.induct with
    | some (.inductInfo iv) => ofInds iv.all
    | _ => ({} : NameSet).insert v.induct
  | .recInfo v => (ofInds v.all).insert ci.name
  | .defnInfo v => v.all.foldl (·.insert ·) {}
  | .thmInfo v => v.all.foldl (·.insert ·) {}
  | .opaqueInfo v => v.all.foldl (·.insert ·) {}
  | _ => ({} : NameSet).insert ci.name

mutual
/-- Digest of one declaration: kind, universe parameters, type and, per kind, body,
constructors or recursor rules (closure digests, block members by name). -/
partial def hdecl (ci : ConstantInfo) : M ByteArray := do
  let env := (← read).env
  let blk := blockOf env ci
  let base := #[dname ci.name, dnames ci.levelParams, ← hstar blk ci.type]
  match ci with
  | .axiomInfo v => return node 51 (base.push (dbool v.isUnsafe))
  | .defnInfo v =>
    return node 52 (base ++ #[← hstar blk v.value, dstr (toString (repr v.safety))])
  | .thmInfo _ => return node 53 base
  | .opaqueInfo v => return node 54 (base ++ #[← hstar blk v.value, dbool v.isUnsafe])
  | .quotInfo v => return node 55 (base.push (dnat (match v.kind with
      | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4)))
  | .inductInfo v =>
    let mut cs : Array ByteArray := #[]
    for k in v.ctors do
      let t ← match env.find? k with
        | some kci => hstar blk kci.type
        | none => pure (node 0 #[])
      cs := cs.push (node 0 #[dname k, t])
    return node 56 (base ++ #[dnat v.numParams, dnat v.numIndices, dbool v.isRec,
      dbool v.isUnsafe, dbool v.isReflexive, dnat v.numNested, dnames v.all] ++ cs)
  | .ctorInfo v => return node 57 (base ++ #[dname v.induct, dnat v.cidx, dnat v.numParams,
      dnat v.numFields, dbool v.isUnsafe])
  | .recInfo v =>
    let mut rs : Array ByteArray := #[]
    for r in v.rules do
      rs := rs.push (node 0 #[dname r.ctor, dnat r.nfields, ← hstar blk r.rhs])
    return node 58 (base ++ #[dnat v.numParams, dnat v.numIndices, dnat v.numMotives,
      dnat v.numMinors, dbool v.k, dbool v.isUnsafe, dnames v.all] ++ rs)

/-- Closure digest of an expression: its structure, and the closure digest of every
constant it mentions (block members by name). -/
partial def hstar (blk : NameSet) (e : Expr) : M ByteArray := do
  let mut parts := #[← sh e]
  for d in e.getUsedConstants do
    let hd ← if blk.contains d then pure (ByteArray.empty.push 71) else hconst d
    parts := parts ++ #[dname d, hd]
  return node 70 parts

/-- Closure digest of a constant (its meaning, see the module docstring). Caches; the
body is `hdecl` so that its early `return`s cannot skip the cache bookkeeping. -/
partial def hconst (c : Name) : M ByteArray := do
  let ctx ← read
  if !ctx.isProject c then return ByteArray.empty.push 41 ++ dname c
  if let some h := (← get).ch[c]? then return h
  if (← get).inprog.contains c then return node 42 #[dname c]
  modify fun st => { st with inprog := st.inprog.insert c }
  let h ← match ctx.env.find? c with
    | none => pure (node 43 #[dname c])
    | some ci => hdecl ci
  modify fun st => { st with ch := st.ch.insert c h, inprog := st.inprog.erase c }
  return h
end

def hex128 (d : ByteArray) : String := hexOf (d.extract 0 16)

/-! ## Axioms

`Lean.collectAxioms` reads the axiom sets that each module's export recorded in an
environment extension, which only loads with `loadExts := true` (running the
imported modules' initializers). This is Lean v4.33.0's
`Lean.CollectAxioms.collect` (`Lean/Util/CollectAxioms.lean`, private there),
verbatim except that it has no extension lookup: it walks every body, with
one cache shared by all constants. -/

namespace Axioms

structure State where
  seen   : NameMap (Array Name) := {}
  axioms : NameSet := {}

abbrev AM := ReaderT Environment $ StateM State

private def insertArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

partial def collect (c : Name) : AM Unit := do
  let env ← read
  let s ← get
  if let some axs := s.seen.find? c then
    modify fun s => { s with axioms := insertArray s.axioms axs }
    return
  let savedAxioms := s.axioms
  modify fun s => { s with axioms := {}, seen := s.seen.insert c #[] }
  let collectExpr (e : Expr) : AM Unit := e.getUsedConstants.forM collect
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
  | none                 => pure ()
  let collected := (← get).axioms
  let result := collected.toArray.qsort Name.lt
  modify fun s => { s with
    seen   := s.seen.insert c result
    axioms := insertArray savedAxioms result
  }

def collectAndGet (c : Name) : AM (Array Name) := do
  collect c
  return (← get).seen.find? c |>.getD #[]

end Axioms

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => match v.safety with
    | .safe => "def" | .unsafe => "def-unsafe" | .partial => "def-partial"
  | .thmInfo _ => "theorem"
  | .opaqueInfo v => if v.isUnsafe then "opaque-unsafe" else "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants whose meaning enters a closure digest of `ci` (the edges of `hconst`). -/
def meaningDeps (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => ds := ds ++ v.value.getUsedConstants
  | .opaqueInfo v => ds := ds ++ v.value.getUsedConstants
  | .inductInfo v =>
    for k in v.ctors do
      ds := ds.push k
      if let some kci := env.find? k then ds := ds ++ kci.type.getUsedConstants
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v => for r in v.rules do ds := ds ++ r.rhs.getUsedConstants
  | _ => pure ()
  return ds

/-- Project constants some recorded theorem's statement depends on, through types,
definition bodies and constructors. Only for these does a definition's body matter:
the body of any other definition (tactics, simprocs, executables' code) cannot
change what a theorem states. -/
def relevant (env : Environment) (isProject : Name → Bool) (seeds : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := seeds.toList
  while true do
    match todo with
    | [] => break
    | c :: tl =>
      todo := tl
      if seen.contains c || !isProject c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        for d in meaningDeps env ci do
          if !seen.contains d && isProject d then todo := d :: todo
  return seen

/-- Elaborator- or compiler-generated names (`match_1`, `proof_1`, `eq_1`, `_cstage1`,
`eq_def`, ...): whether they exist depends on how proofs are written, so the
signature diff does not compare them by name (their meaning still enters every
closure digest and their axioms are still audited). -/
def isAux (env : Environment) (n : Name) : Bool :=
  let u := privateToUserName n
  u.isInternalDetail || isReservedName env n || isReservedName env u

def parseArgs (args : List String) : Std.HashMap String (List String) := Id.run do
  let mut m : Std.HashMap String (List String) := {}
  let mut rest := args
  while true do
    match rest with
    | k :: v :: tl =>
      m := m.insert k ((v.splitOn ",").filter (· ≠ ""))
      rest := tl
    | _ => break
  return m

/-- Characters that some reader could take as a field or line separator. -/
def isSep (c : Char) : Bool :=
  c.toNat < 32 || c.toNat == 127 || c.toNat == 0x85 || c.toNat == 0x2028 || c.toNat == 0x2029

def hasControl (s : String) : Bool := s.any isSep

/-- Escape so that a field can never contain a tab or a line break. -/
def esc (s : String) : String := s.foldl (init := "") fun acc c =>
  if c == '\\' then acc ++ "\\\\"
  else if isSep c then acc ++ s!"\\x{c.toNat}"
  else acc.push c

def readLines (path? : Option String) : IO (List String) := do
  match path? with
  | none => return []
  | some p => return ((← IO.FS.readFile p).splitOn "\n").filter (· ≠ "")

end GateExtract

open GateExtract in
unsafe def main (args : List String) : IO UInt32 := do
  let a := parseArgs args
  let get (k : String) := a.getD k []
  if get "--selftest" == ["sha256"] then
    let ok := hexOf (sha256 "abc".toUTF8) ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
      hexOf (sha256 (String.ofList (List.replicate 1000 'a')).toUTF8) ==
      "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
    IO.println (if ok then "sha256 ok" else "sha256 WRONG")
    return if ok then 0 else 1
  let roots := (get "--roots").map String.toName
  let some out := (get "--out").head? | throw <| IO.userError "missing --out"
  if roots.isEmpty then throw <| IO.userError "missing --roots"
  initSearchPath (← findSysroot)
  if get "--mode" == ["bytes"] then
    -- evaluates compiled code of the revision: only `B` lines, in a process of its own
    let env ← importModules (roots.toArray.map ({ module := · })) {}
    let mut lines : Array String := #[]
    for b in (get "--bytecode").map String.toName do
      match env.evalConst ByteArray {} b (checkMeta := false) with
      | .ok bytes => lines := lines.push s!"B\t{esc (toString b)}\t{bytes.size}\t{hexOf bytes}"
      | .error e => lines := lines.push s!"B\t{esc (toString b)}\terror\t{esc e}"
    IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
    return 0
  -- Rule: `sorryAx`, `Lean.trustCompiler` and the `native_decide` / `bv_decide`
  -- axioms are rejected whatever the allowlist says.
  let never : List Name := [``sorryAx, ``Lean.trustCompiler, ``Lean.ofReduceBool, ``Lean.ofReduceNat]
  let allowed := ((get "--allowed").map String.toName).filter (· ∉ never)
  -- `--build-dir`: the worktree's build output. A module is local (project) iff the .olean
  -- this import resolved to lies under it; `--exclude` lists .olean paths already recorded.
  let some buildDir := (get "--build-dir").head? | throw <| IO.userError "missing --build-dir"
  let buildDir ← IO.FS.realPath buildDir
  let excluded := (← readLines (get "--exclude").head?)
  let keyPrefix := (get "--key-prefix").headD ""
  -- no initializers run, no extension import hooks (see the module docstring)
  let env ← importModules (loadExts := false) (roots.toArray.map ({ module := · })) {}
  let modNames := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => modNames[i.toNat]!
  let mut localPath : NameMap String := {}
  for m in modNames do
    let f ← IO.FS.realPath (← findOLean m)
    if (buildDir.toString ++ "/").isPrefixOf f.toString then
      localPath := localPath.insert m f.toString
  let isLocal (m : Name) := localPath.contains m
  let isRec (m : Name) := match localPath.find? m with
    | some f => !excluded.contains f
    | none => false
  let isProject (n : Name) := match modOf n with
    | some m => isLocal m
    | none => false
  let mut lines : Array String := #[]
  let mut nViol := 0
  for m in modNames, d in env.header.moduleData do
    if isRec m then
      let f := localPath.find? m |>.getD ""
      lines := lines.push s!"M\t{esc (toString m)}\t{esc f}"
      let imps := d.imports.toList.filterMap fun i => localPath.find? i.module
      lines := lines.push s!"I\t{esc f}\t{",".intercalate (imps.map esc)}"
      if hasControl (toString m) || hasControl f || f.any (· == ',') then
        nViol := nViol + 1
        lines := lines.push s!"N\t{esc (toString m)}"
  let mut consts : Array (Name × ConstantInfo × Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some m := modOf n then
      if isRec m then consts := consts.push (n, ci, m)
  consts := consts.qsort (fun x y => Name.lt x.1 y.1)
  -- comparison keys: private names by their user name (so a pure move keeps its key)
  let mut keyCount : Std.HashMap Name Nat := {}
  for (n, _, _) in consts do
    let u := privateToUserName n
    keyCount := keyCount.insert u (keyCount.getD u 0 + 1)
  let ctx : Ctx := { env, isProject }
  let coreCtx : Core.Context := { fileName := "<gate>", fileMap := default }
  let coreSt : Core.State := { env }
  let t0 ← IO.monoMsNow
  IO.eprintln s!"gate_extract: imported, {consts.size} constants to record"
  -- one state for all constants (the caches must not be shared, or every insert copies them)
  let (rows, _) ← (consts.mapM fun (n, ci, _) => do
      let blk := blockOf env ci
      let lt ← sh ci.type
      let ct ← hstar blk ci.type
      let (lv, cv) ← match valueOf? ci with
        | some v => pure (hex128 (← sh v), hex128 (← hstar blk v))
        | none => pure ("-", "-")
      let full ← hconst n
      return (hex128 lt, hex128 ct, lv, cv, hex128 full) : M _).run ctx |>.run {}
  let t1 ← IO.monoMsNow
  let heads := (get "--headline").map String.toName
  let axList := (Id.run <| (do
      let xs ← consts.mapM fun (n, _, _) => Axioms.collectAndGet n
      let hs ← heads.toArray.mapM fun h => Axioms.collectAndGet h
      return (xs, hs) : Axioms.AM _).run env |>.run' {})
  let (axs, headAxs) := axList
  IO.eprintln s!"gate_extract: digests {t1 - t0} ms, axioms {(← IO.monoMsNow) - t1} ms"
  let thmTypes := consts.foldl (init := #[]) fun acc (_, ci, _) =>
    if ci matches .thmInfo _ then acc ++ ci.type.getUsedConstants else acc
  let rel := relevant env isProject thmTypes
  for (n, ci, m) in consts, (lt, ct, lv, cv, full) in rows, ax in axs do
    let u := privateToUserName n
    let key := if keyCount.getD u 0 > 1 then s!"{u}@{m}" else
      if isPrivateName n then s!"private:{u}" else toString u
    let axStr := if ax.isEmpty then "-" else ",".intercalate (ax.toList.map (esc ∘ toString))
    -- a theorem the user wrote (it has a source range) is compared whatever its name
    let written ← if ci matches .thmInfo _ then
        pure (← (findDeclarationRanges? n : CoreM _).toIO coreCtx coreSt).1.isSome
      else pure false
    let aux := isAux env n && !written
    let nm := esc (toString n)
    lines := lines.push s!"C\t{keyPrefix}{esc key}\t{nm}\t{kindOf ci}\t{esc (toString m)}\t{lt}\t{ct}\t{lv}\t{cv}\t{full}\t{axStr}\t{if aux then 1 else 0}\t{if rel.contains n then 1 else 0}"
    if hasControl (toString n) then
      nViol := nViol + 1
      lines := lines.push s!"N\t{nm}"
    for x in ax do
      if x ∉ allowed then
        nViol := nViol + 1
        lines := lines.push s!"X\t{nm}\t{esc (toString x)}"
    if ci matches .axiomInfo _ then
      nViol := nViol + 1
      lines := lines.push s!"D\t{nm}"
  for h in heads, ax in headAxs do
    let k := match env.find? h with | some ci => kindOf ci | none => "missing"
    lines := lines.push s!"H\t{esc (toString h)}\t{k}\t{",".intercalate (ax.toList.map (esc ∘ toString))}"
  lines := lines.push s!"P\tviolations\t{nViol}"
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"gate_extract: {consts.size} constants, {nViol} policy violations"
  return 0
