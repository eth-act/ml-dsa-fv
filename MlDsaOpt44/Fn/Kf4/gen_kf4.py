#!/usr/bin/env python3
"""Symbolic execution of the kf4 kernel (listing indices 10319..11442).

Prints the term shapes of one loop iteration (two rounds) so that the Lean
model (`Kf4/Model.lean`) and the block lemmas (`Kf4/Blocks*.lean`) can be
generated / checked against the bytecode.
"""
import sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
LISTING = os.path.join(HERE, '..', '..', 'listing.tsv')


def load():
    rows = {}
    with open(LISTING) as f:
        next(f)
        for line in f:
            i, pc, ins = line.rstrip('\n').split('\t')
            rows[int(i)] = (int(pc), ins)
    return rows


ROWS = load()


class Sym:
    def __init__(self, stack, mem='M'):
        self.s = list(stack)  # top = s[0]
        self.stores = []      # (addr, value)

    def run(self, lo, hi):
        """Run indices lo..hi-1."""
        for i in range(lo, hi):
            pc, ins = ROWS[i]
            self.step(i, ins)

    def step(self, i, ins):
        s = self.s
        p = ins.split()
        op = p[0]
        if op.startswith('PUSH'):
            v = 0 if op == 'PUSH0' else int(p[1], 16)
            s.insert(0, ('c', v))
        elif op.startswith('DUP'):
            k = int(op[3:])
            s.insert(0, s[k - 1])
        elif op.startswith('SWAP'):
            k = int(op[4:])
            s[0], s[k] = s[k], s[0]
        elif op == 'POP':
            s.pop(0)
        elif op == 'MLOAD':
            a = s.pop(0)
            s.insert(0, ('ld', a))
        elif op == 'MSTORE':
            a = s.pop(0)
            v = s.pop(0)
            self.stores.append((a, v))
        elif op in ('XOR', 'AND', 'OR', 'ADD', 'GT'):
            a = s.pop(0)
            b = s.pop(0)
            s.insert(0, (op.lower(), a, b))
        elif op in ('SHL', 'SHR'):
            sh = s.pop(0)
            v = s.pop(0)
            assert sh[0] == 'c'
            s.insert(0, (op.lower(), v, sh[1]))
        elif op == 'NOT':
            a = s.pop(0)
            s.insert(0, ('not', a))
        elif op == 'JUMPDEST':
            pass
        else:
            raise Exception(f'{i}: {ins}')


def simp(t):
    """Recognise rotations."""
    if not isinstance(t, tuple):
        return t
    if t[0] == 'c' or t[0] == 'v':
        return t
    if t[0] in ('shl', 'shr'):
        return (t[0], simp(t[1]), t[2])
    t = (t[0],) + tuple(simp(x) for x in t[1:])
    if t[0] == 'or' and t[1][0] == 'shr' and t[2][0] == 'shl' and t[1][1] == t[2][1] \
            and t[1][2] + t[2][2] == 256:
        return ('rot', t[1][1], t[2][2])
    return t


def show(t, names=None):
    names = names or {}
    if t in names:
        return names[t]
    k = t[0]
    if k == 'c':
        return hex(t[1])
    if k == 'v':
        return t[1]
    if k == 'ld':
        return f"ld[{show(t[1], names)}]"
    if k == 'rot':
        return f"rot({show(t[1], names)},{t[2]})"
    if k == 'not':
        return f"~{show(t[1], names)}"
    return f"{k}({', '.join(show(x, names) for x in t[1:])})"


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1].isdigit():
    st = Sym([('v', 'rp'), ('v', 'ret')])
    st.run(10319, 10321)
    st.s = [('v', 'rp'), ('v', 'ret')]
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 10321
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 10877
    st.run(lo, hi)
    for a, v in st.stores:
        print('STORE', show(simp(a)), '<-', show(simp(v)))
    print('STACK')
    for v in st.s:
        print('  ', show(simp(v)))


# ---------------------------------------------------------------------------
# Lean generation
# ---------------------------------------------------------------------------

ROT = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
       41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
CPL = [1, 2, 8, 12, 17, 20]
DORDER = [1, 2, 3, 0, 4]          # stack order of the D values (top first)
ROUND = [10321, 10877]           # first index of each round
TAIL = 11434


def gas(i):
    o = ROWS[i][1].split()[0]
    if o == 'JUMPDEST':
        return 1
    if o in ('PUSH0', 'POP'):
        return 2
    if o == 'JUMPI':
        return 10
    if o == 'JUMP':
        return 8
    return 3


def row_src(y, xo):
    """Source lane of output position (xo, y) and its column / rotation."""
    s = (xo + 3 * y) % 5 + 5 * xo
    return s, s % 5, ROT[s]


def blocks(r):
    """Block index ranges [lo, hi) of round r (0/1)."""
    lo = ROUND[r]
    hi = ROUND[1] if r == 0 else TAIL
    c = lo + 70 + (1 if r == 0 else 0)
    out = [(lo, c)]
    i = c
    j = i + 51
    out.append((i, j))
    i = j
    stores = 0
    for k in range(j, hi):
        if ROWS[k][1] == 'MSTORE':
            stores += 1
            if stores % 5 == 0:
                end = k + 1
                if stores == 25:
                    end = hi
                out.append((i, end))
                i = end
    return out


def tmpl(t, y, x, rc_name='rc'):
    """Lean term (generic in `O`) of a chi output tree with B leaves b0 b1 b2."""
    def leaf_b(t):
        for j in range(3):
            xo = (x + j) % 5
            s, c, r = row_src(y, xo)
            if r:
                if t == ('rot', ('xor', ('v', f'd{c}'), ('ld', ('c', SRC + 32 * s))), 4 * r):
                    return f'b{j}'
            else:
                if t == ('xor', ('v', f'd{c}'), ('ld', ('c', SRC + 32 * s))):
                    return f'b{j}'
        return None

    def go(t):
        b = leaf_b(t)
        if b:
            return b
        k = t[0]
        if k == 'ld':
            return rc_name
        if k == 'not':
            return f'(O.not {go(t[1])})'
        if k in ('xor', 'and', 'or'):
            return f'(O.{k} {go(t[1])} {go(t[2])})'
        raise Exception(t)
    return go(t)


SRC = 0


def round_stores():
    st = Sym([('v', f'd{c}') for c in DORDER] + [('v', 'rp'), ('v', 'ret')])
    b = blocks(0)
    st.run(b[2][0], ROUND[1])
    return [(simp(a), simp(v)) for a, v in st.stores]


def masks():
    cm = [1 if i in CPL else 0 for i in range(25)]
    cmC = [cm[x] ^ cm[x + 5] ^ cm[x + 10] ^ cm[x + 15] ^ cm[x + 20] for x in range(5)]
    mD = [cmC[(x + 4) % 5] ^ cmC[(x + 1) % 5] for x in range(5)]
    mB = [cm[s] ^ mD[s % 5] for s in range(25)]
    return cm, cmC, mD, mB


def evalb(t, env):
    k = t[0]
    if k == 'v':
        return env[t[1]]
    if k == 'not':
        return 1 - evalb(t[1], env)
    a, b = evalb(t[1], env), evalb(t[2], env)
    return {'xor': a ^ b, 'and': a & b, 'or': a | b}[k]


def parse_tmpl(s):
    """Tiny parser for the generated template strings (for checking)."""
    toks = s.replace('(', ' ( ').replace(')', ' ) ').split()
    pos = [0]

    def p():
        t = toks[pos[0]]
        pos[0] += 1
        if t == '(':
            op = toks[pos[0]]
            pos[0] += 1
            args = []
            while toks[pos[0]] != ')':
                args.append(p())
            pos[0] += 1
            return (op.split('.')[1],) + tuple(args)
        return ('v', t)
    return p()


def chi_data():
    """Per output (y, x): template string, input masks, output mask."""
    cm, cmC, mD, mB = masks()
    stores = round_stores()
    res = {}
    for n, (a, v) in enumerate(stores):
        y, x = divmod(n, 5)
        assert a == ('c', 0x400 + 32 * n), a
        t = tmpl(v, y, x)
        ms = [mB[row_src(y, (x + j) % 5)[0]] for j in range(3)]
        mo = cm[n]
        tree = parse_tmpl(t)
        for bits in range(16):
            env = {'b0': bits & 1, 'b1': bits >> 1 & 1, 'b2': bits >> 2 & 1, 'rc': bits >> 3 & 1}
            env2 = {k: env[k] ^ ms[int(k[1])] if k[0] == 'b' else env[k] for k in env}
            got = evalb(tree, env2)
            want = env['b0'] ^ ((1 - env['b1']) & env['b2']) ^ mo ^ (env['rc'] if n == 0 else 0)
            assert got == want, (y, x, t, ms, mo)
        res[(y, x)] = (t, ms, mo)
    return res


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'chi':
    for k, v in chi_data().items():
        print(k, v)
    print(blocks(0))
    print(blocks(1))


# D values: D_c = dL(C_{c-1}, C_{c+1}) or dR(...) (code operand order)
def d_shape():
    """Return {c: ('dL'|'dR')} from the theta block of round 1."""
    st = Sym([('v', 'rp'), ('v', 'ret')])
    st.run(10321, 10443)
    def col(t):
        # t = xor(ld[x+20], xor(... ld[x]))
        while t[0] == 'xor':
            t = t[2]
        return t[1][1] // 32
    res = {}
    for pos, v in enumerate(st.s[:5]):
        v = simp(v)
        c = DORDER[pos]
        p, q = (c + 4) % 5, (c + 1) % 5
        if v[1][0] == 'rot':
            assert v[1][2] == 4 and col(v[1][1]) == q and col(v[2]) == p
            res[c] = 'dL'
        else:
            assert v[2][0] == 'rot' and v[2][2] == 4 and col(v[2][1]) == q and col(v[1]) == p
            res[c] = 'dR'
    return res


def gen_model():
    chi = chi_data()
    ds = d_shape()
    L = []
    w = L.append
    w('''import MlDsaOpt44.Layout
/-! Generated by `Kf4/gen_kf4.py`: the word-level model of one `kf4` round.

`Ops α` packages the five word operations of the kernel; `Ops256` is the EVM
semantics (rotations by `4n` bits of the interleaved words), `Ops64` the
per-slot semantics (`rotl64`). The theta, `B` and chi pieces are stated once,
generically, in the exact operand order of the bytecode. -/

namespace MlDsaOpt44.Proofs.Kf4

open EvmSemantics
open EvmSemantics.EVM

structure Ops (α : Type) where
  xor : α → α → α
  and : α → α → α
  or : α → α → α
  not : α → α
  rot : α → Nat → α

/-- `mload(a)`. -/
def ldY (M : ByteArray) (a : Nat) : UInt256 := MachineState.readWord M a

/-- `mstore(a, v)`. -/
def stY (M : ByteArray) (a : Nat) (v : UInt256) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded v.toNat 32) a

/-- `DUP1 PUSH 4n SHL SWAP1 PUSH (256-4n) SHR OR`: 256-bit rotation by `4n`. -/
def rot256 (x : UInt256) (n : Nat) : UInt256 :=
  UInt256.lor (UInt256.shiftRight x (UInt256.ofNat (256 - 4 * n)))
    (UInt256.shiftLeft x (UInt256.ofNat (4 * n)))

def Ops256 : Ops UInt256 := ⟨UInt256.xor, UInt256.land, UInt256.lor, UInt256.lnot, rot256⟩

def Ops64 : Ops UInt64 :=
  ⟨(· ^^^ ·), (· &&& ·), (· ||| ·), (~~~ ·), EvmSemantics.Crypto.Keccak.rotl64⟩

variable {α : Type}

/-- Column parity `C_x` from the lanes `x, x+5, …, x+20`. -/
def colC (O : Ops α) (a0 a1 a2 a3 a4 : α) : α := O.xor a4 (O.xor a3 (O.xor a2 (O.xor a1 a0)))

/-- `D = rot(q, 1) ^ p` (`p = C_{x-1}`, `q = C_{x+1}`). -/
def dL (O : Ops α) (p q : α) : α := O.xor (O.rot q 1) p

/-- `D = p ^ rot(q, 1)`. -/
def dR (O : Ops α) (p q : α) : α := O.xor p (O.rot q 1)

/-- `B = rot(d ^ a, r)`. -/
def bv (O : Ops α) (d a : α) (r : Nat) : α := O.rot (O.xor d a) r

/-- `B = d ^ a` (lane 0, no rotation). -/
def bv0 (O : Ops α) (d a : α) : α := O.xor d a
''')
    for y in range(5):
        for x in range(5):
            t, ms, mo = chi[(y, x)]
            extra = ' (rc : α)' if (y, x) == (0, 0) else ''
            w(f'def ch{y}{x} (O : Ops α) (b0 b1 b2 : α){extra} : α := {t}\n')
    # per-lane functions of the 25 input lanes
    w('\n/-! ## Each output lane as a function of the 25 input lanes -/\n')
    for c in range(5):
        p, q = (c + 4) % 5, (c + 1) % 5
        cp = ' '.join(f'(c {p + 5 * k})' for k in range(5))
        cq = ' '.join(f'(c {q + 5 * k})' for k in range(5))
        w(f'def dO{c} (O : Ops α) (c : Fin 25 → α) : α := {ds[c]} O (colC O {cp}) (colC O {cq})\n')
    for y in range(5):
        for x in range(5):
            bs = []
            for j in range(3):
                s_, c_, r_ = row_src(y, (x + j) % 5)
                if r_:
                    bs.append(f'(bv O (dO{c_} O c) (c {s_}) {r_})')
                else:
                    bs.append(f'(bv0 O (dO{c_} O c) (c {s_}))')
            if (y, x) == (0, 0):
                w(f'def out{y}{x} (O : Ops α) (c : Fin 25 → α) (rc : α) : α :=\n  ch{y}{x} O {" ".join(bs)} rc\n')
            else:
                w(f'def out{y}{x} (O : Ops α) (c : Fin 25 → α) (_rc : α) : α :=\n  ch{y}{x} O {" ".join(bs)}\n')
    # theta D values of memory
    w('\n/-- Column parity of the lanes at `src`. -/')
    w('def colM (M : ByteArray) (src x : Nat) : UInt256 :=')
    w('  colC Ops256 (ldY M (src + 32 * x)) (ldY M (src + 32 * (x + 5))) (ldY M (src + 32 * (x + 10)))')
    w('    (ldY M (src + 32 * (x + 15))) (ldY M (src + 32 * (x + 20)))\n')
    for c in range(5):
        p, q = (c + 4) % 5, (c + 1) % 5
        w(f'def thD{c} (M : ByteArray) (src : Nat) : UInt256 := {ds[c]} Ops256 (colM M src {p}) (colM M src {q})\n')
    # rows
    for y in range(5):
        extra = ' (rc : UInt256)' if y == 0 else ''
        w(f'/-- Output row {y}: the five chi stores (loads from `M`). -/')
        w(f'def row{y} (M : ByteArray) (src dst : Nat) (d0 d1 d2 d3 d4 : UInt256){extra} : ByteArray :=')
        bs = []
        for xo in range(5):
            s, c, r = row_src(y, xo)
            if r:
                bs.append(f'(bv Ops256 d{c} (ldY M (src + {32 * s})) {r})')
            else:
                bs.append(f'(bv0 Ops256 d{c} (ldY M (src + {32 * s})))')
        mem = 'M'
        for x in range(5):
            args = ' '.join(bs[(x + j) % 5] for j in range(3))
            rc = ' rc' if (y, x) == (0, 0) else ''
            mem = f'(stY {mem} (dst + {32 * (5 * y + x)})\n    (ch{y}{x} Ops256 {args}{rc}))'
        w('  ' + mem[1:-1] + '\n')
    w('''/-- One round: theta from `M`, then the five rows; iota from `ldY M rca`. -/
def roundM (M : ByteArray) (src dst rca : Nat) : ByteArray :=
  let d0 := thD0 M src
  let d1 := thD1 M src
  let d2 := thD2 M src
  let d3 := thD3 M src
  let d4 := thD4 M src
  let M1 := row0 M src dst d0 d1 d2 d3 d4 (ldY M rca)
  let M2 := row1 M1 src dst d0 d1 d2 d3 d4
  let M3 := row2 M2 src dst d0 d1 d2 d3 d4
  let M4 := row3 M3 src dst d0 d1 d2 d3 d4
  row4 M4 src dst d0 d1 d2 d3 d4

/-- One loop iteration: `KS → KB` with `RC4[r]`, then `KB → KS` with `RC4[r+1]`. -/
def iterM (M : ByteArray) (rp : Nat) : ByteArray :=
  roundM (roundM M 0 0x400 rp) 0x400 0 (32 + rp)

end MlDsaOpt44.Proofs.Kf4
''')
    return '\n'.join(L)


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'model':
    open(os.path.join(HERE, 'Model.lean'), 'w').write(gen_model())


LOOP = '''theorem kf4_entry {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 21032 (wd ret :: tail) M) (callState s 21036 (wd 2048 :: wd ret :: tail) M) 4 := by
  opt44_reach [10319, 10320]

theorem kf4_back {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ 960) (M : ByteArray) (r : Nat) (hr : r + 64 < 2816) :
    Reach (callState s {pct} (wd r :: wd ret :: tail) M)
      (callState s 21036 (wd (64 + r) :: wd ret :: tail) M) 28 := by
  opt44_reach [{tpath}]

theorem kf4_exit {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ 960) (M : ByteArray) (r : Nat) (hr : r + 64 = 2816)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s {pct} (wd r :: wd ret :: tail) M) (callState s ret tail M) 38 := by
  opt44_reach [{epath}] with [hj]

''' 

HDR = '''theorem {name} {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsz : 2065 ≤ s.activeWords.toNat) (M : ByteArray) (r : Nat) (hr : r ≤ 2784){args} :
    Reach (callState s {pc0} ({stk0}) M)
      (callState s {pc1} ({stk1}) {mem1}) {cost} := by
  opt44_reach [{path}]
    with [{lemmas}]
'''

BASE = 'wd r :: wd ret :: tail'
DSTK = 'd1 :: d2 :: d3 :: d0 :: d4 :: ' + BASE


def block_thm(name, lo, hi, args, stk0, stk1, mem1, lemmas):
    pc0 = ROWS[lo][0]
    pc1 = ROWS[hi][0]
    cost = sum(gas(i) for i in range(lo, hi))
    path = ', '.join(str(i) for i in range(lo, hi))
    return HDR.format(name=name, args=args, pc0=pc0, pc1=pc1, stk0=stk0, stk1=stk1,
                      mem1=mem1, cost=cost, path=path, lemmas=lemmas)


def gen_blocks(rnd):
    src, dst = (0, 0x400) if rnd == 0 else (0x400, 0)
    rca = 'r' if rnd == 0 else '32 + r'
    b = blocks(rnd)
    L = ['''import MlDsaOpt44.Fn.Kf4.Model
/-! Generated by `Kf4/gen_kf4.py`: the straight-line blocks of round %d of `kf4`. -/

namespace MlDsaOpt44.Proofs.Kf4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
''' % (rnd + 1)]
    R = rnd + 1
    cstk = ' :: '.join(f'colM M {src} {x}' for x in (4, 3, 2, 1, 0)) + ' :: ' + BASE
    L.append(block_thm(f'r{R}_cols', *b[0], '', BASE, cstk, 'M',
                       'colM, colC, Ops256, ldY'))
    ds = d_shape()
    dv = {c: f'{ds[c]} Ops256 c{(c + 4) % 5} c{(c + 1) % 5}' for c in range(5)}
    L.append(block_thm(f'r{R}_ds', *b[1], ' (c0 c1 c2 c3 c4 : UInt256)',
                       'c4 :: c3 :: c2 :: c1 :: c0 :: ' + BASE,
                       ' :: '.join(f'({dv[c]})' for c in DORDER) + ' :: ' + BASE, 'M',
                       'dL, dR, Ops256, rot256'))
    for y in range(5):
        rc = f' (ldY M ({rca}))' if y == 0 else ''
        L.append(block_thm(f'r{R}_row{y}', *b[2 + y], ' (d0 d1 d2 d3 d4 : UInt256)', DSTK,
                           DSTK if y < 4 else BASE,
                           f'(row{y} M {src} {dst} d0 d1 d2 d3 d4{rc})',
                           f'row{y}, ch{y}0, ch{y}1, ch{y}2, ch{y}3, ch{y}4, bv, bv0, Ops256, rot256, ldY, stY'))
    if rnd == 1:
        L.append(LOOP.format(pct=ROWS[TAIL][0], pce=ROWS[TAIL + 7][0],
                             tpath=', '.join(str(i) for i in range(TAIL, TAIL + 7)),
                             epath=', '.join(str(i) for i in range(TAIL, TAIL + 9))))
    L.append('end MlDsaOpt44.Proofs.Kf4\n')
    return '\n'.join(L)


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'blocks':
    for rnd in (0, 1):
        open(os.path.join(HERE, f'Blocks{rnd + 1}.lean'), 'w').write(gen_blocks(rnd))


GEN_HDR = '''/-! Generated by `Kf4/gen_kf4.py`. {doc} -/

namespace MlDsaOpt44.Proofs.Kf4

open EvmSemantics
open EvmSemantics.Crypto.Keccak
open MlDsaOptCommon

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
'''


def lanes_of(y, x):
    """[(s, c, r)] of the three B inputs of output (y, x)."""
    return [row_src(y, (x + j) % 5) for j in range(3)]


def gen_hom():
    L = ['import MlDsaOpt44.Fn.Kf4.Il\n' + GEN_HDR.format(
        doc='The chi pieces and the output lanes commute with `W`.')]
    w = L.append
    ops = 'Ops256_xor, Ops256_and, Ops256_or, Ops256_not, Ops64_xor, Ops64_and, Ops64_or, Ops64_not, W_xor, W_and, W_or, W_not'
    for y in range(5):
        for x in range(5):
            rc = (y, x) == (0, 0)
            w(f'theorem ch{y}{x}_W (f0 f1 f2{" frc" if rc else ""} : Nat → UInt64) :\n'
              f'    ch{y}{x} Ops256 (W f0) (W f1) (W f2){" (W frc)" if rc else ""} =\n'
              f'      W fun k => ch{y}{x} Ops64 (f0 k) (f1 k) (f2 k){" (frc k)" if rc else ""} := by\n'
              f'  simp only [ch{y}{x}, {ops}]\n')
    for y in range(5):
        for x in range(5):
            w(f'theorem out{y}{x}_W (g : Fin 25 → Nat → UInt64) (h : Nat → UInt64) :\n'
              f'    out{y}{x} Ops256 (fun i => W (g i)) (W h) = W fun k => out{y}{x} Ops64 (fun i => g i k) (h k) := by\n'
              f'  simp (disch := decide) only [out{y}{x}, dO0, dO1, dO2, dO3, dO4, colC_W, dL_W, dR_W, bv_W, bv0_W, ch{y}{x}_W]\n')
    w('end MlDsaOpt44.Proofs.Kf4\n')
    return '\n'.join(L)


def spec_lane(n):
    y, x = divmod(n, 5)
    bs = []
    for s, c, r in lanes_of(y, x):
        p, q = (c + 4) % 5, (c + 1) % 5
        cp = ' '.join(f'x{p + 5 * k}' for k in range(5))
        cq = ' '.join(f'x{q + 5 * k}' for k in range(5))
        bs.append(f'(bS x{s} (dS (colS {cp}) (colS {cq})) {r})')
    e = f'chiS {" ".join(bs)}'
    return f'({e}) ^^^ rc' if n == 0 else e


def gen_slot():
    chi = chi_data()
    xs = ' '.join(f'x{i}' for i in range(25))
    arr = ', '.join(f'x{i}' for i in range(25))
    L = ['import MlDsaOpt44.Fn.Kf4.Lane\n' + GEN_HDR.format(
        doc='Per slot, the lane-complemented model round is `Keccak.round`.')]
    w = L.append
    bits = ['UInt64.toBitVec_xor', 'UInt64.toBitVec_and', 'UInt64.toBitVec_or',
            'UInt64.toBitVec_not', 'UInt64.toBitVec_zero']
    gbits = ['BitVec.getElem_xor', 'BitVec.getElem_and', 'BitVec.getElem_or',
             'BitVec.getElem_not', 'BitVec.getElem_zero']
    B = lambda b: 'true' if b else 'false'
    for y in range(5):
        for x in range(5):
            t, ms, mo = chi[(y, x)]
            rc = (y, x) == (0, 0)
            rhs = '(chiS b0 b1 b2 ^^^ rc)' if rc else 'chiS b0 b1 b2'
            cases = 'cases b0.toBitVec[i] <;> cases b1.toBitVec[i] <;> cases b2.toBitVec[i]'
            if rc:
                cases += ' <;> cases rc.toBitVec[i]'
            w(f'theorem ch{y}{x}_msk (b0 b1 b2{" rc" if rc else ""} : UInt64) :\n'
              f'    ch{y}{x} Ops64 (b0 ^^^ msk {B(ms[0])}) (b1 ^^^ msk {B(ms[1])}) (b2 ^^^ msk {B(ms[2])}){" rc" if rc else ""} =\n'
              f'      {rhs} ^^^ msk {B(mo)} := by\n'
              f'  simp only [ch{y}{x}, Ops64_xor, Ops64_and, Ops64_or, Ops64_not, chiS, msk, ones_eq]\n'
              f'  apply UInt64.toBitVec_inj.mp\n'
              f'  simp only [{", ".join(bits)}]\n'
              f'  ext i hi\n'
              f'  simp only [{", ".join(gbits)}]\n'
              f'  {cases} <;> rfl\n')
    # round lanes
    w(f'theorem round_lanes ({xs} rc : UInt64) :')
    eqs = [f'    (round #[{arr}] rc)[{n}]! = {spec_lane(n)}' for n in range(25)]
    w(' ∧\n'.join(eqs) + ' := by')
    w('''  simp only [round, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, pure_bind, bind_pure_comp, Id.run_bind, List.range',
      List.foldl, Id.run_map, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceSub, Nat.reduceDiv,
      Array.replicate, List.replicate, Nat.add_zero, Nat.zero_add, map_pure, Array.set!_eq_setIfInBounds,
      List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, List.getElem!_toArray,
      List.getElem!_cons_succ, List.getElem!_cons_zero, rotOff, List.forIn_cons,
      List.forIn_nil, chiS, bS, dS, colS, and_self]
''')
    hs = ', '.join(f'h{n}' for n in range(25))
    aargs = ' '.join(f'A[{i}]!' for i in range(25))
    for y in range(5):
        for x in range(5):
            n = 5 * y + x
            w(f'''theorem slot{y}{x} (A : Array UInt64) (hA : A.size = 25) (rc : UInt64) :
    out{y}{x} Ops64 (fun i => cplU i.val A[i.val]!) rc = cplU {n} (round A rc)[{n}]! := by
  obtain ⟨{hs}⟩ := round_lanes {aargs} rc
  conv_rhs => rw [arr25 hA, h{n}]
  simp only [out{y}{x}, dO0, dO1, dO2, dO3, dO4, cplU, Infra.finVal_lit, cplb, Nat.reduceBEq,
    Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or]
  simp (disch := decide) only [colC_msk, dL_msk, dR_msk, bv_msk, bv0_msk, Bool.xor_false,
    Bool.false_xor, Bool.xor_true, Bool.true_xor, Bool.not_true, Bool.not_false]
  rw [ch{y}{x}_msk]
  simp only [colC_eq, dL_eq, dR_eq, bv_eq, bv0_eq]
''')
    w('end MlDsaOpt44.Proofs.Kf4\n')
    return '\n'.join(L)


def gen_roundmem():
    L = ['import MlDsaOpt44.Fn.Kf4.Model\n' + GEN_HDR.format(
        doc='The words a round stores, as `out` of the words it loads.')]
    w = L.append
    w('''theorem ldY_eq (M : ByteArray) (a : Nat) : ldY M a = UInt256.ofNat (word M a) :=
  readWord_eq_word M a

theorem ldY_stY_same (M : ByteArray) (a : Nat) (v : UInt256) : ldY (stY M a v) a = v := by
  rw [ldY_eq, stY, word_mstore _ _ _ (show v.toNat < 2 ^ 256 from v.val.isLt)]; exact ofNat_toNat v

theorem ldY_stY_ne (M : ByteArray) {a b : Nat} (v : UInt256) (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    ldY (stY M b v) a = ldY M a := by
  rw [ldY_eq, ldY_eq, stY, word_mstore_disjoint _ _ h]

theorem stY_frame (M : ByteArray) {a lo hi : Nat} (v : UInt256) (hlo : lo ≤ a) (hhi : a + 32 ≤ hi) :
    FrameExcept M (stY M a v) [(lo, hi)] :=
  FrameExcept.mono (FrameExcept.mstore M a v.toNat) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨(lo, hi), by simp, hlo, hhi⟩)

theorem frame_trans {m₁ m₂ m₃ : ByteArray} {rs : List (Nat × Nat)}
    (h₁ : FrameExcept m₁ m₂ rs) (h₂ : FrameExcept m₂ m₃ rs) : FrameExcept m₁ m₃ rs :=
  FrameExcept.mono (FrameExcept.trans h₁ h₂) (by
    intro r hr
    exact ⟨r, by simpa using hr, le_rfl, le_rfl⟩)
''')
    dargs = 'd0 d1 d2 d3 d4'
    for y in range(5):
        rc = ' rc' if y == 0 else ''
        rcb = ' (rc : UInt256)' if y == 0 else ''
        w(f'''theorem ldY_row{y} (M : ByteArray) (src dst : Nat) ({dargs} : UInt256){rcb} {{a : Nat}}
    (h : a + 32 ≤ dst + {160 * y} ∨ dst + {160 * y + 160} ≤ a) :
    ldY (row{y} M src dst {dargs}{rc}) a = ldY M a := by
  simp (disch := omega) only [row{y}, ldY_stY_ne]

theorem row{y}_frame (M : ByteArray) (src dst : Nat) ({dargs} : UInt256){rcb} :
    FrameExcept M (row{y} M src dst {dargs}{rc}) [(dst, dst + 800)] := by
  simp only [row{y}]
  repeat (first
    | exact FrameExcept.refl _ _
    | refine frame_trans ?_ (stY_frame _ _ (by omega) (by omega)))
''')
        for x in range(5):
            n = 5 * y + x
            bs = []
            for s, c, r in lanes_of(y, x):
                if r:
                    bs.append(f'(bv Ops256 d{c} (ldY M (src + {32 * s})) {r})')
                else:
                    bs.append(f'(bv0 Ops256 d{c} (ldY M (src + {32 * s})))')
            w(f'''theorem ldY_row{y}_{x} (M : ByteArray) (src dst : Nat) ({dargs} : UInt256){rcb} :
    ldY (row{y} M src dst {dargs}{rc}) (dst + {32 * n}) =
      ch{y}{x} Ops256 {" ".join(bs)}{rc if x == 0 else ""} := by
  simp (disch := omega) only [row{y}, ldY_stY_same, ldY_stY_ne]
''')
    thd = ' '.join(f'(thD{c} M src)' for c in range(5))
    w(f'''def rM1 (M : ByteArray) (src dst rca : Nat) : ByteArray := row0 M src dst {thd} (ldY M rca)
def rM2 (M : ByteArray) (src dst rca : Nat) : ByteArray := row1 (rM1 M src dst rca) src dst {thd}
def rM3 (M : ByteArray) (src dst rca : Nat) : ByteArray := row2 (rM2 M src dst rca) src dst {thd}
def rM4 (M : ByteArray) (src dst rca : Nat) : ByteArray := row3 (rM3 M src dst rca) src dst {thd}

theorem roundM_eq (M : ByteArray) (src dst rca : Nat) :
    roundM M src dst rca = row4 (rM4 M src dst rca) src dst {thd} := rfl

theorem ldY_rM1 (M : ByteArray) (src dst rca : Nat) {{a : Nat}} (h : a + 32 ≤ dst ∨ dst + 160 ≤ a) :
    ldY (rM1 M src dst rca) a = ldY M a := by
  rw [rM1]
  simp (disch := omega) only [ldY_row0]
theorem ldY_rM2 (M : ByteArray) (src dst rca : Nat) {{a : Nat}} (h : a + 32 ≤ dst ∨ dst + 320 ≤ a) :
    ldY (rM2 M src dst rca) a = ldY M a := by
  rw [rM2]
  simp (disch := omega) only [ldY_row1, ldY_rM1]
theorem ldY_rM3 (M : ByteArray) (src dst rca : Nat) {{a : Nat}} (h : a + 32 ≤ dst ∨ dst + 480 ≤ a) :
    ldY (rM3 M src dst rca) a = ldY M a := by
  rw [rM3]
  simp (disch := omega) only [ldY_row2, ldY_rM2]
theorem ldY_rM4 (M : ByteArray) (src dst rca : Nat) {{a : Nat}} (h : a + 32 ≤ dst ∨ dst + 640 ≤ a) :
    ldY (rM4 M src dst rca) a = ldY M a := by
  rw [rM4]
  simp (disch := omega) only [ldY_row3, ldY_rM3]

theorem roundM_frame (M : ByteArray) (src dst rca : Nat) :
    FrameExcept M (roundM M src dst rca) [(dst, dst + 800)] := by
  rw [roundM_eq, rM4, rM3, rM2, rM1]
  exact frame_trans (frame_trans (frame_trans (frame_trans (row0_frame _ _ _ _ _ _ _ _ _)
    (row1_frame _ _ _ _ _ _ _ _)) (row2_frame _ _ _ _ _ _ _ _)) (row3_frame _ _ _ _ _ _ _ _))
    (row4_frame _ _ _ _ _ _ _ _)
''')
    for y in range(5):
        for x in range(5):
            n = 5 * y + x
            steps = ['rw [roundM_eq]']
            for yy in range(4, y, -1):
                steps.append(f'simp (disch := omega) only [ldY_row{yy}]')
                steps.append(f'rw [rM{yy}]')
            steps.append(f'rw [ldY_row{y}_{x}]')
            if y > 0:
                steps.append(f'simp (disch := omega) only [ldY_rM{y}]')
            w(f'''theorem roundM_{n} (M : ByteArray) (src dst rca : Nat) (hsd : src + 800 ≤ dst ∨ dst + 800 ≤ src) :
    ldY (roundM M src dst rca) (dst + {32 * n}) =
      out{y}{x} Ops256 (fun i => ldY M (src + 32 * i.val)) (ldY M rca) := by
  ''' + '\n  '.join(steps) + f'''
  simp only [out{y}{x}, dO0, dO1, dO2, dO3, dO4, thD0, thD1, thD2, thD3, thD4, colM, Infra.finVal_lit,
    Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]
''')
    w('end MlDsaOpt44.Proofs.Kf4\n')
    return '\n'.join(L)


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'math':
    open(os.path.join(HERE, 'Hom.lean'), 'w').write(gen_hom())
    open(os.path.join(HERE, 'Slot.lean'), 'w').write(gen_slot())
    open(os.path.join(HERE, 'RoundMem.lean'), 'w').write(gen_roundmem())
