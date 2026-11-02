"""Generator of the glam ML-DSA-65 / ML-DSA-87 `intt` proofs
(MlDsaOptGlam{65,87}/Fn/Ntt/{Inv1,Inv2,Ctl,Top}.lean).

The inverse part of glam 44's `MlDsaOptGlam44/Fn/Ntt/gen_nttg.py` (the 4 + 4
kernel of `scripts/opt_ntt_glam.py`: 16 words on the stack, block zetas loaded
once, UseHint's wide constants on the stack), with the changes of v4's
`MlDsaOpt65/Fn/NttV4/gen_ntt4p.py`:

* the polynomial address `P` is a parameter of every lemma, so one development
  covers both call sites (`ACC`, `ACC + 0x2000`); the loop bodies take
  `hP : P = ACC ∨ P = ACC + 0x2000`;
* UseHint with `γ2 = 261888`, `m = 16` (`uh6W`, `UHP6`, `uh6_store` of
  `MlDsaOpt65/Fn/NttV4/Lemmas.lean`), read offsets relative to `P`.

Glam 65 and glam 87 run the same `intt` code (both fuse UseHint) at different
pcs; the per-layer lemmas, table records and Shoup constants are glam 44's
(`MlDsaOptGlam44/Fn/Ntt/{Defs,Zeta}.lean`) and v4's.

Run from the repository root: `python3 MlDsaOptGlam65/Fn/Ntt/gen_inttg.py 65|87`
(`uhdef` as a second argument prints the UseHint word).
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.abspath(__file__)) + '/../../..'
sys.path.insert(0, ROOT + '/scripts')

NN = int(sys.argv[1])
assert NN in (65, 87)

from opt_ref import ZETAS  # noqa: E402
from opt_ntt import Kernel  # noqa: E402

L = {}
PC = {}
IDX = {}
for line in open(ROOT + f'/MlDsaOptGlam{NN}/listing.tsv'):
    i, pc, ins = line.rstrip('\n').split('\t')
    if i == 'index':
        continue
    L[int(i)] = ins
    PC[int(i)] = int(pc)
    IDX[int(pc)] = int(i)

LAB = {}
NARG = {}          # pc -> decoded DUPN / SWAPN item
_lines = open(ROOT + f'/MlDsaOpt/{NN}/glam/opt.asm').read().split('\n')
for _k, _l in enumerate(_lines):
    _m = re.match(r'^(\w+):$', _l)
    if _m and _k + 1 < len(_lines):
        LAB[_m.group(1)] = IDX[int(_lines[_k + 1].split()[0])]
        LAB.setdefault(re.sub(r'_\d+$', '', _m.group(1)), LAB[_m.group(1)])
    _m = re.match(r'^\s*(\d+)\s+(DUPN|SWAPN)\s+(\d+)', _l)
    if _m:
        NARG[int(_m.group(1))] = int(_m.group(3))

GAS = {'ADD': 3, 'MUL': 5, 'SUB': 3, 'AND': 3, 'SHR': 3, 'GT': 3, 'ISZERO': 3, 'POP': 2,
       'MLOAD': 3, 'MSTORE': 3, 'JUMP': 8, 'JUMPI': 10, 'JUMPDEST': 1}


def cost(ins):
    op = ins.split()[0]
    if op.startswith('PUSH') or op.startswith('DUP') or op.startswith('SWAP'):
        return 3
    return GAS[op]



OUT = ROOT + f'/MlDsaOptGlam{NN}/Fn/Ntt/'
Q = 8380417
QINV = 0xfc7fdfff
M32 = 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
CINV = 0x04007fa80300000004007fa80300000004007fa80300000004007fa803
MEMWORDS = int(re.search(r'def memWords : Nat := (\d+)',
                         open(ROOT + f'/MlDsaOptGlam{NN}/Infra/Ctx.lean').read()).group(1))
MEMB = 32 * MEMWORDS
ACC, SP, HP = 0xc900, 0x8000, 0x10900
TB = 0x1000


def _uh_consts():
    """UseHint's four wide constants, pushed between the two passes."""
    i = LAB['int2']
    vs = []
    j = i - 1
    while len(vs) < 4:
        if L[j].startswith('PUSH') and int(L[j].split()[1], 16) >= 1 << 64:
            vs.append(int(L[j].split()[1], 16))
        j -= 1
    return list(reversed(vs))


def zm(m):
    return ZETAS[m] * (1 << 32) % Q


# ---------------------------------------------------------------- values
# N: ('lit', n) | ('nv', name) | ('nadd', a, b) | ('nsub', a, b) | ('nop', op, a, b) | ('nshr', v, k)
#    | ('montE', w)
# U: ('var', name) | ('op', op, top, second) | ('montU', t) | ('shU', zs, zt, b) | ('ftA', xa, u)
#    | ('ftB', xa, u) | ('gsA', xa, xb) | ('gsB4', C, xa, xb, z) | ('gsAs', f, xa, xb)
#    | ('uh4', x, s, h)
NK = {'lit', 'nv', 'nadd', 'nsub', 'nop', 'nshr', 'montE'}
OUTK = {'ftA', 'ftB', 'gsA', 'gsB4', 'gsAs'}


def isN(v):
    return v[0] in NK


def lit(n):
    return ('lit', n)


def pn(v):
    """Lean Nat expression of an N value."""
    k = v[0]
    if k == 'lit':
        return str(v[1])
    if k == 'nv':
        return v[1]
    if k == 'nadd':
        return f"({pn(v[1])} + {pn(v[2])})"
    if k == 'nsub':
        return f"({pn(v[1])} - {pn(v[2])})"
    if k == 'nop':
        o = {'mul': '*', 'land': '&&&', 'add': '+'}[v[1]]
        return f"({pn(v[2])} {o} {pn(v[3])})"
    if k == 'montE':
        return f"(montE {pn(v[1])})"
    if k == 'nshr':
        return f"({pn(v[1])} % 2 ^ 256 / 2 ^ {v[2]})"
    raise ValueError(v)


def pu(v):
    """Lean UInt256 expression."""
    if isN(v):
        return f"(UInt256.ofNat {pn(v)})"
    k = v[0]
    if k == 'var':
        return v[1]
    if k == 'montU':
        return f"(montU {pu(v[1])})"
    if k == 'shU':
        return f"(shU {v[1]} {v[2]} {pu(v[3])})"
    if k == 'ftA':
        return f"(ftA {pu(v[1])} {pu(v[2])})"
    if k == 'ftB':
        return f"(ftB {pu(v[1])} {pu(v[2])})"
    if k == 'gsA':
        return f"(gsA {pu(v[1])} {pu(v[2])})"
    if k == 'gsB4':
        return f"(gsB4 {pu(v[1])} {pu(v[2])} {pu(v[3])} {pu(v[4])})"
    if k == 'gsAs':
        return f"(gsAs {pu(v[1])} {pu(v[2])} {pu(v[3])})"
    if k == 'uh4':
        return f"(uh6W {pu(v[1])} {v[2]} {v[3]})"
    if k == 'op':
        o = {'mul': '*', 'add': '+', 'sub': '-'}.get(v[1])
        if o:
            return f"({pu(v[2])} {o} {pu(v[3])})"
        if v[1] == 'land':
            return f"(UInt256.land {pu(v[2])} {pu(v[3])})"
        if v[1] == 'shr':
            return f"(UInt256.shiftRight {pu(v[2])} {pu(v[3])})"
    raise ValueError(v)


def mont_arg(v):
    """If v (U) is the raw Montgomery reduction of t, return t."""
    if v[0] != 'op' or v[1] != 'shr' or v[3] != lit(32):
        return None
    ad = v[2]
    if ad[0] != 'op' or ad[1] != 'add':
        return None
    mu, t = ad[2], ad[3]
    if mu[0] != 'op' or mu[1] != 'mul' or mu[2] != lit(Q):
        return None
    an = mu[3]
    if an[0] != 'op' or an[1] != 'land' or an[2] != lit(M32):
        return None
    mq = an[3]
    if mq[0] != 'op' or mq[1] != 'mul' or mq[2] != lit(QINV):
        return None
    an2 = mq[3]
    if an2[0] != 'op' or an2[1] != 'land' or an2[2] != lit(M32) or an2[3] != t:
        return None
    return t


def montE_arg(v):
    if v[0] != 'nshr' or v[2] != 32:
        return None
    ad = v[1]
    if ad[0] != 'nadd':
        return None
    mu, w = ad[1], ad[2]
    if mu != ('nop', 'mul', lit(Q), ('nop', 'land', lit(M32), ('nop', 'mul', lit(QINV), ('nop', 'land', lit(M32), w)))):
        return None
    return w


def shoup_zs(a, b):
    """`zt * xb − q * (M32 & ((zs * xb) >> 32))` (a = top, b = second): return zs."""
    if not (a[0] == 'op' and a[1] == 'mul' and a[2][0] == 'lit' and a[3][0] == 'var'):
        return None
    if not (b[0] == 'op' and b[1] == 'mul' and b[2] == lit(Q)):
        return None
    an = b[3]
    if not (an[0] == 'op' and an[1] == 'land' and an[2] == lit(M32)):
        return None
    sh = an[3]
    if not (sh[0] == 'op' and sh[1] == 'shr' and sh[3] == lit(32)):
        return None
    mu = sh[2]
    if not (mu[0] == 'op' and mu[1] == 'mul' and mu[2][0] == 'lit' and mu[3] == a[3]):
        return None
    return mu[2][1]


def is_u(v):
    return v[0] in ('montU', 'shU') and (v[0] == 'shU' or (v[1][0] == 'op' and v[1][1] == 'mul'))


def binop(op, a, b):
    """a = top, b = second."""
    if isN(a) and isN(b):
        if a[0] == 'lit' and b[0] == 'lit':
            f = {'add': lambda x, y: x + y, 'mul': lambda x, y: x * y, 'land': lambda x, y: x & y}[op]
            return lit(f(a[1], b[1]) % (1 << 256))
        if op == 'add':
            return ('nadd', a, b)
        return ('nop', op, a, b)
    if op == 'add':
        if is_u(a) and b[0] == 'var':
            return ('ftA', b, a)
        if a[0] == 'var' and b[0] == 'var':
            return ('gsA', b, a)
    return ('op', op, a, b)


def step(i, st, hyps, stores):
    ins = L[i]
    p = ins.split()
    op = p[0]
    if op.startswith('PUSH'):
        st.insert(0, lit(int(p[1], 16)))
    elif op == 'DUPN':
        st.insert(0, st[NARG[PC[i]] - 1])
    elif op == 'SWAPN':
        n = NARG[PC[i]]
        st[0], st[n] = st[n], st[0]
    elif op.startswith('DUP'):
        st.insert(0, st[int(op[3:]) - 1])
    elif op.startswith('SWAP'):
        n = int(op[4:])
        st[0], st[n] = st[n], st[0]
    elif op == 'JUMPDEST':
        pass
    elif op in ('ADD', 'MUL', 'AND'):
        a, b = st.pop(0), st.pop(0)
        st.insert(0, binop({'ADD': 'add', 'MUL': 'mul', 'AND': 'land'}[op], a, b))
    elif op == 'SUB':
        a, b = st.pop(0), st.pop(0)
        r = ('op', 'sub', a, b)
        if a[0] == 'nv' and b[0] == 'lit':
            r = ('nsub', a, b)      # pointer minus offset (discharged from a hypothesis)
        elif a[0] == 'var' and is_u(b):
            r = ('ftB', a, b)
        else:
            zs = shoup_zs(a, b)
            if zs is not None:
                r = ('shU', zs, a[2][1], a[3])
        st.insert(0, r)
    elif op == 'SHR':
        a, b = st.pop(0), st.pop(0)
        if isN(a) and isN(b):
            r = ('nshr', b, a[1])
            w = montE_arg(r)
            if w is not None:
                r = ('montE', w)
        else:
            r = ('op', 'shr', b, a)
            t = mont_arg(r)
            if t is not None:
                r = ('montU', t)
                if t[0] == 'op' and t[1] == 'mul':
                    z, d = t[2], t[3]
                    if (d[0] == 'op' and d[1] == 'add' and d[2][0] == 'op' and d[2][1] == 'sub'
                            and isN(d[2][2]) and d[2][3][0] == 'var' and d[3][0] == 'var'):
                        r = ('gsB4', d[2][2], d[2][3], d[3], z)
                    elif d[0] == 'gsA':
                        r = ('gsAs', z, d[1], d[2])
        st.insert(0, r)
    elif op == 'MLOAD':
        a = st.pop(0)
        key = pn(a)
        if key in hyps:
            st.insert(0, ('nv', hyps[key]))
        else:
            raise ValueError(f"unmapped MLOAD at {i}: {key}")
    elif op == 'MSTORE':
        a, v = st.pop(0), st.pop(0)
        stores.append((a, v))
    elif op == 'POP':
        st.pop(0)
    else:
        raise ValueError(f"control op {op} at {i}")


def emulate(start, end, stack, hyps):
    """stack top first. hyps: map Lean address string -> N value name for MLOAD.
    Returns (indices, cost, stack, stores)."""
    st = list(stack)
    idx, c, stores = [], 0, []
    for i in range(start, end):
        idx.append(i)
        c += cost(L[i])
        step(i, st, hyps, stores)
    return idx, c, st, stores


def u_b(u):
    """The multiplied operand of a forward `u`."""
    return u[3] if u[0] == 'shU' else u[1][3]


def slot_of(v):
    k = v[0]
    if k == 'ftA':
        return v[1][1]
    if k == 'ftB':
        return u_b(v[2])[1]
    if k == 'gsA':
        return v[1][1]
    if k == 'gsB4':
        return v[3][1]
    if k == 'gsAs':
        return v[2][1]
    raise ValueError(v)


def bfly_of(v):
    k = v[0]
    if k in ('ftA', 'ftB'):
        xa = v[1][1]
        u = v[2]
        if u[0] == 'shU':
            return ('cts', xa, u[3][1], (u[1], u[2]))
        return ('ctm', xa, u[1][3][1], u[1][2])
    if k == 'gsA':
        return None
    if k == 'gsB4':
        return ('gs', v[2][1], v[3][1], v[4])
    if k == 'gsAs':
        return ('gsS', v[2][1], v[3][1], v[1])
    raise ValueError(v)


def is_bout(v):
    return v[0] in ('ftB', 'gsB4')


def stack_text(st):
    return ' :: '.join(pu(v) for v in st)



UHC = _uh_consts()

HDR = f"""import MlDsaOptGlam44.Fn.Ntt.Zeta
import MlDsaOpt65.Fn.NttV4.Lemmas
import MlDsaOptGlam{NN}.Layout
/-! Generated by `MlDsaOptGlam65/Fn/Ntt/gen_inttg.py {NN}` (glam `intt`, MlDsaOpt/{NN}/glam/opt.asm): {{title}}. -/

namespace MlDsaOptGlam{NN}.Proofs.NttG

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.Ntt4 MlDsaOpt65.Proofs.Ntt6
open MlDsaOptGlam44.Proofs.NttG
open MlDsaOptGlam{NN}.Proofs MlDsaOptGlam{NN}.Proofs.Infra

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
"""

SIMP_DEFS = "montU, shU, ftA, ftB, gsA, gsB4, gsAs, uh6W, uF6, uV6, uD6, uY, uQ, uX, wrU, montE"
HTAIL = "950"


def block_lemma(name, start, end, pre, hyps_map, nat_params, uint_params, hyps, extra_simp, mem_ops,
                post_override=None, mem_params='(mem : ByteArray)', pre_tac=''):
    idx, c, post, stores = emulate(start, end, pre, hyps_map)
    if post_override:
        post, stores = post_override(post, stores)
    pc0, pc1 = PC[start], PC[end]
    mem_post = 'mem'
    for a, v in stores:
        mem_post = f"(wrU {mem_post} {pn(a)} {pu(v)})"
    params = ''
    if nat_params:
        params += f" ({' '.join(nat_params)} : Nat)"
    if uint_params:
        params += f" ({' '.join(uint_params)} : UInt256)"
    hs_ = ''.join(f"\n    ({h})" for h in hyps)
    simp = ', '.join([SIMP_DEFS] + extra_simp)
    txt = f"""
theorem {name} {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ {HTAIL})
    {mem_params}{params}{hs_} :
    Reach (callState s {pc0} ({stack_text(pre)} :: tail) mem)
      (callState s {pc1} ({stack_text(post)} :: tail) {mem_post}) {c} := by
"""
    txt += pre_tac
    if mem_ops:
        txt += "  have hmw := hs.sized; unfold memWords at hmw\n"
    txt += f"  glam{NN}_rreach [{', '.join(map(str, idx))}] with [{simp}]\n"
    return txt, post, c, stores


# zeta record u of a block: width w, group g; m = 16 w + b w + g
def wg(u):
    w = 1 if u < 1 else 2 if u < 3 else 4 if u < 7 else 8
    return w, u + 1 - w


def m_expr(u, b):
    w, g = wg(u)
    return f"{16 * w} + {w} * {b} + {g}"


def rec_val(b, u):
    return f"nttRecG (15 * {b} + {u})"


IMM_M = {}
for _m in range(1, 256):
    IMM_M.setdefault(zm(_m), _m)
SHOUP_M = {(Kernel.shoup(m), ZETAS[m]): m for m in range(1, 16)}

CIN = lit(CINV)
M32N = lit(M32)

INV_ST = lambda X: [('nv', 'pj'), ('nv', X), CIN, M32N, ('nv', 'P'), ('nv', 'ret')]
INV2_ST = lambda X: [('nv', 'pj'), ('nv', X)] + [lit(v) for v in reversed(UHC)] + [CIN, M32N, ('nv', 'P'), ('nv', 'ret')]

PASSES = [
    dict(name='ivA', file='Inv1', title='inverse pass 1 (layers 1-4, premont, block zetas)', head='int1',
         nw=16, nz=15, off=32, P='P', X='zb', Xn='11296 - 480 * n', ctl=INV_ST, premont=True, tbl=True,
         rb='(15 - n)', L0=0, n='n', pj='P + 512 * n', slot='16 * n + {i}',
         D='t / 16 < {n}', S='t / 16 = n', dec='⟨t % 16, by omega⟩', model='inv',
         Pre='(fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))',
         Post='(fun t w => LOK (UInt256.ofNat w) (Bi 4) (fun k => invL (scaleR h k) 4 t))'),
    dict(name='ivB', file='Inv2', title='inverse pass 2 (layers 5-8, scaling, UseHint)', head='int2',
         nw=16, nz=0, off=512, P='P', X='e', Xn='512 + P', ctl=INV2_ST, premont=False, tbl=False, L0=4,
         n='c', pj='P + 32 * c', slot='c + 16 * {i}',
         D='t % 16 < {n}', S='t % 16 = c', dec='⟨t / 16, by omega⟩', model='inv',
         Pre='(fun t w => LOK (UInt256.ofNat w) (Bi 4) (fun k => invL (scaleR h k) 4 t))',
         Post='(fun t w => UHP6 m0 P t w (fun k => Sc * invL (scaleR h k) 8 t))'),
]
PASS = {p['name']: p for p in PASSES}


class AnyZ(dict):
    def __contains__(self, key):
        return True

    def __getitem__(self, key):
        return 'zz'


def layer_end(start, nw, cur):
    st = list(cur)
    done = 0
    i = start
    while True:
        step(i, st, AnyZ(), [])
        i += 1
        if st and is_bout(st[0]):
            done += 1
            if done == nw // 2:
                return i


def to_vars(post):
    return [('var', f"x{int(slot_of(v)[1:])}") if v[0] in OUTK else v for v in post]


def layer_ends(start, nw, nlayers, cur):
    ends = []
    for _ in range(nlayers):
        e = layer_end(start, nw, cur)
        ends.append(e)
        _, _, post, _ = emulate(start, e, cur, AnyZ())
        cur = to_vars(post)
        start = e
    return ends


def xs_of(st):
    return [v[1] for v in st if v[0] == 'var']


def gen_blocks(ps):
    name, nw, off, P, nz = ps['name'], ps['nw'], ps['off'], ps['P'], ps['nz']
    ctl = ps['ctl'](ps['X'])
    out = ''
    head = LAB[ps['head']]
    k, i = 0, head
    while k < nw + nz:
        if L[i] == 'MLOAD':
            k += 1
        i += 1
    load_end = i + (12 if ps['premont'] and nz == 0 else 0)
    addrs = ['pj'] + [f"({off * j} + pj)" for j in range(1, nw)]
    hmap = {a: f"w{j}" for j, a in enumerate(addrs)}
    zaddrs = ['zb'] + [f"({32 * u} + zb)" for u in range(1, nz)]
    hmap.update({a: f"z{u}" for u, a in enumerate(zaddrs)})
    hyps = [f"hpj : pj + {off * (nw - 1) + 32} ≤ {MEMB}"] + [f"hw{j} : word mem {a} = w{j}" for j, a in enumerate(addrs)]
    nps = ['pj', ps['X'], 'ret', 'P'] + [f"w{j}" for j in range(nw)]
    simp = [f"hw{j}" for j in range(nw)]
    if nz:
        hyps += [f"hzb : zb + {32 * nz} ≤ {MEMB}"] + [f"hz{u} : word mem {a} = z{u}" for u, a in enumerate(zaddrs)]
        nps += [f"z{u}" for u in range(nz)]
        simp += [f"hz{u}" for u in range(nz)]
    txt, post, cld, _ = block_lemma(f"{name}_ld", head, load_end, ctl, hmap, nps, [], hyps, simp, True)
    out += txt
    costs = [cld]

    def slot_load(v):
        if v[0] == 'nv' and v[1][0] == 'w':
            return int(v[1][1:])
        if v[0] == 'montE':
            return int(v[1][1][1:])
        return None

    cur = [('var', f"x{slot_load(v)}") if slot_load(v) is not None else v for v in post]
    zps = [f"z{u}" for u in range(nz)]
    ends = layer_ends(load_end, nw, 4, cur)
    layers = []
    start = load_end
    for li, e in enumerate(ends):
        txt, post, cl, _ = block_lemma(f"{name}_l{li + 1}", start, e, cur, {},
                                       ['pj', ps['X'], 'ret', 'P'] + zps, sorted(xs_of(cur), key=lambda s: int(s[1:])),
                                       [], [], False)
        out += txt
        costs.append(cl)
        bfs = []
        for v in post:
            if v[0] not in OUTK:
                continue
            bf = bfly_of(v)
            if bf is None:
                continue
            prev = [j for j, b in enumerate(bfs) if (b[1], b[2]) == (bf[1], bf[2])]
            if not prev:
                bfs.append(bf)
            elif bf[0] == 'gsS':
                bfs[prev[0]] = bf
        assert len(bfs) == nw // 2, (name, li, bfs)
        layers.append(bfs)
        cur = to_vars(post)
        start = e
    uh = name == 'ivB'
    sthyp = [f"hpj : pj + {off * (nw - 1) + 32} ≤ {MEMB}"]
    st_blocks = []
    if not uh:
        # up to the 16th MSTORE with only the control words left
        st = list(cur)
        i, ns = start, 0
        while not (ns == nw and len(st) == len(ctl)):
            stores = []
            step(i, st, {}, stores)
            ns += len(stores)
            i += 1
        ctl_i = i
        txt, post, cst, stores = block_lemma(f"{name}_st", start, ctl_i, cur, {},
                                             ['pj', ps['X'], 'ret', 'P'] + zps,
                                             sorted(xs_of(cur), key=lambda s: int(s[1:])),
                                             sthyp, [], True)
        assert post == ctl, post
        out += txt
        costs.append(cst)
        st_blocks.append((f"{name}_st", stores, []))
    else:
        s0 = start
        rest = list(cur)
        for j in range(nw):
            e = s0
            while L[e] != 'MSTORE':
                e += 1
            e += 1
            x = rest[0]
            xi = int(x[1][1:])
            soff = ACC - SP - off * xi
            hoff = HP - ACC + off * xi
            skey = f"(pj - {soff})"
            hkey = f"({hoff} + pj)"
            hm = {skey: 'sv', hkey: 'hv'}
            tmpl = _subst(UH_TEMPLATE, x)

            def override(post, stores, tmpl=tmpl, x=x):
                assert len(stores) == 1 and stores[0][1] == tmpl, (stores, tmpl)
                return post, [(stores[0][0], ('uh4', x, 'sv', 'hv'))]
            vs = sorted(xs_of(rest), key=lambda s: int(s[1:]))
            hy = [f"hpj : pj + {HP - ACC + off * (nw - 1) + 32} ≤ {MEMB}", f"hpj0 : {soff} ≤ pj",
                  "hpA : P ≤ pj", "hpB : pj < P + 512",
                  "hF : FrameExcept M0 mem [(P, P + 8192)]",
                  f"hsv0 : word M0 (pj - {soff}) = sv", f"hhv0 : word M0 ({hoff} + pj) = hv"]
            ptac = (f"  have hsv : word mem (pj - {soff}) = sv := (FrameExcept.word hF (by\n"
                    f"    simp only [avoids_cons, avoids_nil, and_true]; omega)).trans hsv0\n"
                    f"  have hhv : word mem ({hoff} + pj) = hv := (FrameExcept.word hF (by\n"
                    f"    simp only [avoids_cons, avoids_nil, and_true]; omega)).trans hhv0\n")
            txt, post, cst, stores = block_lemma(f"{name}_st{j}", s0, e, rest, hm,
                                                 ['pj', ps['X'], 'ret', 'P', 'sv', 'hv'], vs, hy,
                                                 ['hsv', 'hhv'], True, override,
                                                 '(mem M0 : ByteArray)', ptac)
            out += txt
            costs.append(cst)
            st_blocks.append((f"{name}_st{j}", stores, [x, soff, hoff, vs]))
            rest = post
            s0 = e
        assert rest == ctl, rest
        ctl_i = s0
    return out, layers, costs, st_blocks, ctl_i


def _subst(t, x):
    if t == ('var', 'X'):
        return x
    if isinstance(t, tuple):
        return tuple(_subst(a, x) for a in t)
    return t


def _uh_template():
    ps = PASS['ivB']
    head = LAB[ps['head']]
    k, i = 0, head
    while k < 16:
        if L[i] == 'MLOAD':
            k += 1
        i += 1
    cur = [('var', f"x{j}") for j in range(16)] + INV2_ST('e')
    ends = layer_ends(i, 16, 4, cur)
    _, _, post, _ = emulate(i, ends[-1], cur, AnyZ())
    stk = to_vars(post)
    stk[0] = ('var', 'X')
    s0 = ends[-1]
    e = s0
    while L[e] != 'MSTORE':
        e += 1

    class Any(dict):
        def __contains__(self, key):
            return True

        def __getitem__(self, key):
            return 'sv' if '-' in key else 'hv'
    _, _, post, stores = emulate(s0, e + 1, stk, Any())
    assert len(stores) == 1
    return stores[0][1]


UH_TEMPLATE = _uh_template()


def uh_def():
    t = UH_TEMPLATE
    return pu(t).replace('(UInt256.ofNat sv)', '(UInt256.ofNat s)').replace('(UInt256.ofNat hv)', '(UInt256.ofNat h)') \
        .replace(' X', ' x').replace('(X ', '(x ')


CIT = str(CINV)
M32T = str(M32)


def head_stack(ps, pjexpr, Xexpr):
    if ps['model'] == 'fwd':
        return (f"UInt256.ofNat ({pjexpr}) :: UInt256.ofNat ({Xexpr}) :: "
                f"UInt256.ofNat {M32T} :: UInt256.ofNat {ps['P']} :: UInt256.ofNat ret :: tail")
    mid = ''
    if ps['name'] == 'ivB':
        mid = ''.join(f"UInt256.ofNat {v} :: " for v in reversed(UHC))
    return (f"UInt256.ofNat ({pjexpr}) :: UInt256.ofNat ({Xexpr}) :: {mid}UInt256.ofNat {CIT} :: "
            f"UInt256.ofNat {M32T} :: UInt256.ofNat {ps['P']} :: UInt256.ofNat ret :: tail")


def gen_body(ps, layers, costs, st_blocks, ctl_i):
    name, nw, off, P, nz = ps['name'], ps['nw'], ps['off'], ps['P'], ps['nz']
    n = ps['n']
    slot = lambda i: ps['slot'].format(i=i)
    D0 = ps['D'].format(n=n)
    D1 = ps['D'].format(n=f"{n} + 1")
    hb = f"(h{n} : {n} < 16)"
    tbl = " (htbl : TblAt M)" if ps['tbl'] else ""
    uh = ps['name'] == 'ivB'
    inv = f"PI M {P} (fun t => {{D}}) {ps['Pre']} {ps['Post']}"
    hs = head_stack(ps, ps['pj'], ps['Xn'])
    cost = sum(costs)
    extra = ''
    if uh:
        extra = (f"\n    (m0 : ByteArray) (hF : FrameExcept m0 M [({P}, {P} + 8192)])"
                 f"\n    (hSH : H → ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (P - {ACC - SP} + 32 * t)) r ≤ 128 * 8380417 + 261888 - 1 ∧"
                 f"\n      lane (word m0 (P + {HP - ACC} + 32 * t)) r ≤ 1)")
    out = f"""
theorem {name}_body {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ {HTAIL})
    (ret : Nat) (P : Nat) (hPv : P = {ACC} ∨ P = {ACC + 0x2000}) (H : Prop) (h : Nat → Nat → F) ({n} : Nat) {hb}
    (M : ByteArray){tbl}{extra}
    (hP : H → {inv.format(D=D0)}) :
    ∃ M', (H → {inv.format(D=D1).replace('PI M ', "PI M' ")}) ∧
      FrameExcept M M' [({P}, {P} + 8192)] ∧
      Reach (callState s {PC[LAB[ps['head']]]} ({hs}) M)
        (callState s {PC[ctl_i]} ({hs}) M') {cost} := by
"""
    pj, X = ps['pj'], ps['Xn']
    ws = ' '.join(f"(word M ({P} + 32 * ({slot(i)})))" for i in range(nw))
    hws = ' '.join("(congrArg (word M) (by omega))" for i in range(nw))
    if nz:
        zv = ' '.join(f"({rec_val(ps['rb'], u)})" for u in range(nz))
        hz = ' '.join(f"(by rw [← htbl (15 * {ps['rb']} + {u}) (by omega)]; congr 1; unfold MlDsaOpt44.Proofs.TBL; omega)"
                      for u in range(nz))
        parts = [f"({name}_ld hs htail M ({pj}) ({X}) ret P {ws} {zv} (by omega) {hws} (by omega) {hz})"]
    else:
        parts = [f"({name}_ld hs htail M ({pj}) ({X}) ret P {ws} (by omega) {hws})"]
    zsl = ' '.join('_' for _ in range(nz))
    for li in range(len(layers)):
        xs = ' '.join('_' for _ in range(nw))
        parts.append(f"({name}_l{li + 1} hs htail M ({pj}) ({X}) ret P {zsl} {xs})")
    if not uh:
        xs = ' '.join('_' for _ in range(nw))
        parts.append(f"({name}_st hs htail M ({pj}) ({X}) ret P {zsl} {xs} (by omega))")
    else:
        for j, (bn, stores, (x, soff, hoff, vs)) in enumerate(st_blocks):
            xi = int(x[1][1:])
            sv = f"(word M (P - {ACC - SP} + 32 * ({slot(xi)})))"
            hv = f"(word M (P + {HP - ACC} + 32 * ({slot(xi)})))"
            xs = ' '.join('_' for _ in vs)
            parts.append(f"({bn} hs htail _ M ({pj}) ({X}) ret P {sv} {hv} {xs} (by omega) (by omega) "
                         f"(by omega) (by omega)\n      (by repeat (first | exact FrameExcept.refl _ _ | "
                         f"refine frame_wrU _ ?_ (by omega) (by omega)))\n"
                         f"      (congrArg (word M) (by omega)) (congrArg (word M) (by omega)))")
    r = parts[-1]
    for p in reversed(parts[:-1]):
        r = f"({p}.trans\n    {r})"
    out += f"  have hR := {r}\n"
    out += "  refine ⟨_, fun hH => ?sem, ?frm, hR.mono (by norm_num)⟩\n"
    out += "  case frm =>\n    repeat (first | exact FrameExcept.refl _ _ | refine frame_wrU _ ?_ (by omega) (by omega))\n"
    out += "  case sem =>\n    have hI := hP hH\n"
    for i in range(nw):
        f = f"passInvG_pre hI (t := {slot(i)}) (by omega) (by omega)"
        if ps['premont']:
            f = f"premont_step h ({slot(i)}) _ (({f}).mono (by norm_num))"
        out += f"    have v0_{i} := {f}\n"
    for li, bfs in enumerate(layers):
        Lr = ps['L0'] + li
        for (kind, a, b, z) in bfs:
            a, b = int(a[1:]), int(b[1:])
            ia, ib = slot(a), slot(b)
            if kind == 'gsS':
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := gsS4_step (scaleR h) ({ia}) ({ib}) (by omega) "
                        f"(by omega) v{li}_{a} v{li}_{b}\n")
                continue
            if kind == 'cts':
                zs, zt = z
                m = SHOUP_M[(zs, zt)]
                ln = 128 >> Lr
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := ct4s_step h {Lr} {ln} ({ia}) ({ib}) {m} "
                        f"(by norm_num) (by norm_num) (by omega) (by omega) (by omega) shoupG{m} "
                        f"v{li}_{a} v{li}_{b}\n")
                continue
            if z[0] == 'lit':
                m = IMM_M[z[1]]
                mexpr, zexpr, hz = str(m), str(z[1]), f"zmiG{m}.symm"
            else:
                u = int(z[1][1:])
                mexpr = m_expr(u, ps['rb'])
                zexpr = rec_val(ps['rb'], u)
                hz = f"(recG{u} {ps['rb']})"
            if ps['model'] == 'fwd':
                ln = 128 >> Lr
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := ct4m_step h {Lr} {ln} ({ia}) ({ib}) ({mexpr}) "
                        f"({zexpr}) (by norm_num) (by norm_num) (by omega) (by omega) (by omega) {hz} "
                        f"v{li}_{a} v{li}_{b}\n")
            else:
                ln = 1 << Lr
                m0 = 1 << (8 - Lr)
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := gs4_step (scaleR h) {Lr} {ln} {m0} ({ia}) ({ib}) "
                        f"({mexpr}) ({zexpr}) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) "
                        f"(by omega) {hz} v{li}_{a} v{li}_{b}\n")
    nl = len(layers)
    S = ps['S']
    if uh:
        for i in range(nw):
            out += (f"    have u_{i} := uh6_store (hSH hH) hF (by omega) (t := {slot(i)}) (by omega) v{nl}_{i}\n")
    out += f"""    refine passInvG_store hI (S := fun t => {S}) (fun t => by omega) ?new ?old
    case old =>
      intro t ht hS
      simp (disch := omega) only [word_wrU, if_neg]
    case new =>
      intro t ht hS
      obtain ⟨i, rfl⟩ : ∃ i, t = {slot('i')} := {ps['dec']}
      have hi : i < {nw} := by omega
      rw [show {P} + 32 * ({slot('i')}) =
        {off} * i + ({pj}) by omega]
      interval_cases i
"""
    fin = 'u' if uh else f"v{nl}"
    for i in range(nw):
        out += (f"      · simp (disch := with_unfolding_all rfl) only [word_wrU_add_eq, word_wrU_add_ne, "
                f"word_wrU_base_eq, word_wrU_base_ne, ofNat_toNat]; exact {fin}_{i}\n")
    return out


def gen_file(ps):
    blocks, layers, costs, st_blocks, ctl_i = gen_blocks(ps)
    out = HDR.format(title=ps['title'])
    out += blocks
    out += gen_body(ps, layers, costs, st_blocks, ctl_i)
    return out, costs, ctl_i


CU = ' :: '.join(f"cU{3 - j}" for j in range(4))
NOTES = (f'local notation "cM" => UInt256.ofNat {M32}\n'
         f'local notation "cCI" => UInt256.ofNat {CINV}\n' +
         ''.join(f'local notation "cU{j}" => UInt256.ofNat {v}\n' for j, v in enumerate(UHC)))


def I1(pj, X):
    return f"UInt256.ofNat {pj} :: UInt256.ofNat {X} :: cCI :: cM :: UInt256.ofNat P :: UInt256.ofNat ret :: tail"


def I2(pj, X):
    return (f"UInt256.ofNat {pj} :: UInt256.ofNat {X} :: {CU} :: cCI :: cM :: UInt256.ofNat P :: "
            f"UInt256.ofNat ret :: tail")


def gen_ctl(ctl):
    hj = f'hj : Decode.isValidJumpDest MlDsaOptGlam{NN}.optBytecode ret = true'
    items = [
        ('i_pro', LAB['intt'], 5, '', [], "UInt256.ofNat P :: UInt256.ofNat ret :: tail", LAB['int1'],
         I1('P', '11296'), []),
        ('ivA_cont', ctl['ivA'], 13, ' (pj zb : Nat)', ['hpj : pj < 70000', 'hzb : zb < 70000', 'h480 : 480 ≤ zb',
                                                        'hz : 4096 ≤ zb - 480'], I1('pj', 'zb'),
         LAB['int1'], I1('(512 + pj)', '(zb - 480)'), []),
        ('ivA_exit', ctl['ivA'], 23, ' (pj zb : Nat)', ['hpj : pj < 70000', 'hzb : zb < 70000', 'h480 : 480 ≤ zb',
                                                        'hz : zb - 480 < 4096'], I1('pj', 'zb'),
         LAB['int2'], I2('P', '(512 + P)'), []),
        ('ivB_cont', ctl['ivB'], 7, ' (pj : Nat)', ['hpj : 32 + pj < 512 + P'], I2('pj', '(512 + P)'),
         LAB['int2'], I2('(32 + pj)', '(512 + P)'), []),
        ('ivB_exit', ctl['ivB'], 17, ' (pj : Nat)', ['hpj : 32 + pj = 512 + P', hj, 'hret : ret < 2 ^ 16'],
         I2('pj', '(512 + P)'), 'ret', 'tail', ['hj']),
    ]
    out = f"""import MlDsaOptGlam44.Fn.Ntt.Zeta
import MlDsaOptGlam{NN}.Layout
/-! Generated by `MlDsaOptGlam65/Fn/Ntt/gen_inttg.py {NN}`: prologue, loop control and exits of the
glam `intt` (MlDsaOpt/{NN}/glam/opt.asm), for a polynomial address `P`. -/

namespace MlDsaOptGlam{NN}.Proofs.NttG

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOptGlam{NN}.Proofs MlDsaOptGlam{NN}.Proofs.Infra

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

{NOTES}
section
variable {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ {HTAIL}) (mem : ByteArray)
  (ret P : Nat) (hP : P < 70000)
include hs htail hP
"""
    costs = {}
    for (nm, st, ln, params, hyps, pre, tgt, post, extra) in items:
        idx = list(range(st, st + ln))
        last = L[idx[-1]].split()[0]
        if tgt == 'ret':
            assert last == 'JUMP', (nm, last)
            pcpost = 'ret'
        else:
            assert last == 'JUMPI' or idx[-1] + 1 == tgt, (nm, last)
            pcpost = str(PC[tgt])
        c = sum(cost(L[i]) for i in idx)
        costs[nm] = c
        hs_ = ''.join(f" ({h})" for h in hyps)
        w = f" with [{', '.join(extra)}]" if extra else ''
        out += f"""
theorem {nm}{params}{hs_} :
    Reach (callState s {PC[st]} ({pre}) mem)
      (callState s {pcpost} ({post}) mem) {c} := by
  glam{NN}_rreach [{', '.join(map(str, idx))}]{w}
"""
    out += f"\nend\n\nend MlDsaOptGlam{NN}.Proofs.NttG\n"
    open(OUT + 'Ctl.lean', 'w').write(out)
    return costs


TOP = r'''import MlDsaOptGlam{NN}.Fn.Ntt.Inv1
import MlDsaOptGlam{NN}.Fn.Ntt.Inv2
import MlDsaOptGlam{NN}.Fn.Ntt.Ctl
import MlDsaOptGlam{NN}.Budget
import MlDsa.Bridge44
/-! Generated by `MlDsaOptGlam65/Fn/Ntt/gen_inttg.py {NN}`: the two loops of the glam `intt`
(MlDsaOpt/{NN}/glam/opt.asm) for a polynomial address `P` (each iterates its loop body with the back
edge, `reach_iterF`, then the last body and the exit), and `intt` end to end with UseHint fused
(`γ2 = 261888`), as v4's `MlDsaOpt65/Fn/NttV4/Top.lean` `intt_v4`. -/

namespace MlDsaOptGlam{NN}.Proofs.NttG

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.Ntt4 MlDsaOpt65.Proofs.Ntt6
open MlDsaOpt65.Proofs.NttV4 (uh6L_spec useHint_emod6)
open MlDsaOptGlam44.Proofs.NttG
open MlDsaOptGlam{NN}.Proofs MlDsaOptGlam{NN}.Proofs.Infra

set_option maxHeartbeats 0
set_option maxRecDepth 100000

{NOTES}
local notation "IP" h:max B:max L:max => fun t w => LOK (UInt256.ofNat w) B (fun k => invL (scaleR h k) L t)

section
variable {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ {HTAIL}) (ret : Nat)
  (H : Prop) (h : Nat → Nat → F)
include hs htail

theorem ivA_pass (P : Nat) (hPv : P = {A0} ∨ P = {A1}) (M0 : ByteArray) (htbl : TblAt M0)
    (hP0 : H → PI M0 P (fun t => t / 16 < 0) (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (IP h (Bi 4) 4)) :
    ∃ M', (H → PI M' P (fun t => t / 16 < 16)
        (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t)) (IP h (Bi 4) 4)) ∧
      FrameExcept M0 M' [(P, P + 8192)] ∧
      Reach (callState s {h1} ({I1P}) M0) (callState s {h2} ({I2P}) M') {cA} := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun n M => callState s {h1} (UInt256.ofNat (P + 512 * n) ::
      UInt256.ofNat (11296 - 480 * n) :: cCI :: cM :: UInt256.ofNat P :: UInt256.ofNat ret :: tail) M)
    (Q := fun n M => (H → PI M P (fun t => t / 16 < n)
        (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t)) (IP h (Bi 4) 4)) ∧
      FrameExcept M0 M [(P, P + 8192)])
    (c := fun _ => {bA} + {cAc}) 15 (fun n M hn hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := ivA_body hs htail ret P hPv H h n (by omega) M
        (tblG_frame htbl hQ.2 (by omega)) hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post2 (hR'.trans (ivA_cont hs htail M' ret P (by omega) _ _ (by omega) (by omega) (by omega)
          (by omega))) (by omega) (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := ivA_body hs htail ret P hPv H h 15 (by norm_num) M1
    (tblG_frame htbl hF1 (by omega)) hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (ivA_exit hs htail M2 ret P (by omega) _ _ (by omega) (by norm_num) (by norm_num)
      (by norm_num))).mono (by simp only [costSum]; norm_num)⟩

theorem ivB_pass (P : Nat) (hPv : P = {A0} ∨ P = {A1}) (M0 m0 : ByteArray)
    (hF0 : FrameExcept m0 M0 [(P, P + 8192)])
    (hSH : H → ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (P - 18688 + 32 * t)) r ≤ 128 * 8380417 + 261888 - 1 ∧
      lane (word m0 (P + 16384 + 32 * t)) r ≤ 1)
    (hj : Decode.isValidJumpDest MlDsaOptGlam{NN}.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hP0 : H → PI M0 P (fun t => t % 16 < 0) (IP h (Bi 4) 4)
      (fun t w => UHP6 m0 P t w (fun k => Sc * invL (scaleR h k) 8 t))) :
    ∃ M', (H → PI M' P (fun t => t % 16 < 16) (IP h (Bi 4) 4)
        (fun t w => UHP6 m0 P t w (fun k => Sc * invL (scaleR h k) 8 t))) ∧
      FrameExcept M0 M' [(P, P + 8192)] ∧
      Reach (callState s {h2} ({I2P}) M0) (callState s ret tail M') {cB} := by
  obtain ⟨M1, ⟨hP1, hF1⟩, hR1⟩ := reach_iterF
    (S := fun c M => callState s {h2} (UInt256.ofNat (P + 32 * c) :: UInt256.ofNat (512 + P) ::
      {CU} :: cCI :: cM :: UInt256.ofNat P :: UInt256.ofNat ret :: tail) M)
    (Q := fun c M => (H → PI M P (fun t => t % 16 < c) (IP h (Bi 4) 4)
        (fun t w => UHP6 m0 P t w (fun k => Sc * invL (scaleR h k) 8 t))) ∧
      FrameExcept M0 M [(P, P + 8192)])
    (c := fun _ => {bB} + {cBc}) 15 (fun c M hc hQ => by
      obtain ⟨M', hP', hF', hR'⟩ := ivB_body hs htail ret P hPv H h c (by omega) M m0
        (frame_trans1 hF0 hQ.2) hSH hQ.1
      exact ⟨M', ⟨hP', frame_trans1 hQ.2 hF'⟩,
        reach_post1 (hR'.trans (ivB_cont hs htail M' ret P (by omega) (P + 32 * c) (by omega)))
          (by omega)⟩)
    M0 ⟨hP0, FrameExcept.refl _ _⟩
  obtain ⟨M2, hP2, hF2, hR2⟩ := ivB_body hs htail ret P hPv H h 15 (by norm_num) M1 m0
    (frame_trans1 hF0 hF1) hSH hP1
  exact ⟨M2, hP2, frame_trans1 hF1 hF2,
    ((hR1.trans hR2).trans (ivB_exit hs htail M2 ret P (by omega) (P + 32 * 15) (by omega) hj hret)).mono
      (by simp only [costSum]; norm_num)⟩

end

theorem intt_g {{s : State}} (hs : Ctx s) {{g : Nat}} (hg : g < 2) {{ret : Nat}} {{tail : List UInt256}}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) →
        (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 0x2000 * g + 32 * t)) r ≤ spOff ∧
          lane (word m (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r =
          (MlDsa.Fips204.useHint MlDsaOpt{NN}.Proofs.P (lane (word m (HP + 0x2000 * g + 32 * t)) r)
            ((MlDsa.Fips204.nttInv (lanesPoly m (ACC + 0x2000 * g) r))[t]! +
              lane (word m (SP + 0x2000 * g + 32 * t)) r - spOff)).toNat) ∧
      FrameExcept m m' [(ACC + 0x2000 * g, ACC + 0x2000 * g + 8192)] ∧
      Call s Entry.intt [wd (ACC + 0x2000 * g)] ret tail m [] m' Gas.intt := by
  rw [MlDsa.Bridge44.nttInv_eq]
  obtain ⟨A, hA⟩ : ∃ A, A = ACC + 0x2000 * g := ⟨_, rfl⟩
  rw [← hA]
  have hSPa : ∀ t, SP + 0x2000 * g + 32 * t = A - 18688 + 32 * t := fun t => by
    rw [hA]; unfold SP ACC; omega
  have hHPa : ∀ t, HP + 0x2000 * g + 32 * t = A + 16384 + 32 * t := fun t => by
    rw [hA]; unfold HP ACC; omega
  simp only [hSPa, hHPa]
  have hAv : A = {A0} ∨ A = {A1} := by rw [hA]; unfold ACC; omega
  have hsp : spOff = 128 * 8380417 + 261888 - 1 := by unfold spOff MlDsa.Fips204.q; norm_num
  have htail : tail.length ≤ {HTAIL} := by
    have := hr.depth; simp only [Stack.intt, Stack.leaf] at this; omega
  obtain ⟨h, hh⟩ : ∃ h : Nat → Nat → F, h = fun k t => (((lanesPoly m A k)[t]! : ℤ) : F) := ⟨_, rfl⟩
  let H : Prop := (∀ k, k < 4 → ∀ t, t < 256 → lane (word m (A + 32 * t)) k < 2 ^ 57) ∧
    (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (A - 18688 + 32 * t)) r ≤ spOff ∧
      lane (word m (A + 16384 + 32 * t)) r ≤ 1)
  have hP0 : H → PI m A (fun t => t / 16 < 0)
      (fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))
      (fun t w => LOK (UInt256.ofNat w) (Bi 4) (fun k => invL (scaleR h k) 4 t)) := by
    intro hH
    refine passInvG_init (fun t ht k hk => ?_) (fun t => by omega)
    rw [lane_word]
    refine ⟨hH.1 k hk t ht, ?_⟩
    show _ = h k t
    simp only [hh]
    rw [lanesPoly_get' m A k ht]; push_cast; rfl
  obtain ⟨M1, hP1, hF1, hR1⟩ := ivA_pass hs htail ret H h A hAv m htbl hP0
  obtain ⟨M2, hP2, hF2, hR2⟩ := ivB_pass hs htail ret H h A hAv M1 m hF1
    (fun hH t ht r hr4 => by rw [← hsp]; exact hH.2 t ht r hr4) hr.jumpdest hr.small
    (fun hH => passInvG_init (passInvG_done (hP1 hH) (fun t _ => by omega)) (fun t => by omega))
  refine ⟨M2, fun h1 h2 t ht r hr4 => ?_, frame_trans1 hF1 hF2, ?_⟩
  · obtain ⟨W, hWB, hWF, hlane⟩ := passInvG_done (hP2 ⟨h1, h2⟩) (fun t _ => by omega) t ht r hr4
    rw [hlane, uh6L_spec MlDsaOpt{NN}.Proofs.P rfl (h2 t ht r hr4).2]
    congr 1
    rw [useHint_emod6 MlDsaOpt{NN}.Proofs.P _ (_ - 261887),
      useHint_emod6 MlDsaOpt{NN}.Proofs.P _ (_ - (spOff : Int))]
    congr 1
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    have hWn : ((W : ℤ) : F) = (((MlDsa44.Fips204.nttInv (lanesPoly m A r))[t]! : ℤ) : F) := by
      push_cast
      beta_reduce at hWF
      rw [hWF, nttInv_model _ (lanesPoly_size' m A r) ht]
      have e : scaleR h r = fun i => Rinv * (((lanesPoly m A r)[i]! : ℤ) : F) := by
        funext i; simp only [scaleR, hh]; rw [mul_comm]
      rw [e, invL_smul]
      unfold Sc
      linear_combination (8347681 * invL (fun i => (((lanesPoly m A r)[i]! : ℤ) : F)) 8 t) * R_Rinv
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (W : ℤ)
      ((MlDsa44.Fips204.nttInv (lanesPoly m A r))[t]!) 8380417).mp hWn
    refine ⟨-c + 128, ?_⟩
    have hq : (MlDsa.Fips204.q : Int) = 8380417 := by unfold MlDsa.Fips204.q; norm_num
    rw [hsp, hq]
    push_cast
    linear_combination -hc
  · rw [call_iff, Entry.intt, Gas.intt]
    exact (((i_pro hs htail m ret A (by omega)).trans (hR1.trans hR2)).mono
      (by norm_num)).of_eq (by simp) (by simp)

end MlDsaOptGlam{NN}.Proofs.NttG
'''


if __name__ == '__main__':
    which = sys.argv[2:]
    if which == ['uhdef']:
        print(uh_def())
        sys.exit(0)
    ctl, body = {}, {}
    for ps in PASSES:
        txt, c, ctl_i = gen_file(ps)
        open(OUT + ps['file'] + '.lean', 'w').write(txt)
        ctl[ps['name']] = ctl_i
        body[ps['name']] = sum(c)
        print(ps['file'], c, sum(c), 'head', LAB[ps['head']], PC[LAB[ps['head']]], 'ctl', ctl_i, PC[ctl_i])
    cc = gen_ctl(ctl)
    cA = 15 * (body['ivA'] + cc['ivA_cont']) + body['ivA'] + cc['ivA_exit']
    cB = 15 * (body['ivB'] + cc['ivB_cont']) + body['ivB'] + cc['ivB_exit']
    total = cc['i_pro'] + cA + cB
    print('intt', total, 'pro', cc['i_pro'], 'pass1', cA, 'pass2', cB)
    open(OUT + 'Top.lean', 'w').write(TOP.format(
        NN=NN, NOTES=NOTES, HTAIL=HTAIL, A0=ACC, A1=ACC + 0x2000, CU=CU,
        h1=PC[LAB['int1']], h2=PC[LAB['int2']], I1P=I1('P', '11296'), I2P=I2('P', '(512 + P)'),
        bA=body['ivA'], cAc=cc['ivA_cont'], bB=body['ivB'], cBc=cc['ivB_cont'], cA=cA, cB=cB))
