"""kf8i: kf8m with one round per loop iteration, in place (half the code).

Every chi output of a round is parked on the stack (its home word is still
needed by rho until the last row), and after the tenth row the 50 outputs
are stored to their home words, top first, twice each (DUP1 PUSH MSTORE
PUSH MSTORE as in kf8m). So one buffer is enough and the loop body is a
single round. Parking an output under the row's remaining B values costs a
SWAP, and it breaks some of chi's in-place operand consumption; the B load
order and the output order of each row are chosen by exhaustive search
(120 x 120 per row type) to minimise that.
"""
from __future__ import annotations

import itertools
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from opt_asm import Asm, Stack  # noqa: E402
from opt_evm import OPS  # noqa: E402
from opt_keccak import CHI  # noqa: E402

import lab  # noqa: E402
from kf8m import PHI, PSI, Layout8, rho_src, store2, theta8, waddr  # noqa: E402


def gas_of(items):
    return sum(OPS[it[1]][1] if it[0] == "op" else 3 for it in items if it[0] in ("op", "push"))


def chi_row(st: Stack, yo, out_order, rc_get, tag, store_now=None):
    """B0..B4 on top (any order): leaves outputs O{tag}{x} parked, B's consumed.
    Outputs in store_now (xo -> address) are stored at once (twice) instead."""
    store_now = store_now or {}
    uses = {f"B{x}": 3 for x in range(5)}
    for n, xo in enumerate(out_order):
        op, n1, n2, nout = CHI[yo][xo]
        names = [f"B{(xo + 1) % 5}", f"B{(xo + 2) % 5}"]
        nots = [n1, n2]
        for j, (b, nt) in enumerate(zip(names, nots)):
            uses[b] -= 1
            if uses[b] == 0 and st.depth(b) == j:   # top for the first operand, under it for the second
                st.rename(b, f"f{j}")
            else:
                st.dup(b, f"f{j}")
            if nt:
                st.op("NOT", 1, f"f{j}")
        if st.s[-2] != "f0":
            raise ValueError("operand order")
        st.op(op, 2, "f")
        b = f"B{xo}"
        uses[b] -= 1
        if uses[b] == 0 and st.depth(b) == 1:
            st.rename(b, "g")
        else:
            st.dup(b, "g")
        st.op("XOR", 2, "o")
        if nout:
            st.op("NOT", 1, "o")
        if rc_get is not None and xo == 0:
            rc_get(st)
            st.op("XOR", 2, "o")
        st.rename("o", f"O{tag}{xo}")
        if xo in store_now:
            store2(st, store_now[xo])
        # dead B copies whose last use was a DUP
        for x in range(5):
            if uses.get(f"B{x}") == 0 and st.has(f"B{x}"):
                st.rename(f"B{x}", "dead")
                uses.pop(f"B{x}")
        live = sum(1 for v in st.s[-8:] if v.startswith("B") or v == "dead")
        k = 0
        for v in reversed(st.s[:-1]):
            if v.startswith("B") or v == "dead":
                k += 1
            else:
                break
        if n < 4 and k and xo not in store_now:
            st.swap(k)                       # park the output under the live B's
        while st.top() == "dead":
            st.pop()
        del live
    while "dead" in st.s:
        st.pop("dead")
    assert not any(v.startswith("B") for v in st.s), st.s


def best_row(yo, store_now=None):
    """(load order, output order) minimising the row's gas."""
    best = None
    for load in itertools.permutations(range(5)):
        for out in itertools.permutations(range(5)):
            a = Asm()
            st = Stack(a, ["x"] + [f"B{x}" for x in load])
            try:
                chi_row(st, yo, out, (lambda st: st.push(1, "rc")) if yo == 0 else None, "", store_now)
            except (ValueError, AssertionError):
                continue
            g = gas_of(a.items)
            if best is None or g < best[0]:
                best = (g, load, out)
    return best


ROWS = {}
ORDERS = {
    "yo-major": [(yo, ho) for yo in range(5) for ho in range(2)],
    "ho-major": [(0, 0), (0, 1)] + [(yo, ho) for ho in range(2) for yo in range(1, 5)],
}
ORDER = list(ORDERS["yo-major"])


def consumer(i, h):
    """Row-half (yo, ho) whose rho reads word (i, h)."""
    x, y = i % 5, i // 5
    yo = (2 * x + 3 * y) % 5
    for ho in range(2):
        if rho_src(i, ho)[0] == h:
            return yo, ho


def round8i(st: Stack, buf, dbuf, rc_get, stats=None):
    base = len(st.s)
    fD = theta8(st, buf, dbuf, PHI, PSI, stats=stats)
    done = set()
    for yo, ho in ORDER:
        done.add((yo, ho))
        store_now = {xo: waddr(buf, xo + 5 * yo, ho) for xo in range(5)
                     if consumer(xo + 5 * yo, ho) in done}
        key = (yo, ho, tuple(sorted(store_now)))
        if key not in ROWS:
            ROWS[key] = best_row(yo, {k: 0 for k in store_now})
        _, load, out = ROWS[key]
        if True:
            for xo in load:
                sx, sy = (xo + 3 * yo) % 5, xo
                s = sx + 5 * sy
                h, k = rho_src(s, ho)
                st.push(waddr(buf, s, h) + k, "a")
                st.op("MLOAD", 1, "m")
                st.push(waddr(dbuf, sx, h) + (k + fD[(sx, h)]) % 32, "a")
                st.op("MLOAD", 1, "d")
                st.op("XOR", 2, f"B{xo}")
            chi_row(st, yo, out, (lambda st, ho=ho: rc_get(st, ho)) if yo == 0 else None, f"{yo}{ho}_", store_now)
    while len(st.s) > base:
        name = st.top()
        yo, ho, xo = int(name[1]), int(name[2]), int(name[4])
        store2(st, waddr(buf, xo + 5 * yo, ho))


def gen_kf8i(a: Asm, name, st_addr, d_addr, rct, stats=None):
    a.region(name)
    a.label(name)
    st = Stack(a, ["ret"])
    st.push(rct, "rp")
    a.label(name + "_loop")

    def rc_get(st, ho):
        st.dup("rp", "p")
        if ho:
            st.push(32, "o")
            st.op("ADD", 2, "p")
        st.op("MLOAD", 1, "rc")
    round8i(st, st_addr, d_addr, rc_get, stats)
    st.add_const("rp", 64)
    st.dup("rp", "c")
    a.push(rct + 32 * 48)
    st.s.append("end")
    st.op("GT", 2, "lt")
    a.jumpi(name + "_loop")
    st.s.pop()
    st.pop("rp")
    a.op("JUMP")


if __name__ == "__main__":
    L = Layout8()
    stats = {}
    for name, order in ORDERS.items():
        ORDER[:] = order
        ROWS.clear()
        g, sz, n = lab.check(lambda a: gen_kf8i(a, "kf", L.ST, L.DB, L.RCT, stats), L)
        print(f"  row order {name}: {g:,} gas/call, parked outputs/round {sum(5 - len(k[2]) for k in ROWS)}")
    g, sz, n = lab.check(lambda a: gen_kf8i(a, "kf", L.ST, L.DB, L.RCT, stats), L)
    print(f"kf8i (1 round/iter, in place, parked outputs): {g:,} gas/call, {g / 8:,.0f}/state, {sz:,} B, "
          f"{n} KAT calls ok; parked outputs/round {sum(5 - len(k[2]) for k in ROWS)}")
