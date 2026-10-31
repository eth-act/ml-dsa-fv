"""Small EVM macro-assembler used by scripts/gen_opt.py.

The readable intermediate form is the listing (`Asm.listing()`): one
instruction per line with pc, mnemonic, immediate, the enclosing region
(subroutine) and generator comments. Labels are 2-byte PUSH targets.
"""
from __future__ import annotations

from opt_evm import OPS


class Asm:
    def __init__(self):
        self.items = []          # (kind, a, b)
        self.regions = []        # (item index, name)

    # ── emission ────────────────────────────────────────────────────────
    def op(self, name, comment=None):
        assert name in OPS, name
        self.items.append(("op", name, comment))

    def push(self, v, comment=None):
        assert v >= 0
        if v == 0:
            self.items.append(("op", "PUSH0", comment))
            return
        k = (v.bit_length() + 7) // 8
        assert k <= 32, hex(v)
        self.items.append(("push", v, k, comment))

    def pushn(self, v, k, comment=None):
        """PUSH with a fixed width (for patchable constants)."""
        self.items.append(("push", v, k, comment))

    def pushl(self, label, comment=None):
        self.items.append(("pushl", label, comment))

    def label(self, name):
        self.items.append(("label", name, None))
        self.items.append(("op", "JUMPDEST", None))

    def region(self, name):
        self.regions.append((len(self.items), name))

    def comment(self, text):
        self.items.append(("comment", text, None))

    def jump(self, label):
        self.pushl(label)
        self.op("JUMP")

    def jumpi(self, label):
        self.pushl(label)
        self.op("JUMPI")

    def raw(self, items):
        self.items.extend(items)

    # ── assembly ────────────────────────────────────────────────────────
    def assemble(self):
        addr = {}
        pc = 0
        pcs = []
        for it in self.items:
            pcs.append(pc)
            if it[0] == "op":
                pc += 1
            elif it[0] == "push":
                pc += 1 + it[2]
            elif it[0] == "pushl":
                pc += 3
            elif it[0] == "label":
                assert it[1] not in addr, f"duplicate label {it[1]}"
                addr[it[1]] = pc
        pcs.append(pc)
        out = bytearray()
        lines = []
        reg_at = dict(self.regions)
        region = "-"
        self.region_pcs = []
        for idx, it in enumerate(self.items):
            if idx in reg_at:
                region = reg_at[idx]
                self.region_pcs.append((len(out), region))
            kind = it[0]
            if kind == "op":
                out.append(OPS[it[1]][0])
                lines.append(f"{pcs[idx]:6d}  {it[1]:<14}{'':<20} ; {region}" + (f"  {it[2]}" if it[2] else ""))
            elif kind == "push":
                v, k = it[1], it[2]
                out.append(0x5F + k)
                out += v.to_bytes(k, "big")
                lines.append(f"{pcs[idx]:6d}  PUSH{k:<10}0x{v:0{2*k}x} ; {region}" + (f"  {it[3]}" if it[3] else ""))
            elif kind == "pushl":
                a = addr[it[1]]
                out.append(0x61)
                out += a.to_bytes(2, "big")
                lines.append(f"{pcs[idx]:6d}  PUSH2         @{it[1]} ; {region}")
            elif kind == "label":
                lines.append(f"{it[1]}:")
            elif kind == "comment":
                lines.append(f"        ; {it[1]}")
        self.labels = addr
        self.lines = lines
        return bytes(out)

    def listing(self):
        return "\n".join(self.lines) + "\n"


class Stack:
    """Tracks named stack values for straight-line code generation.

    `s` lists names bottom..top. `get(name, keep)` brings a copy (DUP) or
    the value itself (SWAP to top, if not kept) to the top of the stack.
    Anonymous/temporary values get names too; the generator is responsible
    for consuming everything it creates.
    """

    def __init__(self, asm: Asm, names=()):
        self.a = asm
        self.s = list(names)

    def depth(self, name):
        i = len(self.s) - 1 - self.s[::-1].index(name)
        return len(self.s) - 1 - i

    def has(self, name):
        return name in self.s

    def push(self, v, name, comment=None):
        self.a.push(v, comment)
        self.s.append(name)

    def pushl(self, label, name):
        self.a.pushl(label)
        self.s.append(name)

    def dup(self, name, new=None):
        d = self.depth(name)
        assert d < 16, f"dup too deep: {name} at {d} ({self.s})"
        self.a.op(f"DUP{d + 1}")
        self.s.append(new if new is not None else name + "'")

    def to_top(self, name):
        d = self.depth(name)
        if d == 0:
            return
        assert d <= 16, f"swap too deep: {name} at {d}"
        self.a.op(f"SWAP{d}")
        i = len(self.s) - 1 - d
        self.s[i], self.s[-1] = self.s[-1], self.s[i]

    def get(self, name, keep):
        """Bring `name` to the top: a DUP copy if keep else the value itself."""
        if keep:
            self.dup(name, "~" + name)
        else:
            self.to_top(name)

    def swap(self, k):
        self.a.op(f"SWAP{k}")
        self.s[-1], self.s[-1 - k] = self.s[-1 - k], self.s[-1]

    def op(self, name, nin, out=None, comment=None):
        self.a.op(name, comment)
        for _ in range(nin):
            self.s.pop()
        if out is not None:
            self.s.append(out)

    def pop(self, name=None):
        if name is not None:
            self.to_top(name)
        self.a.op("POP")
        self.s.pop()

    def add_const(self, name, c):
        """name += c without changing the stack layout."""
        d = self.depth(name)
        if d:
            self.a.op(f"SWAP{d}")
        self.a.push(c)
        self.a.op("ADD")
        if d:
            self.a.op(f"SWAP{d}")

    def sub_const(self, name, c):
        """name -= c without changing the stack layout."""
        d = self.depth(name)
        if d:
            self.a.op(f"SWAP{d}")
        self.a.push(c)
        self.a.op("SWAP1")
        self.a.op("SUB")
        if d:
            self.a.op(f"SWAP{d}")

    def expect(self, names):
        assert self.s == list(names), f"stack layout {self.s} != {list(names)}"

    def rename(self, old, new):
        i = len(self.s) - 1 - self.s[::-1].index(old)
        self.s[i] = new

    def top(self):
        return self.s[-1]
