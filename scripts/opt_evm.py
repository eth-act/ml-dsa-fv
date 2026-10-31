#!/usr/bin/env python3
"""Minimal Osaka EVM interpreter for the ML-DSA optimisation work.

Covers the opcodes a pure verifier frame can use (arithmetic, bitwise,
calldata, memory, control flow, RETURN/REVERT/INVALID, plus CODECOPY) with
exact frame gas (static costs, copy costs, quadratic memory expansion), and
records per-pc gas for profiling. Measures the same quantity as
`mldsa44tool run-file` and foundry's GasProbe: gas consumed by the frame
itself, from pc = 0.

Used by scripts/gen_opt.py's unit tests and scripts/opt_run.py; not part of
any proof.
"""
from __future__ import annotations

M256 = (1 << 256) - 1

# name -> (opcode, static gas)
OPS = {
    "STOP": (0x00, 0), "ADD": (0x01, 3), "MUL": (0x02, 5), "SUB": (0x03, 3),
    "DIV": (0x04, 5), "MOD": (0x06, 5), "ADDMOD": (0x08, 8), "MULMOD": (0x09, 8),
    "LT": (0x10, 3), "GT": (0x11, 3), "EQ": (0x14, 3), "ISZERO": (0x15, 3),
    "AND": (0x16, 3), "OR": (0x17, 3), "XOR": (0x18, 3), "NOT": (0x19, 3),
    "BYTE": (0x1A, 3), "SHL": (0x1B, 3), "SHR": (0x1C, 3),
    "CALLDATALOAD": (0x35, 3), "CALLDATASIZE": (0x36, 2), "CALLDATACOPY": (0x37, 3),
    "CODECOPY": (0x39, 3),
    "POP": (0x50, 2), "MLOAD": (0x51, 3), "MSTORE": (0x52, 3), "MSTORE8": (0x53, 3),
    "JUMP": (0x56, 8), "JUMPI": (0x57, 10), "JUMPDEST": (0x5B, 1), "MCOPY": (0x5E, 3),
    "PUSH0": (0x5F, 2), "RETURN": (0xF3, 0), "REVERT": (0xFD, 0), "INVALID": (0xFE, 0),
}
for _i in range(1, 33):
    OPS[f"PUSH{_i}"] = (0x5F + _i, 3)
for _i in range(1, 17):
    OPS[f"DUP{_i}"] = (0x7F + _i, 3)
    OPS[f"SWAP{_i}"] = (0x8F + _i, 3)
NAMES = {v[0]: k for k, v in OPS.items()}
GAS = {v[0]: v[1] for v in OPS.values()}


class EvmError(Exception):
    pass


def mem_cost(words: int) -> int:
    return 3 * words + words * words // 512


def run(code: bytes, calldata: bytes = b"", gas: int = 1 << 40, memory: bytearray | None = None,
        profile: bool = False, stack: list | None = None, stop_pc: int | None = None,
        max_steps: int = 1 << 62):
    """Execute `code`; returns dict(status, ret, gas_used, memory, stack, prof).

    status: 'return' | 'revert' | 'stop' | 'invalid' | 'oog' | 'error:<msg>'.
    `stop_pc`: halt (status 'break') when pc reaches this value.
    """
    n = len(code)
    jumpdests = set()
    i = 0
    while i < n:
        op = code[i]
        if op == 0x5B:
            jumpdests.add(i)
        if 0x60 <= op <= 0x7F:
            i += op - 0x5E
        else:
            i += 1
    mem = memory if memory is not None else bytearray()
    msize = (len(mem) + 31) // 32
    if len(mem) < msize * 32:
        mem.extend(b"\0" * (msize * 32 - len(mem)))
    st = stack if stack is not None else []
    cd = calldata
    cdl = len(cd)
    used = 0
    pc = 0
    prof = [0] * (n + 1) if profile else None
    cnt = [0] * (n + 1) if profile else None
    G = GAS
    steps = 0

    def expand(end):
        nonlocal msize, used
        if end <= msize * 32:
            return
        w = (end + 31) // 32
        used += mem_cost(w) - mem_cost(msize)
        mem.extend(b"\0" * ((w - msize) * 32))
        msize = w

    def cdload(off):
        if off >= cdl:
            return 0
        chunk = cd[off:off + 32]
        return int.from_bytes(chunk + b"\0" * (32 - len(chunk)), "big")

    status = "stop"
    ret = b""
    try:
        while True:
            if pc >= n:
                status = "stop"
                break
            if pc == stop_pc:
                status = "break"
                break
            steps += 1
            if steps > max_steps:
                status = "steps"
                break
            op = code[pc]
            g0 = used
            used += G.get(op, 0)
            if 0x60 <= op <= 0x7F:
                k = op - 0x5F
                st.append(int.from_bytes(code[pc + 1:pc + 1 + k].ljust(k, b"\0"), "big"))
                npc = pc + 1 + k
            elif 0x80 <= op <= 0x8F:
                st.append(st[-(op - 0x7F)])
                npc = pc + 1
            elif 0x90 <= op <= 0x9F:
                k = op - 0x8E
                st[-1], st[-k] = st[-k], st[-1]
                npc = pc + 1
            else:
                npc = pc + 1
                if op == 0x01:
                    a = st.pop(); st[-1] = (a + st[-1]) & M256
                elif op == 0x02:
                    a = st.pop(); st[-1] = (a * st[-1]) & M256
                elif op == 0x03:
                    a = st.pop(); st[-1] = (a - st[-1]) & M256
                elif op == 0x04:
                    a = st.pop(); b = st[-1]; st[-1] = a // b if b else 0
                elif op == 0x06:
                    a = st.pop(); b = st[-1]; st[-1] = a % b if b else 0
                elif op == 0x08:
                    a = st.pop(); b = st.pop(); m = st[-1]; st[-1] = (a + b) % m if m else 0
                elif op == 0x09:
                    a = st.pop(); b = st.pop(); m = st[-1]; st[-1] = (a * b) % m if m else 0
                elif op == 0x10:
                    a = st.pop(); st[-1] = 1 if a < st[-1] else 0
                elif op == 0x11:
                    a = st.pop(); st[-1] = 1 if a > st[-1] else 0
                elif op == 0x14:
                    a = st.pop(); st[-1] = 1 if a == st[-1] else 0
                elif op == 0x15:
                    st[-1] = 1 if st[-1] == 0 else 0
                elif op == 0x16:
                    a = st.pop(); st[-1] &= a
                elif op == 0x17:
                    a = st.pop(); st[-1] |= a
                elif op == 0x18:
                    a = st.pop(); st[-1] ^= a
                elif op == 0x19:
                    st[-1] ^= M256
                elif op == 0x1A:
                    i_ = st.pop(); x = st[-1]; st[-1] = (x >> (8 * (31 - i_))) & 0xFF if i_ < 32 else 0
                elif op == 0x1B:
                    s = st.pop(); st[-1] = (st[-1] << s) & M256 if s < 256 else 0
                elif op == 0x1C:
                    s = st.pop(); st[-1] = st[-1] >> s if s < 256 else 0
                elif op == 0x35:
                    st[-1] = cdload(st[-1])
                elif op == 0x36:
                    st.append(cdl)
                elif op == 0x37 or op == 0x39 or op == 0x5E:
                    dst = st.pop(); src = st.pop(); ln = st.pop()
                    if ln:
                        used += 3 * ((ln + 31) // 32)
                        if op == 0x5E:
                            expand(max(dst, src) + ln)
                            mem[dst:dst + ln] = bytes(mem[src:src + ln])
                        else:
                            expand(dst + ln)
                            srcb = cd if op == 0x37 else code
                            chunk = srcb[src:src + ln] if src < len(srcb) else b""
                            mem[dst:dst + ln] = chunk + b"\0" * (ln - len(chunk))
                elif op == 0x50:
                    st.pop()
                elif op == 0x51:
                    a = st[-1]; expand(a + 32); st[-1] = int.from_bytes(mem[a:a + 32], "big")
                elif op == 0x52:
                    a = st.pop(); v = st.pop(); expand(a + 32); mem[a:a + 32] = v.to_bytes(32, "big")
                elif op == 0x53:
                    a = st.pop(); v = st.pop(); expand(a + 1); mem[a] = v & 0xFF
                elif op == 0x56:
                    d = st.pop()
                    if d not in jumpdests:
                        raise EvmError(f"bad jump {d} at {pc}")
                    npc = d
                elif op == 0x57:
                    d = st.pop(); c = st.pop()
                    if c:
                        if d not in jumpdests:
                            raise EvmError(f"bad jumpi {d} at {pc}")
                        npc = d
                elif op == 0x5B:
                    pass
                elif op == 0x5F:
                    st.append(0)
                elif op == 0x00:
                    status = "stop"
                    break
                elif op == 0xF3 or op == 0xFD:
                    a = st.pop(); ln = st.pop()
                    if ln:
                        expand(a + ln)
                    ret = bytes(mem[a:a + ln])
                    status = "return" if op == 0xF3 else "revert"
                    break
                elif op == 0xFE:
                    status = "invalid"
                    break
                else:
                    raise EvmError(f"unsupported opcode {op:#x} at {pc}")
            if len(st) > 1024:
                raise EvmError("stack overflow")
            if profile:
                prof[pc] += used - g0
                cnt[pc] += 1
            pc = npc
    except IndexError:
        status = f"error:stack underflow at {pc} ({NAMES.get(code[pc], hex(code[pc]))})"
    except EvmError as e:
        status = f"error:{e}"
    if used > gas:
        status = "oog"
    return {"status": status, "ret": ret, "gas_used": used, "memory": mem, "stack": st,
            "prof": prof, "cnt": cnt, "pc": pc, "steps": steps}


def disasm(code: bytes):
    out = []
    i = 0
    while i < len(code):
        op = code[i]
        name = NAMES.get(op, f"0x{op:02x}")
        if 0x60 <= op <= 0x7F:
            k = op - 0x5F
            out.append((i, name, code[i + 1:i + 1 + k].hex()))
            i += 1 + k
        else:
            out.append((i, name, ""))
            i += 1
    return out
