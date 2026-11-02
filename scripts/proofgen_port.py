#!/usr/bin/env python3
"""Port ML-DSA-44 kernel proofs (`MlDsaOpt44/…`) to the ML-DSA-65/87 artifact.

Usage:
  python3 scripts/proofgen_port.py NN [--sub OLD=NEW ...] [--path OLD=NEW ...] FILE ...
  python3 scripts/proofgen_port.py --reloc NN [--all-jd] [--pc-lines REGEX] FILE ...

`--reloc NN` relocates files of `MlDsaOptNN/` in place from the previous proved
bytes (`MlDsaOpt/NN/v3/`, `OLD`) to the current bytes of the same set (`reloc_maps`,
`reloc_text`): unchanged regions are mapped whole, changed ones on their common
prefix/suffix; memory size v3 → v4 in memory-size contexts only. Every relocated
proof is re-checked by the kernel; read the `CHECK` / `RELOC` lines.

e.g.  python3 scripts/proofgen_port.py 65 MlDsaOpt44/Fn/Kf4/Blocks1.lean

Why a port and not a semantic transport. The kernels that `scripts/gen_opt.py`
emits identically for all three sets differ between the artifacts only in
their absolute jump targets (PUSH2 immediates of loop back-edges, internal
return addresses) and their position. A `Reach` fact of the 44 artifact cannot
be transported to another code by a generic simulation theorem: every
contract quantifies over a caller return address that must be a valid
JUMPDEST *of the 44 code*, and inverting the relational `Steps` of a 44 trace
needs an argument that no exception-and-resume path through the caller can
rejoin the frame. So the block lemmas are re-checked against the new artifact
instead: the 44 proof text is relocated and re-elaborated. Pure lemmas
(models, bit-level identities, loop invariants over memory) are not copied:
the ported files import and open the 44 modules that hold them.

What the port rewrites, for every FILE (written to the same relative path
under `MlDsaOptNN/`):

* instruction indices inside `opt44_reach [...]` / `locatedPath [...]` lists and
  the index argument of `reach_mcopy hs N`: through the index map of the
  enclosing subroutine (44 region → NN region, same instruction count);
* program counters `callState X N`, `then N`, `else N`: through the pc map;
  stack words `wd N` only when `N` is a JUMPDEST of the 44 code (reported); (every instruction boundary of every region
  whose instruction count agrees, plus each region's end);
* the fixed memory size `2065` → `memWords` of NN;
* the tactic names `opt44_` → `optNN_`, the namespaces `MlDsaOpt44` →
  `MlDsaOptNN` in `namespace` / `end` / `open` lines and in
  `MlDsaOpt44.Proofs.Infra` / `.Artifact` / `MlDsaOpt44.optBytecode` references;
  imports of ported files
  are renamed, imports of other files are kept (pure 44 lemmas);
* after every `namespace` line, `open MlDsaOpt44.Proofs` and the 44 twin of the
  namespace; every `open N` of a namespace that has a 44 twin also opens the
  twin. So unported names resolve to the 44 constants (names of the NN
  namespace take precedence); `maxHeartbeats 0` (block timings differ slightly
  per artifact);
* `--sub OLD=NEW`: extra whole-word substitutions (data constants that differ,
  e.g. the `BK` address in `fix`; also namespace components, e.g.
  `--sub NttW=NttW2` for a second instance);
* `--path OLD=NEW`: output path rewrite (and the matching import rewrite among
  ported modules), e.g. `--path Fn/Ntt/=Fn/Ntt2/` for a second instance of a
  kernel at another base pointer.

Every other number in the pc-map domain is reported (file, line, context) so
the porter can check that it is data. The result must build; nothing here is
trusted.
"""
from __future__ import annotations

import difflib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
MEMW = {44: 2616, 65: 2865, 87: 2897}             # v4 (current bytes)
OLD = "v3"                                        # `--reloc` source: `MlDsaOpt/NN/v3/`
MEMW_OLD = {44: 2097, 65: 2865, 87: 2897}         # memory size of OLD


def regions(nn, sub=""):
    out = {}
    for l in open(os.path.join(ROOT, "MlDsaOpt", str(nn), sub, "layout.txt")):
        m = re.match(r"\s*(\d+) \.\.\s+(\d+)\s+\d+ bytes\s+(\S+)", l)
        if m:
            out[m.group(3)] = (int(m.group(1)), int(m.group(2)))
    return out


def kz(nn):
    """Base of `kf1`'s third buffer `KZ` (v3 layout)."""
    for l in open(os.path.join(ROOT, "MlDsaOpt", str(nn), "layout.txt")):
        m = re.match(r"\s*KZ\s+0x([0-9a-f]+)", l)
        if m:
            return int(m.group(1), 16)
    raise SystemExit(f"no KZ in MlDsaOpt/{nn}/layout.txt")


def listing(nn):
    pcs = []
    for l in open(os.path.join(ROOT, f"MlDsaOpt{nn}", "listing.tsv")).readlines()[1:]:
        i, pc, _ = l.split("\t", 2)
        pcs.append(int(pc))
    return pcs


def jumpdests44():
    out = set()
    for l in open(os.path.join(ROOT, "MlDsaOpt44", "listing.tsv")).readlines()[1:]:
        i, pc, ins = l.rstrip("\n").split("\t", 2)
        if ins == "JUMPDEST":
            out.add(int(pc))
    return out


JD44 = jumpdests44()


def maps(nn):
    """Index and pc maps 44 → NN over the regions with equal instruction counts."""
    r44, rnn = regions(44), regions(nn)
    p44, pnn = listing(44), listing(nn)
    idx, pc, kinds = {}, {}, {}
    for name, (a, b) in r44.items():
        if name not in rnn or name in ("main", "expand_a", "hash_mu", "final_hash"):
            continue
        a2, b2 = rnn[name]
        i44 = [i for i, p in enumerate(p44) if a <= p < b]
        inn = [i for i, p in enumerate(pnn) if a2 <= p < b2]
        if len(i44) != len(inn):
            continue
        for x, y in zip(i44, inn):
            idx[x] = y
            pc[p44[x]] = pnn[y]
            kinds[p44[x]] = name
        pc[b] = b2
    return idx, pc, kinds


def disasm(nn, sub=""):
    """[(pc, opcode, immediate)] of `MlDsaOpt/NN/[sub/]opt.hex`, one entry per
    instruction (the order of `listing.tsv`)."""
    txt = open(os.path.join(ROOT, "MlDsaOpt", str(nn), sub, "opt.hex")).read().strip()
    code = bytes.fromhex(txt[2:] if txt.startswith("0x") else txt)
    out, i = [], 0
    while i < len(code):
        o = code[i]
        w = o - 0x5F if 0x5F <= o <= 0x7F else 0
        out.append((i, o, int.from_bytes(code[i + 1:i + 1 + w], "big") if w else None))
        i += 1 + w
    return out


def reloc_maps(nn):
    """Index and pc maps v2 → v3 of one set (`--reloc`).

    A region with the same instruction count in both versions is mapped
    entirely. A changed region is mapped on the matching stretches of the two
    instruction sequences (difflib), comparing instructions modulo PUSH2
    immediates (jump targets), so the unchanged parts keep their proofs. Everything else
    (the changed code) is unmapped: its proofs have to be rewritten."""
    ra, rb = regions(nn, OLD), regions(nn)
    da, db = disasm(nn, OLD), disasm(nn)
    pa, pb = [p for p, _, _ in da], [p for p, _, _ in db]
    key = lambda t: (t[1], None if t[1] == 0x61 else t[2])
    idx, pc = {}, {}
    for name, (a, b) in ra.items():
        if name not in rb:
            continue
        a2, b2 = rb[name]
        ia = [i for i, p in enumerate(pa) if a <= p < b]
        ib = [i for i, p in enumerate(pb) if a2 <= p < b2]
        if len(ia) == len(ib):
            pairs = list(zip(ia, ib))
            pc[b] = b2
        else:
            # matching blocks of the two instruction sequences (difflib): the
            # unchanged stretches of a changed region keep their proofs
            sm = difflib.SequenceMatcher(None, [key(da[i]) for i in ia], [key(db[i]) for i in ib],
                                         autojunk=False)
            pairs = []
            for x, y, n in sm.get_matching_blocks():
                pairs += [(ia[x + t], ib[y + t]) for t in range(n)]
            if pairs and pairs[-1] == (ia[-1], ib[-1]):
                pc[b] = b2
            print(f"reloc {nn}: {name} changed ({len(ia)} -> {len(ib)} instructions); "
                  f"mapped {len(pairs)} in {len(sm.get_matching_blocks()) - 1} stretches")
        for x, y in pairs:
            idx[x] = y
            pc[pa[x]] = pb[y]
    jd = {p for p, o, _ in da if o == 0x5B}
    return idx, pc, jd


L, R = "\x02", "\x03"            # protect relocated numbers from later passes


def reloc_text(src, nn, idx, pcm, jd, report, fname, all_jd=False, data=(), pc_lines=None):
    """In-place v2 → v3 relocation of one file of `MlDsaOptNN` (`--reloc`).

    Contexts as in the 44 → NN port (`then N` / `else N` only inside
    `callState s (if …)`), plus the `Entry` pcs of `Layout.lean`. With
    `all_jd`, every other 4–5 digit number that is a moved v2 JUMPDEST (and
    not a layout constant in `data`) is relocated too and reported as `RELOC`
    (custom block predicates carry pcs as plain arguments); on lines matching
    the regex `pc_lines`, every moved v2 instruction pc is."""
    def map_list(m):
        def one(t):
            n = int(t.group(0))
            if n not in idx:
                report.append(f"{fname}: index {n} in a changed region (unmapped)")
                return t.group(0)
            return L + str(idx[n]) + R
        return m.group(1) + re.sub(r"\d+", one, m.group(2)) + "]"

    out = re.sub(rf"((?:opt{nn}_r?reach|locatedPath|blockCostEval|reach_block(?:_pot)?\s+\S+)\s*\[)([^\]]*)\]",
                 map_list, src)

    def map_mcopy(m):
        n = int(m.group(2))
        if n not in idx:
            report.append(f"{fname}: reach_mcopy index {n} unmapped")
            return m.group(0)
        return m.group(1) + L + str(idx[n]) + R
    out = re.sub(r"((?:reach_mcopy|reach_ret)\s+\S+\s+⟨?)(\d+)", map_mcopy, out)

    def map_pc(m):
        n = int(m.group(2))
        if n in pcm:
            return m.group(1) + L + str(pcm[n]) + R
        if n in jd:
            report.append(f"{fname}: pc {n} in a changed region (unmapped): {m.group(0)}")
        return m.group(0)

    out = re.sub(r"(callState\s+(?:\w+|\([^()]*\))\s+)(\d+)\b", map_pc, out)
    out = re.sub(r"(callState\s+\w+\s+\(if [^()]*\bthen\s+)(\d+)\b", map_pc, out)
    out = re.sub(r"(callState\s+\w+\s+\(if [^()]*\belse\s+)(\d+)\b", map_pc, out)

    def map_jd(m):
        n = int(m.group(2))
        if n in jd and n in pcm:
            if pcm[n] != n:
                report.append(f"{fname}: relocated stack word wd {n} -> {pcm[n]} (old JUMPDEST)")
            return m.group(1) + L + str(pcm[n]) + R
        return m.group(0)
    out = re.sub(r"(\bwd\s+)(\d+)\b", map_jd, out)

    # `namespace Entry … end Entry` (Layout.lean): subroutine entry pcs
    def map_entry(m):
        return re.sub(r"(def \w+ : Nat := )(\d+)", lambda e: map_pc(e), m.group(0))
    out = re.sub(r"namespace Entry\n.*?\nend Entry", map_entry, out, flags=re.S)
    old, new = MEMW_OLD[nn], MEMW[nn]           # memory-size contexts only (never index lists)
    out = re.sub(rf"\b{old}(?=\s*≤\s*(?:s\.activeWords|32 \* s\.activeWords))", str(new), out)
    out = re.sub(rf"(32 \* |memWords = |memWords : Nat := ){old}\b", rf"\g<1>{new}", out)
    moved = {n for n, v in pcm.items() if v != n}
    lines = out.split("\n")
    for k, l in enumerate(lines):
        if re.search(rf"opt{nn}_r?reach", l) or "locatedPath" in l:
            continue
        bare = re.sub(f"{L}[^{R}]*{R}", "", l)
        for m in re.finditer(r"(?<![\w.])(\d{4,5})(?![\w.])", bare):
            n = int(m.group(1))
            if n in jd and n in moved and all_jd and n not in data:
                report.append(f"RELOC {fname}:{k + 1}: {n} -> {pcm[n]}: {l.strip()[:100]}")
            elif n in jd and (n in moved or n not in pcm):
                report.append(f"{fname}:{k + 1}: {n}: {l.strip()[:100]}")
        if all_jd:
            anypc = pc_lines is not None and re.search(pc_lines, l)
            def sub(m):
                n = int(m.group(1))
                ok = (n in jd or anypc) and n in moved and n not in data
                if ok and n not in jd:
                    report.append(f"RELOC {fname}:{k + 1}: {n} -> {pcm[n]} (pc-line): {l.strip()[:100]}")
                return str(pcm[n]) if ok else m.group(0)
            parts = re.split(f"({L}[^{R}]*{R})", l)
            lines[k] = "".join(p if p.startswith(L) else
                               re.sub(r"(?<![\w.])(\d{4,5})(?![\w.])", sub, p) for p in parts)
    return "\n".join(lines).replace(L, "").replace(R, "")


def layout_data(nn):
    """Every address constant of `layout.txt` (both versions), as a guard for `--all-jd`."""
    out = set()
    for sub in (OLD, ""):
        for l in open(os.path.join(ROOT, "MlDsaOpt", str(nn), sub, "layout.txt")):
            for h in re.findall(r"0x[0-9a-f]+", l):
                out.add(int(h, 16))
    return out


def reloc_main(nn, files, all_jd=False, pc_lines=None):
    idx, pcm, jd = reloc_maps(nn)
    data = layout_data(nn)
    report = []
    for f in files:
        path = os.path.join(ROOT, f)
        src = open(path).read()
        out = reloc_text(src, nn, idx, pcm, jd, report, f, all_jd, data, pc_lines)
        if out != src:
            with open(path, "w") as fh:
                fh.write(out)
            print(f"relocated {f}")
    for r in report:
        print("CHECK", r)


def namespaces44():
    """Every namespace declared (absolutely or nested) in `MlDsaOpt44/**.lean`."""
    out = set()
    for dp, _, fs in os.walk(os.path.join(ROOT, "MlDsaOpt44")):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            stack = []
            for l in open(os.path.join(dp, f)):
                m = re.match(r"namespace\s+(\S+)\s*$", l)
                if m:
                    n = m.group(1)
                    full = n if n.startswith("MlDsaOpt44") or not stack else stack[-1] + "." + n
                    stack.append(full)
                    out.add(full)
                elif re.match(r"end\s+\S+\s*$", l) and stack:
                    stack.pop()
    return out


NS44 = namespaces44()


def port_text(src, nn, idx, pcm, subs, ported, report, fname):
    tac44, tacn = "opt44_", f"opt{nn}_"

    def map_list(m):
        body = m.group(2)
        def one(t):
            n = int(t.group(0))
            if n not in idx:
                raise SystemExit(f"{fname}: index {n} outside the mapped regions")
            return str(idx[n])
        return m.group(1) + re.sub(r"\d+", one, body) + "]"

    out = re.sub(r"((?:opt44_r?reach|locatedPath|blockCostEval)\s*\[)([^\]]*)\]", map_list, src)
    out = re.sub(r"(reach_mcopy\s+\S+\s+)(\d+)",
                 lambda m: m.group(1) + str(idx[int(m.group(2))]), out)

    def map_pc(m):
        n = int(m.group(2))
        if n in pcm:
            return m.group(1) + str(pcm[n])
        return m.group(0)

    out = re.sub(r"(callState\s+(?:\w+|\([^()]*\))\s+)(\d+)\b", map_pc, out)
    def map_jd(m):
        # stack words are relocated only if they are a JUMPDEST of the 44 code
        # (return addresses, jump targets); other values are data
        n = int(m.group(2))
        if n in pcm and n in JD44:
            report.append(f"{fname}: relocated stack word wd {n} -> {pcm[n]} (44 JUMPDEST)")
            return m.group(1) + str(pcm[n])
        return m.group(0)

    out = re.sub(r"(\bwd\s+)(\d+)\b", map_jd, out)
    out = re.sub(r"(\b(?:then|else)\s+)(\d+)\b", map_pc, out)
    old, new = MEMW[44], MEMW[nn]              # memory-size contexts only (never index lists)
    out = re.sub(rf"\b{old}(?=\s*≤\s*(?:s\.activeWords|32 \* s\.activeWords))", str(new), out)
    out = re.sub(rf"(32 \* |memWords = |memWords : Nat := ){old}\b", rf"\g<1>{new}", out)
    kz44, kzn = kz(44), kz(nn)                 # kf1's third buffer (v3): word addresses
    out = re.sub(r"(?<![\w.])(\d{5})(?![\w.])", lambda m: str(int(m.group(1)) - kz44 + kzn)
                 if kz44 <= int(m.group(1)) < kz44 + 800 and (int(m.group(1)) - kz44) % 32 == 0
                 else m.group(0), out)
    for old, new in subs:
        out = re.sub(rf"\b{re.escape(old)}\b", new, out)
    out = out.replace(tac44, tacn)
    out = out.replace("MlDsaOpt44.Proofs.Infra", f"MlDsaOpt{nn}.Proofs.Infra")
    out = out.replace("MlDsaOpt44.Proofs.Artifact", f"MlDsaOpt{nn}.Proofs.Artifact")
    out = out.replace("MlDsaOpt44.optBytecode", f"MlDsaOpt{nn}.optBytecode")
    lines = out.split("\n")
    res = []
    stack = []                     # full namespaces (NN names)
    roots = ("EvmSemantics", "MlDsaOptCommon", "MlDsa44", "MlDsa", "Mathlib", "Lean", "Nat",
             "List", "Std", "Fips", "Int", "ZMod", "Function", "Classical", "Option", "Array")

    def to44(ns):
        ns = ns.replace(f"MlDsaOpt{nn}", "MlDsaOpt44", 1)
        for old, new in subs:                     # undo namespace renames (`--sub NttW=NttW2`)
            ns = re.sub(rf"\b{re.escape(new)}\b", old, ns)
        return ns

    for l in lines:
        m = re.match(r"import (MlDsaOpt44\.\S+)", l)
        if m:
            mod = m.group(1)
            path = mod.replace(".", "/") + ".lean"
            if path in ported or mod in ("MlDsaOpt44.Layout", "MlDsaOpt44.Budget", "MlDsaOpt44.Infra", "MlDsaOpt44.Infra.Reflect"):
                l = l.replace("MlDsaOpt44", f"MlDsaOpt{nn}", 1)
            res.append(l)
            continue
        m = re.match(r"namespace\s+(\S+)\s*$", l)
        if m:
            name = m.group(1).replace("MlDsaOpt44", f"MlDsaOpt{nn}", 1)
            full = name if name.startswith(f"MlDsaOpt{nn}") or not stack else stack[-1] + "." + name
            stack.append(full)
            res.append(f"namespace {name}")
            opens = ["MlDsaOpt44.Proofs"]
            f44 = to44(full)
            if f44 != "MlDsaOpt44.Proofs" and f44 in NS44:
                opens.append(f44)
            res.append("")
            res.append("open " + " ".join(opens))
            continue
        m = re.match(r"end\s+(\S+)\s*$", l)
        if m and stack:
            stack.pop()
            res.append(l.replace("MlDsaOpt44", f"MlDsaOpt{nn}", 1))
            continue
        m = re.match(r"(\s*open\s+)(.*?)(\s+in)?\s*$", l)
        if m and not l.strip().startswith("open scoped"):
            names = m.group(2).split()
            extra = []
            cur = to44(stack[-1]) if stack else ""
            for n_ in names:
                if n_.startswith("MlDsaOpt44"):
                    if n_ in NS44:
                        extra.append(n_)
                    continue
                if n_.startswith(roots) or "(" in n_:
                    continue
                c = cur
                while c:
                    if c + "." + n_ in NS44:
                        extra.append(c + "." + n_)
                        break
                    c = c.rsplit(".", 1)[0] if "." in c else ""
            names = [x.replace("MlDsaOpt44", f"MlDsaOpt{nn}") for x in names]
            names += [e for e in extra if e not in names]
            l = m.group(1) + " ".join(names) + (m.group(3) or "")
        res.append(l)
    out = "\n".join(res)
    # report remaining numbers that look like 44 pcs
    for k, l in enumerate(out.split("\n")):
        if re.search(rf"opt{nn}_r?reach", l) or "locatedPath" in l:
            continue
        for m in re.finditer(r"\b(\d{4,5})\b", l):
            n = int(m.group(1))
            if n in pcm and n >= 6000 and n not in pcm.values():
                report.append(f"{fname}:{k + 1}: {n}: {l.strip()[:100]}")
    return out


def main(argv):
    if not argv:
        raise SystemExit(__doc__)
    if argv == ["--reflect-selected"]:
        # Preserve the ports' hand adjustments; change measured proofs only.
        for nn in (44, 65, 87):
            for relative, names in (("Fn/Blk/BodyA.lean", {"bodyA"}),
                                    ("Fn/Sponge/Trabs.lean", {"trabs_mid"}),
                                    ("Fn/Kf4/Blocks1.lean", None),
                                    ("Fn/Kf4/Blocks2.lean", None)):
                path = os.path.join(ROOT, f"MlDsaOpt{nn}", relative)
                text = open(path).read()
                chunks = re.split(r"(?=theorem \w+)", text)
                for i, chunk in enumerate(chunks):
                    match = re.match(r"theorem (\w+)", chunk)
                    if match and (match[1] in names if names is not None else match[1].startswith(("r1_", "r2_"))):
                        chunks[i] = chunk.replace(f"opt{nn}_reach", f"opt{nn}_rreach")
                text = "".join(chunks)
                imp = f"import MlDsaOpt{nn}.Infra.Reflect\n"
                if imp not in text:
                    text = imp + text
                with open(path, "w") as f:
                    f.write(text)
        return
    if argv[0] == "--reloc":
        nn = int(argv[1])
        rest = argv[2:]
        all_jd, pc_lines, files = False, None, []
        it = iter(rest)
        for a in it:
            if a == "--all-jd":
                all_jd = True
            elif a == "--pc-lines":
                pc_lines = next(it)
            else:
                files.append(os.path.relpath(a, ROOT) if os.path.isabs(a) else a)
        reloc_main(nn, files, all_jd, pc_lines)
        return
    nn = int(argv[0])
    subs, files, paths = [], [], []
    it = iter(argv[1:])
    for a in it:
        if a == "--sub":
            o, n = next(it).split("=")
            subs.append((o, n))
        elif a == "--path":
            o, n = next(it).split("=")
            paths.append((o, n))
        else:
            files.append(os.path.relpath(a, ROOT) if os.path.isabs(a) else a)
    idx, pcm, _ = maps(nn)
    ported = set(files)
    report = []
    for f in files:
        src = open(os.path.join(ROOT, f)).read()
        dst = f.replace("MlDsaOpt44/", f"MlDsaOpt{nn}/", 1)
        for o, n_ in paths:
            dst = dst.replace(o, n_)
        os.makedirs(os.path.dirname(os.path.join(ROOT, dst)), exist_ok=True)
        text = port_text(src, nn, idx, pcm, subs, ported, report, f)
        for o, n_ in paths:
            mo, mn = o.strip("/").replace("/", "."), n_.strip("/").replace("/", ".")
            text = re.sub(rf"(import MlDsaOpt{nn}\.){re.escape(mo)}\b", rf"\g<1>{mn}", text)
        header = (f"/- Ported from `{f}` by `scripts/proofgen_port.py {nn}`"
                  + (" " + " ".join(f"--sub {o}={n}" for o, n in subs) if subs else "")
                  + (" " + " ".join(f"--path {o}={n}" for o, n in paths) if paths else "")
                  + "; hand adjustments are marked `-- port:`. -/\n")
        # imports first (some 44 files start with a comment line)
        lines = text.split("\n")
        imps = [l for l in lines if l.startswith("import ")]
        rest = [l for l in lines if not l.startswith("import ")]
        while rest and not rest[0].strip():
            rest.pop(0)
        imps += [e for e in (f"import MlDsaOpt{nn}.Layout", f"import MlDsaOpt{nn}.Budget") if e not in imps]
        text = "\n".join(imps + [header.rstrip("\n"),
                                 "set_option maxHeartbeats 0  -- port: re-elaboration headroom"]
                          + rest)
        with open(os.path.join(ROOT, dst), "w") as fh:
            fh.write(text)
        print(f"ported {f} -> {dst}")
    for r in report:
        print("CHECK", r)


if __name__ == "__main__":
    main(sys.argv[1:])
