#!/usr/bin/env python3
"""Proof-preservation gate: does a change keep everything proved exactly as it was?

    python3 scripts/gate/gate.py check BASE [HEAD] [--allow-moves] [options]
    python3 scripts/gate/gate.py snapshot REV -o FILE [options]

BASE and HEAD are each a git revision (`origin/master`, a SHA, a branch), a
checkout directory (its working tree as it is, uncommitted and untracked files
included; HEAD defaults to `.`), or a snapshot file written by `snapshot` (a
baseline). Each revision is built in a private worktree (`.lake/gate/wt`) and
summarised in a snapshot; `check` compares two snapshots and exits 1 on any
difference in meaning. See scripts/gate/README.md for what is checked and why.

Options:
  --allow-moves          tolerate constants that only moved to another module
  --allow-gate-change    tolerate a running gate that is not BASE's, or a HEAD whose
                         scripts/gate/ differs from the running gate
  --allow-lakefile-change  tolerate a lakefile.toml that differs from BASE's
  --bootstrap            BASE predates the gate (has no scripts/gate/): run this checkout's gate
  --clean                build the revision from scratch; implies --no-cache
  --jobs N               kernel replay workers (default: from memory, at most 8)
  --no-cache             recompute snapshots and kernel replays even when cached
  --skip-generators      do not re-run the generators (dev loop only: not a gate)
  --report FILE          also write the report to FILE
"""
from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import signal
import tempfile
import fcntl
import tomllib
import atexit
from pathlib import Path, PurePosixPath

GATE_DIR = Path(__file__).resolve().parent
ROOT = GATE_DIR.parent.parent

# ── Policy. It lives here, in the gate, and is read from nowhere else: run the base
# revision's gate (`git worktree add` the base, run its scripts/gate/gate.py), never
# the gate of the change under test. `sorryAx`, `Lean.trustCompiler` and the
# `native_decide` axioms are rejected by the extractor whatever this list says.
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

HEADLINES = [f"{ns}_{s}" for ns in ("MlDsa44.Proofs.reference", "MlDsaOpt44.Proofs.opt",
                                     "MlDsaOpt65.Proofs.opt", "MlDsaOpt87.Proofs.opt")
             for s in ("correctInAnyContextWithSchedule", "correctInAnyContext",
                       "correctWithSchedule", "correct")]

# Bytecode literal → the hex file it must equal, byte for byte.
BYTECODES = {
    "MlDsa44.referenceBytecode": "MlDsa44/Reference/reference.hex",
    "MlDsaOpt44.optBytecode": "MlDsaOpt/44/opt.hex",
    "MlDsaOpt65.optBytecode": "MlDsaOpt/65/opt.hex",
    "MlDsaOpt87.optBytecode": "MlDsaOpt/87/opt.hex",
}

# Frozen artifacts: byte-identical between BASE and HEAD (git blob ids).
FROZEN = ["*.hex", "MlDsa44/Reference/*", "MlDsa65/Reference/*", "MlDsa87/Reference/*",
          "MlDsaOpt/*", "MlDsaOpt44/Bytecode.lean", "MlDsaOpt65/Bytecode.lean",
          "MlDsaOpt87/Bytecode.lean", "MlDsaOpt44/listing.tsv", "MlDsaOpt65/listing.tsv",
          "MlDsaOpt87/listing.tsv", "docs/reference.listing", "docs/reference.layout"]

TOOL = ".lake/build/bin/mldsa44tool"
# Deterministic generators: (name, command, file its stdout must equal, or None when it
# rewrites files in place and the tree must stay unchanged). `--` marks a file argument.
GENERATORS = (
    [("gen_reference.py", ["python3", "scripts/gen_reference.py"], "MlDsa44/Reference/reference.yul")]
    + [(f"gen_reference_param.py {n}", ["python3", "scripts/gen_reference_param.py", str(n)],
        f"MlDsa{n}/Reference/reference.yul") for n in (44, 65, 87)]
    + [("gen_opt.py", ["python3", "scripts/gen_opt.py"], None),
       ("gen_opt.py --version v2", ["python3", "scripts/gen_opt.py", "--version", "v2"], None)]
    + [(f"proofgen_artifact.py {n}", ["python3", "scripts/proofgen_artifact.py", f"MlDsaOpt/{n}/opt.hex",
        f"MlDsaOpt{n}", f"MlDsaOpt{n}", f"opt{n}", str(m)], None)
       for n, m in ((44, 2097), (65, 2865), (87, 2897))]
    + [(f"mldsa44tool compile {n}", [TOOL, "compile", f"MlDsa{n}/Reference/reference.yul",
        f"MlDsa{n}/Reference/reference.hex"], None) for n in (44, 65, 87)]
    + [("mldsa44tool bytes", [TOOL, "bytes", "MlDsa44/Reference/reference.hex", "MlDsa44"],
        "MlDsa44/Reference/Bytes.lean"),
       ("mldsa44tool artifact", [TOOL, "artifact", "MlDsa44/Reference/reference.yul"],
        "MlDsa44/Proofs/Artifact.lean"),
       ("mldsa44tool layout", [TOOL, "layout", "MlDsa44/Reference/reference.yul"], "docs/reference.layout"),
       ("gen_keccak.py", ["python3", "MlDsa44/Proofs/Fn/Keccak/gen_keccak.py"], None),
       ("gen_kf1.py", ["python3", "MlDsaOpt44/Fn/Kf1/gen_kf1.py"], None),
       ("Csum gen_blocks.py 87", ["python3", "MlDsaOpt65/Fn/Csum/gen_blocks.py", "87"], None),
       ("Ginit gen_lanes.py 87", ["python3", "MlDsaOpt65/Fn/Ginit/gen_lanes.py", "87"],
        "MlDsaOpt87/Fn/Ginit/Lanes.lean")]
# Not listed (do not reproduce the checked-in files on master; see README): gen_kf4.py,
# gen_ntt.py, gen_p3.py, Main/Wp11Gen/gen_*.py, Main/S1/gen_s1.py, Csum gen_blocks.py 65,
# Ginit gen_lanes.py 65.
)
PORT_HEADER = re.compile(r"/- Ported from `([^`\s]+)` by `scripts/proofgen_port.py (\d+)`([^;\n]*);")
# Lean files outside every lean_lib that must still compile (rule 4).
OUTSIDE_LEAN = ["*/checks/*.lean", "scripts/*.lean"]  # PurePosixPath.match: `*` is one component
EXES = ["mldsa44tool", "mldsatool"]

WORK = ROOT / ".lake" / "gate"
WT = WORK / "wt"


def _gate_key() -> str:
    """Hash of the gate itself (policy included): part of every snapshot's cache key."""
    h = hashlib.sha256()
    for p in sorted(GATE_DIR.rglob("*")):
        if p.is_file() and ".lake" not in p.parts and "__pycache__" not in p.parts \
                and p.suffix in (".py", ".lean", ".toml"):
            h.update(str(p.relative_to(GATE_DIR)).encode() + b"\0" + p.read_bytes() + b"\0")
    return h.hexdigest()[:16]


GATE_KEY = _gate_key()  # once, at start: the gate's files may change while it runs


def gate_key() -> str:
    return GATE_KEY


# ── small helpers ────────────────────────────────────────────────────────────

def log(msg: str) -> None:
    print(f"[gate] {msg}", file=sys.stderr, flush=True)


def _run(cmd, **kw):
    """`subprocess.run` in a session of its own: if the gate stops for any reason while
    the command runs, its whole process group (`lake` and every `lean` it started) is
    killed, so no orphan can write into the worktree afterwards."""
    with subprocess.Popen(cmd, start_new_session=True, **kw) as p:
        try:
            out, err = p.communicate()
        except BaseException:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            raise
        return subprocess.CompletedProcess(cmd, p.returncode, out, err)


def run(cmd, cwd=None, check=True, env=None, capture=True, logfile=None, stdin=None):
    if logfile is not None:
        with open(logfile, "ab") as f:
            f.write(f"\n$ {' '.join(map(str, cmd))}\n".encode())
            f.flush()
            p = _run(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, stdin=stdin)
    else:
        cap = subprocess.PIPE if capture else None
        p = _run(cmd, cwd=cwd, env=env, stdout=cap, stderr=cap, stdin=stdin)
    if check and p.returncode != 0:
        err = (p.stderr or b"").decode(errors="replace") if logfile is None else f"see {logfile}"
        raise SystemExit(f"gate: command failed ({p.returncode}): {' '.join(map(str, cmd))}\n{err}")
    return p


def git(*args, cwd=None, check=True) -> str:
    return run(["git", *args], cwd=cwd or ROOT, check=check).stdout.decode().strip()


def lean_env() -> dict:
    env = dict(os.environ)
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    env["TMPDIR"] = str(ROOT / ".lake" / "tmp")
    (ROOT / ".lake" / "tmp").mkdir(parents=True, exist_ok=True)
    # Nothing the caller's environment says may steer Lean (rule 5).
    for k in list(env):
        if k.startswith(("LEAN", "LAKE", "ELAN")) and k != "ELAN_HOME":
            env.pop(k)
    return env


def blob(tree: str, path: str) -> str | None:
    p = run(["git", "rev-parse", f"{tree}:{path}"], cwd=ROOT, check=False)
    return p.stdout.decode().strip() if p.returncode == 0 else None


def show(tree: str, path: str) -> bytes:
    return run(["git", "cat-file", "-p", f"{tree}:{path}"], cwd=ROOT).stdout


# ── revisions ────────────────────────────────────────────────────────────────

def resolve(spec: str):
    """('snapshot', path) or ('tree', tree_sha, label)."""
    p = Path(spec)
    if p.is_file():
        return ("snapshot", p.resolve(), spec)
    if p.is_dir():
        d = p.resolve()
        common = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir", cwd=d))
        mine = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir"))
        if common != mine:
            raise SystemExit(f"gate: {d} is not a checkout of this repository")
        top = Path(git("rev-parse", "--show-toplevel", cwd=d))
        idx = WORK / "index.tmp"
        WORK.mkdir(parents=True, exist_ok=True)
        gitdir = Path(git("rev-parse", "--path-format=absolute", "--git-dir", cwd=top))
        if (gitdir / "index").exists():
            shutil.copy(gitdir / "index", idx)
        env = dict(os.environ, GIT_INDEX_FILE=str(idx))
        run(["git", "add", "-A", "."], cwd=top, env=env)
        tree = run(["git", "write-tree"], cwd=top, env=env).stdout.decode().strip()
        idx.unlink(missing_ok=True)
        head = git("rev-parse", "--short", "HEAD", cwd=top)
        return ("tree", tree, f"{spec} (working tree on {head}, tree {tree[:12]})")
    sha = git("rev-parse", "--verify", f"{spec}^{{commit}}")
    tree = git("rev-parse", f"{sha}^{{tree}}")
    return ("tree", tree, f"{spec} ({sha[:12]})")


def checkout(tree: str, clean: bool) -> None:
    if not (WT / ".git").exists():
        WORK.mkdir(parents=True, exist_ok=True)
        if WT.exists():
            shutil.rmtree(WT)
        git("worktree", "add", "--detach", str(WT), "HEAD")
    git("read-tree", "-u", "--reset", tree, cwd=WT)
    git("clean", "-fdq", "-e", ".lake", cwd=WT)
    lk = WT / ".lake"
    lk.mkdir(exist_ok=True)
    pk = lk / "packages"
    if pk.is_symlink() and pk.resolve() != (ROOT / ".lake" / "packages").resolve():
        pk.unlink()
    if not pk.is_symlink():
        if pk.exists():
            shutil.rmtree(pk)
        pk.symlink_to(ROOT / ".lake" / "packages")
    if clean and (lk / "build").exists():
        shutil.rmtree(lk / "build")


def worktree_users() -> list[str]:
    """Other processes whose working directory or open files are inside the worktree."""
    users = []
    wt = str(WT.resolve()) if WT.exists() else str(WT)
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid():
            continue
        try:
            paths = [os.readlink(proc / "cwd")] + [os.readlink(fd) for fd in (proc / "fd").iterdir()]
        except OSError:
            continue
        if any(x == wt or x.startswith(wt + "/") for x in paths):
            try:
                cmd = (proc / "cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace")[:80]
            except OSError:
                cmd = "?"
            users.append(f"{proc.name} {cmd}")
    return users


def lock_work() -> None:
    """One gate run per checkout: they share the worktree and its build directory."""
    global _LOCK
    WORK.mkdir(parents=True, exist_ok=True)
    f = open(WORK / "lock", "w")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        f.close()
        raise SystemExit(f"gate: another gate run holds {WORK / 'lock'}")
    _LOCK = f


def unlock_work() -> None:
    global _LOCK
    if _LOCK is not None:
        _LOCK.close()
        _LOCK = None


_LOCK = None


def deps_state(tree: str) -> list[str]:
    """Pinned dependencies: the revision's manifest must match the shared packages."""
    man = json.loads(show(tree, "lake-manifest.json"))
    out = []
    for pkg in man["packages"]:
        name = pkg["name"].strip("«»")
        if pkg.get("type") != "git":
            raise SystemExit(f"gate: dependency {name} is not a pinned git package")
        d = ROOT / ".lake" / "packages" / name
        rev = git("rev-parse", "HEAD", cwd=d) if d.exists() else "missing"
        dirty = git("status", "--porcelain", "--untracked-files=no", cwd=d) if d.exists() else ""
        if rev != pkg["rev"] or dirty:
            raise SystemExit(f"gate: .lake/packages/{name} is at {rev}{' (dirty)' if dirty else ''}, "
                             f"the revision pins {pkg['rev']}; run `lake update`-free `lake build` in the "
                             f"main checkout for that manifest first")
        out.append(f"{name}@{pkg['rev']}")
    return out


def lib_config(tree: str):
    for other in ("lakefile.lean", "lakefile.json"):
        if blob(tree, other):
            raise SystemExit(f"gate: the revision has {other}; only a declarative lakefile.toml is supported")
    cfg = tomllib.loads(show(tree, "lakefile.toml").decode())
    # fail closed on settings that move sources or outputs or select modules otherwise
    allowed = {"": {"name", "version", "defaultTargets", "require", "lean_lib", "lean_exe", "leanOptions"},
               "lean_lib": {"name", "roots", "leanOptions", "defaultFacets"},  # roots are built as +modules
               "lean_exe": {"name", "root", "supportInterpreter", "leanOptions"}}
    bad = sorted(set(cfg) - allowed[""])
    for sect in ("lean_lib", "lean_exe"):
        for t in cfg.get(sect, []):
            bad += [f"{sect}.{k}" for k in sorted(set(t) - allowed[sect])]
    if bad:
        raise SystemExit(f"gate: lakefile.toml settings the gate does not support: {', '.join(bad)}")
    libs, roots = [], []
    for lib in cfg.get("lean_lib", []):
        libs.append(lib["name"])
        roots += lib.get("roots", [lib["name"]])
    exes = [e.get("root", e["name"]) for e in cfg.get("lean_exe", [])]
    return libs, roots, exes, cfg.get("defaultTargets", [])


# ── snapshot ─────────────────────────────────────────────────────────────────

_TOOLS: Path | None = None


def tools(env) -> Path:
    """Build the extractor from the gate's own sources (never the revision's), once per
    gate process, into a fresh directory."""
    global _TOOLS
    if _TOOLS is None:
        WORK.mkdir(parents=True, exist_ok=True)
        d = Path(tempfile.mkdtemp(prefix=f"tools-{gate_key()}-", dir=WORK))
        atexit.register(shutil.rmtree, d, True)
        for f in ("GateExtract.lean", "GateReplay.lean", "lakefile.toml"):
            shutil.copy(GATE_DIR / "extract" / f, d / f)
        shutil.copy(ROOT / "lean-toolchain", d / "lean-toolchain")
        log(f"building the extractor in {d}")
        if run(["lake", "build"], cwd=d, env=env, logfile=d / "build.log", check=False).returncode:
            raise SystemExit(f"gate: building the extractor failed:\n{(d / 'build.log').read_text()[-3000:]}")
        exe = d / ".lake" / "build" / "bin"
        run([str(exe / "gate_extract"), "--selftest", "sha256"], env=env)
        _TOOLS = exe
    return _TOOLS


def changed_files() -> list[str]:
    a = git("diff", "--name-only", cwd=WT).splitlines()
    b = git("ls-files", "--others", "--exclude-standard", cwd=WT).splitlines()
    return sorted(set(a + b) - {".lake"})


def restore() -> None:
    git("checkout-index", "-a", "-f", cwd=WT)
    git("clean", "-fdq", "-e", ".lake", cwd=WT)


def generator_checks(env, logf, ports: bool = True) -> list[str]:
    lines = []
    for name, cmd, out in GENERATORS:
        p = run(cmd, cwd=WT, env=env, check=False)
        if p.returncode != 0:
            res, detail = "fail", f"exit {p.returncode}"
        elif out is not None:
            same = (WT / out).exists() and (WT / out).read_bytes() == p.stdout
            res, detail = ("ok", out) if same else ("fail", f"stdout differs from {out}")
        else:
            ch = changed_files()
            res, detail = ("ok", "tree unchanged") if not ch else ("fail", "changed: " + " ".join(ch[:20]))
        with open(logf, "ab") as f:
            f.write(f"\n$ {' '.join(cmd)}\n".encode() + (p.stderr or b"")[-4000:])
        restore()
        lines.append(f"K\tgen {esc(name)}\t{res}\t{esc(detail)}")
    if not ports:
        return lines
    # proofgen_port.py: every file with a `Ported from` header, re-ported from its source
    # with the arguments the header records (sources of the same set ported together).
    ports = {}
    for f in sorted(x for x in ls_files(WT) if x.startswith(("MlDsaOpt65/", "MlDsaOpt87/"))):
        if f.endswith(".lean"):
            m = PORT_HEADER.search((WT / f).read_text(errors="replace"))
            if m:
                # only the `--sub X` / `--path X` pairs; the header may carry prose after them
                args = tuple(a for pair in re.findall(r"(--(?:sub|path)) (\S+)", m.group(3)) for a in pair)
                ports[f] = (m.group(2), m.group(1), args)
    groups = {}
    for f, (nn, src, args) in ports.items():
        groups.setdefault((nn, args), []).append(f)
    for (nn, args), files in sorted(groups.items()):
        srcs = sorted({s for (n, s, _) in ports.values() if n == nn})
        before = {f: (WT / f).read_bytes() for f in files}
        p = run(["python3", "scripts/proofgen_port.py", nn, *args, *srcs], cwd=WT, env=env, check=False)
        for f in files:
            same = p.returncode == 0 and (WT / f).read_bytes() == before[f]
            lines.append(f"K\tport {esc(f)}\t{'ok' if same else 'fail'}\t{esc(ports[f][1] + ' ' + ' '.join(args))}")
        restore()
    return lines


def replay_keys(imports: dict[str, list[str]], salt: str) -> dict[str, str]:
    """Replay cache key of each module (.olean path): the replayer's code, toolchain and pins
    (salt), the module's .olean bytes, and recursively the keys of its project imports."""
    keys: dict[str, str] = {}

    def k(m: str) -> str:
        if m not in keys:
            h = hashlib.sha256(salt.encode() + b"\0" + m.encode() + b"\0")
            for ext in ("", ".server", ".private"):
                p = Path(m + ext)
                if p.exists():
                    h.update(ext.encode() + hashlib.sha256(p.read_bytes()).digest())
            for i in sorted(imports[m]):
                h.update(b"import " + (k(i) if i in imports else "?" + i).encode())
            keys[m] = h.hexdigest()
        return keys[m]

    for m in imports:
        k(m)
    return keys


def esc(x: str) -> str:
    """A field gate.py writes can never contain a separator."""
    return "".join(c if c.isprintable() and c not in "\t\\" else f"\\x{ord(c)}" for c in x)


def ls_files(cwd) -> list[str]:
    return [f for f in run(["git", "ls-files", "-z"], cwd=cwd).stdout.decode().split("\0") if f]


def snapshot(tree: str, label: str, opts) -> list[str]:
    key = gate_key()
    cache = WORK / "snapshots" / f"{tree}-{key}.tsv"
    if cache.exists() and not (opts.no_cache or opts.clean or opts.skip_generators):
        log(f"{label}: cached snapshot {cache.name}")
        return cache.read_text().split("\n")[:-1]
    env = lean_env()
    toolchain = show(tree, "lean-toolchain").decode().strip()
    lines = [f"R\tlabel\t{label}", f"R\ttree\t{tree}", f"R\tgate\t{key}", f"R\ttoolchain\t{toolchain}",
             f"R\tmanifest\t{blob(tree, 'lake-manifest.json')}",
             f"R\tlakefile\t{blob(tree, 'lakefile.toml')}"]
    deps = deps_state(tree)
    lines += [f"R\tdep\t{d}" for d in deps]
    if toolchain.encode() != (ROOT / "lean-toolchain").read_bytes().strip():
        raise SystemExit("gate: the revision's lean-toolchain differs from this checkout's")
    libs, roots, exes, defaults = lib_config(tree)
    # build outputs or Lake's cached configuration committed in the tree would stand in
    # for the worktree's own
    tracked_lake = git("ls-tree", "-r", "--name-only", tree, "--", ".lake")
    if tracked_lake:
        raise SystemExit(f"gate: the revision tracks files under .lake/: {tracked_lake.splitlines()[:5]}")
    exe = tools(env)
    log(f"{label}: checking out into {WT}")
    # An interrupted build can leave an .olean newer than its Lake trace (Lean wrote the
    # output, Lake had not yet recorded it); a later `lake build` of other sources then
    # accepts the stale .olean as up to date. The marker lives from checkout until every
    # build command has exited on its own; if it is found, the build directory is wiped.
    users = worktree_users()
    if users:
        raise SystemExit(f"gate: processes are still using {WT} (an earlier, interrupted run?): {users[:5]}; "
                         "stop them and rerun")
    marker = WORK / "build-in-progress"
    interrupted = marker.exists()
    if interrupted:
        log(f"{label}: an earlier build in {WT} was interrupted; building from scratch")
    marker.parent.mkdir(parents=True, exist_ok=True)
    marker.write_text(tree)
    checkout(tree, opts.clean or interrupted)
    logf = WORK / f"log-{tree[:12]}.txt"
    logf.write_text("")
    # the Lean that actually runs in this worktree (elan honours overrides)
    githash = run(["lean", "--githash"], cwd=WT, env=env).stdout.decode().strip()
    lines.append(f"R\tlean\t{githash}")
    # 1. full build: the default targets, every library root as an explicit module target
    #    (so lakefile facets cannot skip one), both executables; then nothing may be stale
    targets = [f"+{r}" for r in roots] + EXES
    t = run(["lake", "build"], cwd=WT, env=env, check=False, logfile=logf)
    lines.append(f"K\tbuild default targets ({' '.join(defaults)})\t{'ok' if t.returncode == 0 else 'fail'}\t-")
    build_rcs = []
    for x in targets:
        t2 = run(["lake", "build", x], cwd=WT, env=env, check=False, logfile=logf)
        build_rcs.append(t2.returncode)
        lines.append(f"K\tbuild {x}\t{'ok' if t2.returncode == 0 else 'fail'}\t-")
    fresh = run(["lake", "build", "--no-build", *targets], cwd=WT, env=env, check=False, logfile=logf)
    lines.append(f"K\tbuild up to date (lake build --no-build)\t{'ok' if fresh.returncode == 0 else 'fail'}\t-")
    built = t.returncode == 0 and fresh.returncode == 0
    if all(r >= 0 for r in [t.returncode, fresh.returncode] + build_rcs):  # none killed by a signal
        marker.unlink()
    log(f"{label}: build {'ok' if built else 'FAILED'} (log {logf})")
    if not built:
        lines.append("K\tsnapshot\tfail\tbuild failed; nothing extracted")
        return lines
    tracked = ls_files(WT)
    # 3. extraction. Project = every imported module whose .olean is in this worktree's
    #    build directory. The libraries' roots first; then each executable root on its own
    #    (they all define `main`), keyed apart.
    build_dir = WT / ".lake" / "build"
    recorded = WORK / f"recorded-{tree[:12]}.txt"
    recorded.write_text("")
    runs = [(roots, "")] + [([x], f"{x}:") for x in exes]
    mods: dict[str, str] = {}  # .olean path -> module
    for i, (rts, prefix) in enumerate(runs):
        out = WORK / f"extract-{tree[:12]}-{i}.tsv"
        args = [str(exe / "gate_extract"), "--roots", ",".join(rts), "--build-dir", str(build_dir),
                "--exclude", str(recorded), "--allowed", ",".join(ALLOWED_AXIOMS), "--out", str(out)]
        if prefix:
            args += ["--key-prefix", prefix]
        else:
            args += ["--headline", ",".join(HEADLINES)]
        run(["lake", "env", *args], cwd=WT, env=env, logfile=logf)
        ex = out.read_text().split("\n")
        mods.update({l.split("\t")[2]: l.split("\t")[1] for l in ex if l.startswith("M\t")})
        recorded.write_text("\n".join(mods) + "\n")
        lines += [l for l in ex if l and not l.startswith("P\t")]
    log(f"{label}: extracted {sum(1 for l in lines if l.startswith('C'))} constants from {len(mods)} modules")
    # 4. kernel replay of every recorded module (verdicts cached by a Merkle key over .olean bytes)
    imports = {l.split("\t")[1]: [i for i in l.split("\t")[2].split(",") if i]
               for l in lines if l.startswith("I\t")}
    replayer = hashlib.sha256(b"".join((GATE_DIR / "extract" / f).read_bytes()
                                       for f in ("GateReplay.lean", "lakefile.toml"))).hexdigest()
    keys = replay_keys(imports, f"{replayer}|{toolchain}|{githash}|{','.join(deps)}")
    cached = WORK / "replay-ok"
    cached.mkdir(parents=True, exist_ok=True)
    use_cache = not (opts.no_cache or opts.clean)
    todo = sorted(m for m in mods if not (use_cache and (cached / keys[m]).exists()))
    jobs = opts.jobs or max(1, min(8, os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") // (7 << 30)))
    log(f"{label}: kernel replay of {len(todo)} modules ({len(mods) - len(todo)} cached), {jobs} workers")
    passed = set()
    if todo:
        modfile = WORK / f"modules-{tree[:12]}.txt"
        modfile.write_text("\n".join(todo) + "\n")
        t4 = run(["lake", "env", str(exe / "gate_replay"), "-j", str(jobs), str(modfile)], cwd=WT, env=env,
                 check=False)
        with open(logf, "ab") as f:
            f.write(t4.stdout + t4.stderr)
        passed = {l[len("replayed "):] for l in t4.stdout.decode().split("\n") if l.startswith("replayed ")}
        for m in passed & set(todo):
            (cached / keys[m]).touch()
    failed = sorted(mods[m] for m in set(todo) - passed)
    lines.append(f"K\tkernel replay\t{'ok' if not failed else 'fail'}\t{len(mods)} modules"
                 + (f"; failed: {esc(' '.join(failed[:20]))}" if failed else ""))
    # Lean files outside the libraries (audit files, scripts; never the gate's own)
    outside = [f for f in tracked if not f.startswith("scripts/gate/")
               and any(PurePosixPath(f).match(g) for g in OUTSIDE_LEAN)]
    for f in sorted(outside):
        t3 = run(["lake", "env", "lean", f], cwd=WT, env=env, check=False, logfile=logf)
        lines.append(f"K\tlean {esc(f)}\t{'ok' if t3.returncode == 0 else 'fail'}\t-")
    # bytecode evaluation runs the revision's compiled code: after the replay
    out = WORK / f"bytes-{tree[:12]}.tsv"
    run(["lake", "env", str(exe / "gate_extract"), "--mode", "bytes", "--roots", ",".join(roots),
         "--bytecode", ",".join(BYTECODES), "--out", str(out)], cwd=WT, env=env, logfile=logf)
    lines += [l for l in out.read_text().split("\n") if l.startswith("B\t")]
    # 5. bytecode literals against the hex files
    for l in [l for l in lines if l.startswith("B\t")]:
        _, name, size, hx = l.split("\t")
        want = re.sub(r"\s", "", (WT / BYTECODES[name]).read_text()).lower()
        ok = size != "error" and hx == want
        lines.append(f"K\tbytecode {name} = {BYTECODES[name]}\t{'ok' if ok else 'fail'}\t{size} bytes")
    # 6. generators
    if opts.skip_generators:
        lines.append("K\tgenerators\tfail\tskipped (--skip-generators: not a gate run)")
    else:
        log(f"{label}: re-running generators")
        lines += generator_checks(env, logf)
    # 7. frozen artifacts and orphaned Lean files
    for f in tracked:
        if any(fnmatch.fnmatch(f, g) for g in FROZEN):
            lines.append(f"F\t{esc(f)}\t{blob(tree, f)}")
    for f in tracked:
        if f.endswith(".lean") and f.split("/")[0] in libs:
            o = build_dir / "lib" / "lean" / (f[:-len(".lean")] + ".olean")
            if not o.exists() or str(o.resolve()) not in mods:
                lines.append(f"O\t{esc(f)}")
    errors = Snap(lines).errors
    if errors:
        lines.append(f"K\tsnapshot\tfail\tmalformed: {esc(errors[0])}")
    elif not opts.skip_generators:
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_text("\n".join(lines) + "\n")
    return lines


# ── comparison ───────────────────────────────────────────────────────────────

class Snap:
    FIELDS = ["key", "name", "kind", "module", "lt", "ct", "lv", "cv", "full", "axioms", "aux", "rel"]
    WIDTH = {"R": 3, "K": 4, "F": 3, "C": 13, "X": 3, "D": 2, "N": 2, "H": 4, "B": 4, "O": 2, "M": 3, "I": 3, "S": 3}

    def __init__(self, lines):
        self.meta, self.checks, self.frozen, self.consts = {}, {}, {}, {}
        self.deps, self.viol, self.headline, self.bytes, self.orphans, self.modules = [], [], {}, {}, [], []
        self.errors, self.stale = [], []
        seen = set()
        for l in lines:
            f = l.split("\t")
            t = f[0]
            if not l or t not in self.WIDTH or len(f) != self.WIDTH[t]:
                self.errors.append(f"malformed snapshot line: {l[:120]!r}")
                continue
            if t in ("R", "K", "F", "H", "B") and f[1] != "dep":
                if (t, f[1]) in seen:
                    self.errors.append(f"duplicate {t} line for {f[1][:80]}")
                seen.add((t, f[1]))
            if t == "R":
                if f[1] == "dep":
                    self.deps.append(f[2])
                else:
                    self.meta[f[1]] = f[2]
            elif t == "K":
                self.checks[f[1]] = (f[2], f[3])
            elif t == "F":
                self.frozen[f[1]] = f[2]
            elif t == "C":
                if f[1] in self.consts:
                    self.errors.append(f"duplicate comparison key {f[1]}")
                self.consts[f[1]] = dict(zip(self.FIELDS, f[1:]))
            elif t in ("X", "D", "N"):
                self.viol.append(" ".join(f))
            elif t == "H":
                self.headline[f[1]] = (f[2], f[3])
            elif t == "B":
                self.bytes[f[1]] = (f[2], f[3])
            elif t == "O":
                self.orphans.append(f[1])
            elif t == "S":
                self.stale.append(f"{f[1]}: trace records {f[2]}")
            elif t == "M":
                self.modules.append(f[1])


def cap(items, n=40):
    items = list(items)
    return items[:n] + ([f"... and {len(items) - n} more"] if len(items) > n else [])


def compare(base: Snap, head: Snap, allow_moves=False, allow_gate_change=False, gate_files=None,
            headlines=None, bytecodes=None, allow_lakefile_change=False, base_gate_files=None):
    headlines = HEADLINES if headlines is None else headlines
    bytecodes = BYTECODES if bytecodes is None else bytecodes
    fails, out = [], []

    def section(title):
        out.append(f"\n== {title}")

    def fail(msg, details=()):
        fails.append(msg)
        out.append(f"FAIL {msg}")
        out.extend(f"     {d}" for d in cap(details))

    def ok(msg):
        out.append(f"ok   {msg}")

    out.append(f"base: {base.meta.get('label')}\nhead: {head.meta.get('label')}\ngate: {GATE_KEY} ({GATE_DIR})")
    section("trust base")
    for side, sn in (("base", base), ("head", head)):
        if sn.errors:
            fail(f"{side} snapshot is malformed", sn.errors)
        if "generators" in sn.checks:
            fail(f"{side} snapshot skipped the generators (--skip-generators): not a gate run")
    if base.meta.get("gate") != head.meta.get("gate"):
        fail(f"snapshots made by different gate versions ({base.meta.get('gate')} vs {head.meta.get('gate')}); "
             "re-snapshot the base with this gate")
    for k in ("toolchain", "lean", "manifest"):
        if base.meta.get(k) != head.meta.get(k) or not head.meta.get(k):
            fail(f"{k} differs: {base.meta.get(k)} -> {head.meta.get(k)}")
        else:
            ok(f"{k} identical ({head.meta.get(k)})")
    if base.deps != head.deps:
        fail("pinned dependency checkouts differ", sorted(set(base.deps) ^ set(head.deps)))
    if base.meta.get("lakefile") != head.meta.get("lakefile"):
        if allow_lakefile_change:
            out.append("warn lakefile.toml differs (allowed by --allow-lakefile-change)")
        else:
            fail("lakefile.toml differs (targets, roots, options); review it and rerun with "
                 "--allow-lakefile-change")
    # Rule 6: the policy is the running gate's, so it must be BASE's gate
    if base_gate_files is not None:
        if base_gate_files and not allow_gate_change:
            fail("the running gate is not BASE's scripts/gate/ (run BASE's gate, README rule 6)",
                 base_gate_files)
        elif base_gate_files:
            out.append("warn the running gate is not BASE's scripts/gate/ (allowed by --allow-gate-change)")
    if gate_files is not None:
        if gate_files and not allow_gate_change:
            fail("HEAD's scripts/gate/ differs from the running gate; review the gate change separately "
                 "and rerun with --allow-gate-change", gate_files)
        elif gate_files:
            out.append("warn HEAD's scripts/gate/ differs from the running gate (allowed by --allow-gate-change)")

    section("head: build, kernel replay, axioms, bytecode")
    must = [k for k in head.checks if k.startswith(("build ", "kernel replay", "bytecode ", "snapshot"))]
    for k in sorted(set(base.checks) - set(head.checks)):
        if k.startswith(("build ", "kernel replay", "bytecode ")):
            fail(f"{k}: ran on base, missing on head")
    for k in sorted(must):
        st, d = head.checks[k]
        (ok if st == "ok" else fail)(f"{k}" + ("" if d == "-" else f" [{d}]"))
    if "kernel replay" not in head.checks:
        fail("kernel replay did not run")
    for name in bytecodes:
        if name not in head.bytes:
            fail(f"bytecode literal {name} not evaluated")
    if head.stale:
        fail("build outputs that Lake's traces do not record (an interrupted build; rerun, or --clean)",
             head.stale)
    if head.viol:
        fail(f"axiom policy (decided by Lean's collectAxioms; allowed: {', '.join(ALLOWED_AXIOMS)})", head.viol)
    elif head.consts:
        ok(f"axiom policy: {len(head.consts)} constants use only {', '.join(ALLOWED_AXIOMS)}; no axiom declarations")
    for h in headlines:
        kind, axs = head.headline.get(h, ("missing", "-"))
        if kind != "theorem":
            fail(f"headline {h}: {kind}")
        else:
            ok(f"headline {h}: {axs}")

    section("checks that pass on base must pass on head (outside Lean files, generators)")
    for k in sorted(set(base.checks) | set(head.checks)):
        if k in must:
            continue
        b, h = base.checks.get(k, ("absent", "")), head.checks.get(k, ("absent", ""))
        if b[0] == "ok" and h[0] != "ok":
            fail(f"{k}: {h[0]} [{h[1]}]")
        elif h[0] != "ok":
            out.append(f"note {k}: {h[0]} on head, {b[0]} on base (not gating) [{h[1]}]")
    nok = sum(1 for k, v in head.checks.items() if v[0] == "ok" and k not in must)
    ok(f"{nok} checks pass on head")

    section("frozen artifacts (byte-identical)")
    diffs = [f"{p}: {base.frozen.get(p, 'absent')} -> {head.frozen.get(p, 'absent')}"
             for p in sorted(set(base.frozen) | set(head.frozen)) if base.frozen.get(p) != head.frozen.get(p)]
    if diffs:
        fail(f"{len(diffs)} frozen artifacts differ", diffs)
    else:
        ok(f"{len(head.frozen)} frozen artifacts identical")
    bdiff = [n for n in bytecodes if base.bytes.get(n) != head.bytes.get(n)]
    if bdiff:
        fail("bytecode literals differ", bdiff)
    else:
        ok(f"{len(bytecodes)} bytecode literals identical")

    section("signature diff (every non-auxiliary constant: kind, statement, meaning, axioms, module)")
    bc = {k: v for k, v in base.consts.items() if v["aux"] == "0"}
    hc = {k: v for k, v in head.consts.items() if v["aux"] == "0"}
    removed = sorted(set(bc) - set(hc))
    added = sorted(set(hc) - set(bc))
    changed, moved, meta_bodies = [], [], []
    for k in sorted(set(bc) & set(hc)):
        b, h = bc[k], hc[k]
        what = []
        if b["kind"] != h["kind"]:
            what.append(f"kind {b['kind']} -> {h['kind']}")
        if b["ct"] != h["ct"]:
            what.append("statement" + (" (edited)" if b["lt"] != h["lt"] else " (via a dependency)"))
        if b["full"] != h["full"] and b["ct"] == h["ct"]:
            body_only = b["kind"].startswith(("def", "opaque")) and b["cv"] != h["cv"]
            if body_only and b["rel"] == "0" and h["rel"] == "0":
                meta_bodies.append(f"{b['name']} ({b['kind']})")
            elif body_only:
                what.append("definition body" + (" (edited)" if b["lv"] != h["lv"] else " (via a dependency)"))
            else:
                what.append("declaration (universe parameters, constructors or recursor rules)")
        if b["axioms"] != h["axioms"]:
            what.append(f"axioms {b['axioms']} -> {h['axioms']}")
        if what:
            changed.append(f"{b['name']}: {'; '.join(what)}")
        elif b["module"] != h["module"]:
            moved.append(f"{b['name']}: {b['module']} -> {h['module']}")
    if removed:
        fail(f"{len(removed)} constants removed", [f"{bc[k]['name']} ({bc[k]['kind']}, {bc[k]['module']})" for k in removed])
    if changed:
        edited = [c for c in changed if "(edited)" in c or "kind" in c or "axioms" in c or "declaration" in c]
        fail(f"{len(changed)} constants changed ({len(edited)} directly, the rest through what they mention)",
             edited + [c for c in changed if c not in edited])
    if moved:
        if allow_moves:
            out.append(f"warn {len(moved)} constants moved (allowed by --allow-moves)")
            out.extend(f"     {m}" for m in cap(moved))
        else:
            fail(f"{len(moved)} constants moved to another module (rerun with --allow-moves if intended)", moved)
    if added:
        out.append(f"note {len(added)} constants added (no base constant changes meaning; their axioms are "
                   f"audited above)")
        out.extend(f"     {hc[k]['name']} ({hc[k]['kind']}, {hc[k]['module']})" for k in cap(added, 20)
                   if k in hc)
    if meta_bodies:
        out.append(f"note {len(meta_bodies)} definition bodies changed that no theorem statement depends on "
                   "(tactics, simprocs, executable code)")
        out.extend(f"     {m}" for m in cap(meta_bodies, 20))
    if not (removed or changed or (moved and not allow_moves)):
        ok(f"{len(bc)} constants: none removed or changed"
           + (f", {len(moved)} moved" if moved else "") + f", {len(added)} added")
    aux_b = sum(1 for v in base.consts.values() if v["aux"] == "1")
    aux_h = sum(1 for v in head.consts.values() if v["aux"] == "1")
    out.append(f"info auxiliary constants (match_/proof_/eq_ ..., not compared by name): {aux_b} -> {aux_h}")
    if head.orphans:
        out.append(f"note {len(head.orphans)} .lean files in library directories are not built by any root")
        out.extend(f"     {o}" for o in cap(head.orphans, 20))

    out.append(f"\nGATE {'FAILED' if fails else 'PASSED'}: {len(fails)} failure(s)")
    return fails, out


def gate_diff(tree: str, absent_differs: bool = False) -> list[str]:
    """Files of `tree` under scripts/gate/ that differ from the running gate's own files.
    A revision without a gate differs in nothing, unless `absent_differs`."""
    theirs = {}
    for l in git("ls-tree", "-r", tree, "--", "scripts/gate").splitlines():
        meta, path = l.split("\t", 1)
        theirs[path] = meta.split()[2]
    mine = {}
    for p in GATE_DIR.rglob("*"):
        if p.is_file() and ".lake" not in p.parts and "__pycache__" not in p.parts:
            mine["scripts/gate/" + str(p.relative_to(GATE_DIR))] = git("hash-object", str(p))
    if not theirs and not absent_differs:
        return []
    return sorted(k for k in set(theirs) | set(mine) if theirs.get(k) != mine.get(k))


def load(spec, opts):
    r = resolve(spec)
    if r[0] == "snapshot":
        return Snap(r[1].read_text().split("\n")[:-1]), None
    return Snap(snapshot(r[1], r[2], opts)), r[1]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("base")
    c.add_argument("head", nargs="?", default=".")
    s = sub.add_parser("snapshot")
    s.add_argument("rev")
    s.add_argument("-o", "--out", required=True)
    for p in (c, s):
        p.add_argument("--clean", action="store_true")
        p.add_argument("--jobs", type=int, default=0)
        p.add_argument("--no-cache", action="store_true")
        p.add_argument("--skip-generators", action="store_true")
    c.add_argument("--allow-moves", action="store_true")
    c.add_argument("--allow-gate-change", action="store_true")
    c.add_argument("--allow-lakefile-change", action="store_true")
    c.add_argument("--bootstrap", action="store_true")
    c.add_argument("--report")
    opts = ap.parse_args(argv)
    # SIGTERM unwinds like Ctrl-C, so running commands are killed with their children
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    lock_work()
    try:
        return _main(opts)
    finally:
        unlock_work()


def _main(opts):
    if opts.cmd == "snapshot":
        r = resolve(opts.rev)
        if r[0] != "tree":
            raise SystemExit("gate: snapshot needs a revision or a checkout")
        lines = snapshot(r[1], r[2], opts)
        Path(opts.out).write_text("\n".join(lines) + "\n")
        log(f"wrote {opts.out}")
        return 0
    base, bt = load(opts.base, opts)
    if resolve(opts.head)[0] == "snapshot":
        raise SystemExit("gate: HEAD must be a revision or a checkout (only BASE may be a snapshot file)")
    head, ht = load(opts.head, opts)
    # Rule 6: HEAD's scripts/gate/ is never run, and the running gate must be BASE's.
    edits = gate_diff(ht) if ht else None
    btree = bt or base.meta.get("tree")
    if btree and run(["git", "cat-file", "-e", f"{btree}^{{tree}}"], cwd=ROOT, check=False).returncode != 0:
        btree = None
    if btree and not git("ls-tree", btree, "--", "scripts/gate"):
        base_gate = [] if opts.bootstrap else ["BASE has no scripts/gate/ (before the gate existed: --bootstrap)"]
    else:
        base_gate = gate_diff(btree) if btree else ["BASE tree unknown"]
    fails, out = compare(base, head, opts.allow_moves, opts.allow_gate_change, edits,
                         allow_lakefile_change=opts.allow_lakefile_change, base_gate_files=base_gate)
    if opts.bootstrap and not base_gate:
        out.insert(3, "warn --bootstrap: BASE has no scripts/gate/, so this checkout's gate decided")
    text = "\n".join(out) + "\n"
    print(text)
    if opts.report:
        Path(opts.report).write_text(text)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
