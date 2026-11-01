#!/usr/bin/env python3
"""Per-module wall time, CPU time and peak RSS of the Lean build.

Run `lake build` first: every module is then re-checked on its own with
`lean <file>` against the already-built imports (nothing is written), one at a
time by default, so each row is the module run alone. Rows are written to a
TSV as they finish.

  python3 scripts/time_modules.py                      # all default targets
  python3 scripts/time_modules.py -o out.tsv MlDsaOpt44.Fn.Sponge.Trabs
  python3 scripts/time_modules.py --libs MlDsa44 --jobs 4   # contended, faster

Columns: module, wall_s, cpu_s (user+sys of the lean process), maxrss_mb
(peak resident set of the lean process), exit code. Machine facts (nproc,
memory, Lean version, git commit) go in the header comment.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^import\s+(.+)$")


def module_file(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports_of(mod: str) -> list[str]:
    out = []
    for line in module_file(mod).read_text().splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out += m.group(1).split("--")[0].split()
    return out


def closure(roots: list[str]) -> list[str]:
    """Local modules reachable from `roots`, dependencies first."""
    seen: dict[str, None] = {}
    def visit(mod: str):
        if mod in seen or not module_file(mod).exists():
            return
        seen[mod] = None  # mark before recursion (no cycles in Lean imports)
        for dep in imports_of(mod):
            visit(dep)
        # re-insert so dependencies come first
        del seen[mod]
        seen[mod] = None
    for r in roots:
        visit(r)
    return list(seen)


def lean_env() -> dict[str, str]:
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT,
                         check=True, capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=out)
    env.setdefault("TMPDIR", str(ROOT / ".lake" / "tmp"))
    return env


def run_one(mod: str, env: dict[str, str], lean: str, extra: list[str]):
    # Same outputs as `lake build` (olean, ilean, C), written to a scratch dir.
    with tempfile.TemporaryDirectory(dir=env["TMPDIR"]) as tmp:
        outs = ["-o", f"{tmp}/m.olean", "-i", f"{tmp}/m.ilean", "-c", f"{tmp}/m.c"]
        t0 = time.monotonic()
        proc = subprocess.Popen([lean, str(module_file(mod).relative_to(ROOT)), *outs, *extra],
                                cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out = proc.stdout.read()
        _, status, ru = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
        wall = time.monotonic() - t0
    cpu = ru.ru_utime + ru.ru_stime
    return mod, wall, cpu, ru.ru_maxrss / 1024, proc.returncode, out.decode(errors="replace")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("modules", nargs="*", help="modules to time (default: all of --libs)")
    ap.add_argument("--libs", nargs="*", help="library roots (default: defaultTargets of lakefile.toml)")
    ap.add_argument("-o", "--out", default="module-times.tsv")
    ap.add_argument("-j", "--jobs", type=int, default=1, help="parallel lean processes (1 = alone)")
    ap.add_argument("--lean-arg", action="append", default=[], help="extra argument for lean")
    ap.add_argument("--save-output", metavar="DIR",
                    help="write each module's lean output to DIR/<module>.txt (e.g. with "
                         "--lean-arg=-Dprofiler=true for per-category times)")
    args = ap.parse_args()

    if args.modules:
        mods = args.modules
    else:
        libs = args.libs or tomllib.loads((ROOT / "lakefile.toml").read_text())["defaultTargets"]
        mods = closure(libs)
    env = lean_env()
    if args.save_output:
        os.makedirs(args.save_output, exist_ok=True)
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ROOT, check=True,
                          capture_output=True, text=True).stdout.strip()
    version = subprocess.run([lean, "--version"], capture_output=True, text=True).stdout.strip()
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                            capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
    mem_gb = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") / 2**30

    with open(args.out, "w") as f:
        f.write(f"# {commit}{' (dirty)' if dirty else ''}; {version}; nproc={os.cpu_count()}, "
                f"mem={mem_gb:.0f}G; jobs={args.jobs}; lean args={args.lean_arg}\n")
        f.write("module\twall_s\tcpu_s\tmaxrss_mb\texit\n")
        f.flush()
        failed = []
        with ThreadPoolExecutor(args.jobs) as pool:
            for i, (mod, wall, cpu, rss, rc, out) in enumerate(
                    pool.map(lambda m: run_one(m, env, lean, args.lean_arg), mods), 1):
                f.write(f"{mod}\t{wall:.1f}\t{cpu:.1f}\t{rss:.0f}\t{rc}\n")
                if args.save_output:
                    Path(args.save_output, mod + ".txt").write_text(out)
                f.flush()
                print(f"[{i}/{len(mods)}] {mod} {wall:.1f}s cpu {cpu:.1f}s {rss:.0f}MB"
                      + (f" EXIT {rc}" if rc else ""), flush=True)
                if rc:
                    failed.append(mod)
                    sys.stderr.write(out[-4000:])
    if failed:
        sys.exit(f"{len(failed)} modules failed: {' '.join(failed)}")


if __name__ == "__main__":
    main()
