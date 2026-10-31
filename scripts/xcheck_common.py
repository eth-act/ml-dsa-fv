"""Shared plumbing for the production-EVM cross-check (foundry/).

Oracles (each maps EIP-8355 calldata to a 0/1 verdict):

* ``lean``  the Lean specification `MlDsa44.accepts` (`mldsa44tool spec-file`),
            which is what the bytecode is proved to implement;
* ``rust``  RustCrypto ml-dsa 0.1.1   (foundry/oracles/bin/mldsa44-oracle-rust);
* ``go``    Go stdlib FIPS 140-3 mldsa (foundry/oracles/bin/mldsa44-oracle-go);
* ``dpy``   dilithium-py 1.4.0 (.ref/pylib). Known divergence: it accepts a
            repeated hint index inside a row, which FIPS 204 Algorithm 21
            rejects (`repeated_hint_index`).

The Lean-semantics execution of the frozen bytecode (`mldsa44tool run-file`)
gives the exact frame gas and returned word for each calldata; results are
cached by content hash in foundry/cache/xcheck/leanevm.tsv.
"""
from __future__ import annotations

import hashlib
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / ".ref" / "pylib"))

from dilithium_py.ml_dsa import ML_DSA_44  # noqa: E402

PK_LEN, SIG_LEN = 1312, 2420
HEADER = PK_LEN + SIG_LEN
OMEGA, K, L = 80, 4, 4
HINT_OFF = 32 + L * 576  # offset of the hint inside σ
GAMMA1, BETA = 1 << 17, 78

TOOL = ROOT / ".lake" / "build" / "bin" / "mldsa44tool"
HEX = ROOT / "MlDsa44" / "Reference" / "reference.hex"
ORACLE_BIN = ROOT / "foundry" / "oracles" / "bin"
CACHE = ROOT / "foundry" / "cache" / "xcheck"
LEAN_ENV = dict(os.environ, TMPDIR=str(ROOT / ".lake" / "tmp"))


def hexline(cd: bytes) -> str:
    return cd.hex() if cd else "-"


# ── gas schedule ───────────────────────────────────────────────────────────

def schedule(size: int) -> int:
    """Closed form of `MlDsa44.Proofs.Gas.schedule` (README.md); checked
    against the Lean definition itself by `lean_schedule`."""
    if size < HEADER:
        return 267
    n = size - HEADER
    ell = n + 66
    w = (81120 + n + 31) // 32
    return (13_140_898 + 59_324 * (ell // 136) + 3 * (((ell % 136) + 31) // 32)
            + 3 * ((n + 31) // 32) + 3 * w + w * w // 512)


def lean_schedule(sizes) -> dict[int, int]:
    """Evaluates the Lean `Gas.schedule` for every size (scripts/xcheck_schedule.lean).

    Answers are cached in foundry/cache/xcheck/schedule.tsv; evaluation needs
    the proof oleans, so a transiently missing olean (a concurrent `lake
    build`) is retried."""
    CACHE.mkdir(parents=True, exist_ok=True)
    cache_path = CACHE / "schedule.tsv"
    out: dict[int, int] = {}
    if cache_path.exists():
        for line in cache_path.read_text().splitlines():
            n, g = line.split("\t")
            out[int(n)] = int(g)
    sizes = sorted(set(sizes))
    todo = [s for s in sizes if s not in out]
    for i in range(0, len(todo), 4000):
        chunk = [str(s) for s in todo[i:i + 4000]]
        for attempt in range(10):
            res = subprocess.run(["lake", "env", "lean", "--run", "scripts/xcheck_schedule.lean", *chunk],
                                 cwd=ROOT, env=LEAN_ENV, capture_output=True, text=True)
            if res.returncode == 0:
                break
            print(f"xcheck_schedule.lean failed (attempt {attempt + 1}): {res.stdout[:300]}{res.stderr[:300]}")
            time.sleep(30)
        else:
            raise RuntimeError("cannot evaluate Lean Gas.schedule")
        with cache_path.open("a") as f:
            for line in res.stdout.splitlines():
                n, g = line.split("\t")
                out[int(n)] = int(g)
                f.write(line + "\n")
    missing = [s for s in sizes if s not in out]
    assert not missing, f"xcheck_schedule.lean did not answer {missing[:5]}"
    return {s: out[s] for s in sizes}


# ── verdict oracles ────────────────────────────────────────────────────────

def _lines_oracle(cmd, calldatas, stdin=True) -> list[int]:
    CACHE.mkdir(parents=True, exist_ok=True)
    text = "".join(hexline(cd) + "\n" for cd in calldatas)
    if stdin:
        res = subprocess.run(cmd, input=text, check=True, capture_output=True, text=True, env=LEAN_ENV)
    else:
        path = CACHE / f"oracle_in_{os.getpid()}.txt"
        path.write_text(text)
        res = subprocess.run([*cmd, str(path)], check=True, capture_output=True, text=True,
                             env=LEAN_ENV)
        path.unlink()
    out = [int(x) for x in res.stdout.split()]
    assert len(out) == len(calldatas), f"{cmd[0]}: {len(out)} answers for {len(calldatas)} inputs"
    return out


def lean_spec(calldatas) -> list[int]:
    return _lines_oracle([str(TOOL), "spec-file"], calldatas, stdin=False)


def rust(calldatas) -> list[int]:
    return _lines_oracle([str(ORACLE_BIN / "mldsa44-oracle-rust")], calldatas)


def go(calldatas) -> list[int]:
    return _lines_oracle([str(ORACLE_BIN / "mldsa44-oracle-go")], calldatas)


def dpy_one(cd: bytes) -> int:
    if len(cd) < HEADER:
        return 0
    try:
        return int(bool(ML_DSA_44.verify(cd[:PK_LEN], cd[HEADER:], cd[PK_LEN:HEADER])))
    except Exception:  # malformed encodings may raise inside dilithium-py
        return 0


def dpy(calldatas) -> list[int]:
    return [dpy_one(cd) for cd in calldatas]


ORACLES = {"lean": lean_spec, "rust": rust, "go": go, "dpy": dpy}


def repeated_hint_index(cd: bytes) -> bool:
    """The hint encoding is well formed except for a repeated index inside a
    row (non-decreasing, not strictly increasing): the one input class on
    which dilithium-py is known to diverge from FIPS 204 Algorithm 21."""
    if len(cd) < HEADER:
        return False
    h = cd[PK_LEN + HINT_OFF:HEADER]
    counts = list(h[OMEGA:])
    prev, repeated = 0, False
    for c in counts:
        if c < prev or c > OMEGA:
            return False
        row = h[prev:c]
        if any(row[i] < row[i - 1] for i in range(1, len(row))):
            return False
        repeated |= any(row[i] == row[i - 1] for i in range(1, len(row)))
        prev = c
    return repeated and not any(h[prev:OMEGA])


# ── Lean-semantics execution of the frozen bytecode ────────────────────────

def _code_tag() -> str:
    return hashlib.sha256(HEX.read_bytes()).hexdigest()[:16]


def _key(cd: bytes) -> str:
    return hashlib.sha256(cd).hexdigest()


def lean_evm(calldatas, jobs: int = 8, log=print) -> list[tuple[int, str, str]]:
    """(gas, halt, returndata hex) per calldata from `mldsa44tool run-file`."""
    CACHE.mkdir(parents=True, exist_ok=True)
    cache_path = CACHE / f"leanevm-{_code_tag()}.tsv"
    cache: dict[str, tuple[int, str, str]] = {}
    if cache_path.exists():
        for line in cache_path.read_text().splitlines():
            k, g, halt, ret = line.split("\t")
            cache[k] = (int(g), halt, ret)
    todo = sorted({_key(cd): cd for cd in calldatas if _key(cd) not in cache}.values(),
                  key=len, reverse=True)
    if todo:
        log(f"lean-evm: executing {len(todo)} calldata in the Lean semantics ({jobs} jobs)")
        shards = [todo[i::jobs] for i in range(jobs)]

        def run(idx_shard):
            idx, shard = idx_shard
            path = CACHE / f"run_shard_{os.getpid()}_{idx}.txt"
            path.write_text("".join(hexline(cd) + "\n" for cd in shard))
            res = subprocess.run([str(TOOL), "run-file", str(HEX), str(path)], cwd=ROOT,
                                 env=LEAN_ENV, check=True, capture_output=True, text=True)
            path.unlink()
            rows = res.stdout.splitlines()
            assert len(rows) == len(shard)
            out = []
            for cd, row in zip(shard, rows):
                size, gas, halt, ret = row.split("\t")
                assert int(size) == len(cd)
                out.append((_key(cd), (int(gas), halt, ret)))
            return out

        with ThreadPoolExecutor(jobs) as pool, cache_path.open("a") as f:
            for result in pool.map(run, [(i, s) for i, s in enumerate(shards) if s]):
                for k, v in result:
                    cache[k] = v
                    f.write(f"{k}\t{v[0]}\t{v[1]}\t{v[2]}\n")
    return [cache[_key(cd)] for cd in calldatas]


# ── fixture construction ───────────────────────────────────────────────────

WORD = {0: "00" * 32, 1: "00" * 31 + "01"}


def check_cases(cases, jobs: int = 8, log=print):
    """`cases`: list of (calldata, category, note, generator_expectation|None).

    Runs every oracle and the Lean-semantics execution, returning per-case
    records and the list of disagreements (known dilithium-py divergences are
    tallied separately, not reported as disagreements)."""
    cds = [c[0] for c in cases]
    verdicts = {}
    for name, fn in ORACLES.items():
        log(f"oracle {name}: {len(cds)} cases")
        verdicts[name] = fn(cds)
    evm = lean_evm(cds, jobs=jobs, log=log)
    sched = lean_schedule(len(cd) for cd in cds)
    records, problems, known = [], [], 0
    for i, (cd, cat, note, gen) in enumerate(cases):
        v = {name: verdicts[name][i] for name in ORACLES}
        gas, halt, ret = evm[i]
        lean = v["lean"]
        issues = []
        for name in ("rust", "go"):
            if v[name] != lean:
                issues.append(f"{name}={v[name]}")
        if v["dpy"] != lean:
            if v["dpy"] == 1 and lean == 0 and repeated_hint_index(cd):
                known += 1
            else:
                issues.append(f"dpy={v['dpy']}")
        if gen is not None and gen != lean:
            issues.append(f"generator={gen}")
        if halt != "returned" or ret != WORD[lean]:
            issues.append(f"lean-evm halt={halt} ret={ret}")
        if schedule(len(cd)) != sched[len(cd)]:
            issues.append("closed-form schedule != Lean schedule")
        if gas > sched[len(cd)]:
            issues.append(f"lean-evm gas {gas} > schedule {sched[len(cd)]}")
        rec = dict(cd=cd, cat=cat, note=note, expected=lean, gas=gas, schedule=sched[len(cd)],
                   verdicts=v)
        records.append(rec)
        if issues:
            problems.append((rec, issues))
    return records, problems, known


def write_fixture(path: Path, records) -> None:
    """One line per case: `calldata expected leanGas schedule category note`."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        for r in records:
            note = r["note"].replace(" ", "_") or "-"
            f.write(f"{hexline(r['cd'])} {r['expected']} {r['gas']} {r['schedule']} {r['cat']} {note}\n")


def write_problems(path: Path, problems) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        for rec, issues in problems:
            v = rec["verdicts"]
            f.write(f"{hexline(rec['cd'])} lean={v['lean']} rust={v['rust']} go={v['go']} dpy={v['dpy']} "
                    f"cat={rec['cat']} note={rec['note'].replace(' ', '_')} issues={';'.join(issues)}\n")
