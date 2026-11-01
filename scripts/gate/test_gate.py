#!/usr/bin/env python3
"""Regression tests for the proof-preservation gate.

    python3 scripts/gate/test_gate.py            # all (builds small Lean fixtures, ~2 min)
    python3 scripts/gate/test_gate.py -k Compare # report logic only (no Lean)

The fixture tests build a tiny Lean-core package per variant, run the gate's
own extractor and replayer on it, and feed the snapshots to `gate.compare`.
Each case is a change the gate must catch (or must tolerate).
"""
from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate  # noqa: E402

BASE_FILES = {
    "lakefile.toml": 'name = "fx"\ndefaultTargets = ["Fx"]\n\n[[lean_lib]]\nname = "Fx"\n',
    "Fx.lean": "import Fx.A\nimport Fx.B\n",
    "Fx/A.lean": """
def f (n : Nat) : Nat := n + 1
def g (n : Nat) : Nat := n * 2
def bytes : ByteArray := ByteArray.mk #[1, 2, 3]
theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n
theorem headline : 0 < f 0 := f_pos 0
macro "my_tac" : tactic => `(tactic| decide)
private theorem priv : 1 + 1 = 2 := rfl
structure S where
  a : Nat
  b : Nat
def s0 : S := ⟨0, 1⟩
theorem s0_b : s0.b = 1 := rfl
private def pd : Nat := 1
theorem pd_eq : pd = 1 := rfl
""",
    "Fx/B.lean": """import Fx.A
theorem uses_f : f 0 = 1 := rfl
theorem uses_tac : 2 < 3 := by my_tac
theorem g.proof_1 : 2 + 2 = 4 := rfl
""",
}

LEAN_TESTS = "--fast" not in sys.argv


def build_fixture(root: Path, files: dict[str, str]) -> None:
    root.mkdir(parents=True)
    for p, txt in files.items():
        (root / p).parent.mkdir(parents=True, exist_ok=True)
        (root / p).write_text(txt)
    shutil.copy(gate.ROOT / "lean-toolchain", root / "lean-toolchain")
    p = subprocess.run(["lake", "build"], cwd=root, env=gate.lean_env(), capture_output=True)
    if p.returncode != 0:
        raise AssertionError(f"fixture build failed:\n{p.stdout.decode()[-3000:]}")


def snap(root: Path, label: str, replay: bool = False) -> gate.Snap:
    """The extractor and replayer on a built fixture (the parts of `gate.snapshot` that
    decide meaning, without git, generators or caches)."""
    env = gate.lean_env()
    exe = gate.tools(env)
    out, bout = root / "extract.tsv", root / "bytes.tsv"
    subprocess.run(["lake", "env", str(exe / "gate_extract"), "--roots", "Fx", "--build-dir", str(root / ".lake" / "build"),
                    "--allowed", ",".join(gate.ALLOWED_AXIOMS), "--headline", "headline", "--out", str(out)],
                   cwd=root, env=env, check=True, capture_output=True)
    subprocess.run(["lake", "env", str(exe / "gate_extract"), "--mode", "bytes", "--roots", "Fx",
                    "--bytecode", "bytes", "--out", str(bout)], cwd=root, env=env, check=True, capture_output=True)
    lines = out.read_text().splitlines() + bout.read_text().splitlines()
    lines = [l for l in lines if not l.startswith("P\t")]
    lines = [f"R\tlabel\t{label}", "R\tgate\tk", "R\ttoolchain\tt", "R\tlean\tg", "R\tmanifest\tm"] + lines
    if replay:
        mods = root / "mods.txt"
        mods.write_text("\n".join(l.split("\t")[2] for l in lines if l.startswith("M\t")) + "\n")
        p = subprocess.run(["lake", "env", str(exe / "gate_replay"), "-j", "2", str(mods)], cwd=root,
                           env=env, capture_output=True)
        lines.append(f"K\tkernel replay\t{'ok' if p.returncode == 0 else 'fail'}\t-")
    else:
        lines.append("K\tkernel replay\tok\t-")
    return gate.Snap(lines)


def cmp(b, h, **kw):
    kw.setdefault("headlines", ["headline"])
    kw.setdefault("bytecodes", {"bytes": None})
    return gate.compare(b, h, **kw)


@unittest.skipUnless(LEAN_TESTS, "--fast")
class Fixture(unittest.TestCase):
    """Each variant edits one file of BASE_FILES."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="gate-test-"))
        build_fixture(cls.tmp / "base", BASE_FILES)
        cls.base = snap(cls.tmp / "base", "base", replay=True)
        cls.n = 0

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def variant(self, edits: dict[str, str], replay=False) -> gate.Snap:
        type(self).n += 1
        d = self.tmp / f"v{self.n}"
        files = dict(BASE_FILES)
        for path, (old, new) in edits.items():
            assert old in files[path], old
            files[path] = files[path].replace(old, new)
        build_fixture(d, files)
        return snap(d, d.name, replay=replay)

    def assertFails(self, head, needle, **kw):
        fails, out = cmp(self.base, head, **kw)
        self.assertTrue(any(needle in f for f in fails), "\n".join(out))
        return out

    def assertPasses(self, head, **kw):
        fails, out = cmp(self.base, head, **kw)
        self.assertEqual(fails, [], "\n".join(out))
        return out

    def test_identical_passes(self):
        out = self.assertPasses(self.base)
        self.assertIn("GATE PASSED", "\n".join(out))

    def test_proof_change_passes(self):
        self.assertPasses(self.variant({"Fx/A.lean": ("Nat.succ_pos n", "Nat.zero_lt_succ n")}))

    def test_weakened_statement(self):
        out = self.assertFails(self.variant({"Fx/A.lean": (
            "theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n\ntheorem headline : 0 < f 0 := f_pos 0",
            "theorem f_pos (n : Nat) : 0 ≤ f n := Nat.zero_le _\ntheorem headline : 0 < f 0 := Nat.succ_pos 0")}),
            "changed")
        self.assertIn("f_pos: statement (edited)", "\n".join(out))

    def test_definition_used_by_statement(self):
        out = self.assertFails(self.variant({"Fx/A.lean": ("n + 1", "n.succ")}), "changed")
        text = "\n".join(out)
        self.assertIn("f: definition body (edited)", text)
        self.assertIn("f_pos: statement (via a dependency)", text)

    def test_structure_field_change(self):
        self.assertFails(self.variant({"Fx/A.lean": ("  b : Nat\n", "  b : Int\n")}), "changed")

    def test_unreferenced_bodies_pass(self):
        out = self.assertPasses(self.variant({"Fx/A.lean": ("n * 2", "n * 3")}))
        self.assertIn("no theorem statement depends on", "\n".join(out))
        self.assertPasses(self.variant({"Fx/A.lean": ("`(tactic| decide)", "`(tactic| (first | decide | rfl))")}))

    def test_new_allowed_axiom(self):
        # the clifv case: a theorem newly depends on an allowed axiom
        out = self.assertFails(self.variant({"Fx/A.lean": (
            "theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n",
            "theorem f_pos (n : Nat) : 0 < f n := (Classical.em True).elim (fun _ => Nat.succ_pos n) (fun _ => Nat.succ_pos n)")}),
            "changed")
        self.assertIn("f_pos: axioms - -> propext,Classical.choice,Quot.sound", "\n".join(out))

    def test_axioms_agree_with_print_axioms(self):
        # the extractor's copy of `CollectAxioms.collect` (no extension lookup) must give
        # Lean's own `#print axioms` answer
        d = self.tmp / "base"
        names = [v["name"] for v in self.base.consts.values() if v["aux"] == "0"]
        (d / "Ax.lean").write_text("import Fx\n" + "".join(f"#print axioms {n}\n" for n in names
                                                          if not n.startswith("_private")))
        p = subprocess.run(["lake", "env", "lean", "Ax.lean"], cwd=d, env=gate.lean_env(), capture_output=True)
        lean = {}
        for m in __import__("re").finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)",
                                           p.stdout.decode()):
            lean[m.group(1)] = ",".join(sorted(a.strip() for a in (m.group(2) or "").split(",") if a.strip()))
        self.assertGreater(len(lean), 10, p.stdout.decode()[-2000:])
        for v in self.base.consts.values():
            if v["name"] in lean:
                mine = ",".join(sorted(a for a in v["axioms"].split(",") if a != "-"))
                self.assertEqual(mine, lean[v["name"]], v["name"])

    def test_sorry(self):
        self.assertFails(self.variant({"Fx/B.lean": ("theorem uses_f : f 0 = 1 := rfl", "theorem uses_f : f 0 = 1 := sorry")}),
                         "axiom policy")

    def test_native_decide(self):
        # v4.33 `native_decide` adds an auxiliary axiom `<thm>._native.native_decide.ax_*`
        out = self.assertFails(self.variant({"Fx/B.lean": ("by my_tac", "by native_decide")}), "axiom policy")
        self.assertIn("X uses_tac uses_tac._native.native_decide.ax_", "\n".join(out))

    def test_axiom_declaration(self):
        self.assertFails(self.variant({"Fx/B.lean": ("theorem uses_f", "axiom cheat : f 0 = 1\ntheorem uses_f'")}),
                         "axiom policy")

    def test_move_needs_flag(self):
        v = self.variant({"Fx/A.lean": ("private theorem priv : 1 + 1 = 2 := rfl\n", ""),
                          "Fx/B.lean": ("import Fx.A\n", "import Fx.A\nprivate theorem priv : 1 + 1 = 2 := rfl\ntheorem f_pos' : True := trivial\n")})
        self.assertFails(v, "moved")
        out = self.assertPasses(v, allow_moves=True)
        self.assertIn("added", "\n".join(out))

    def test_user_theorem_with_aux_looking_name(self):
        # `proof_1` names are normally elaborator output and not compared by name, but a
        # theorem written in the source is compared whatever it is called
        out = self.assertFails(self.variant({"Fx/B.lean": ("theorem g.proof_1 : 2 + 2 = 4 := rfl",
                                                            "theorem g.proof_1 : 2 + 2 = 2 + 2 := rfl")}),
                               "changed")
        self.assertIn("g.proof_1: statement (edited)", "\n".join(out))

    def test_private_move_is_a_move(self):
        # a private definition mentioned by a statement moves with it: digests use user names
        v = self.variant({"Fx/A.lean": ("private def pd : Nat := 1\ntheorem pd_eq : pd = 1 := rfl\n", ""),
                          "Fx/B.lean": ("import Fx.A\n", "import Fx.A\nprivate def pd : Nat := 1\ntheorem pd_eq : pd = 1 := rfl\n")})
        self.assertFails(v, "moved")
        self.assertPasses(v, allow_moves=True)

    def test_control_character_in_name(self):
        # a tab in a «name» could forge snapshot fields; it is escaped and rejected
        v = self.variant({"Fx/B.lean": ("theorem uses_f", "def «zz\tC\tf_pos\nC» : Nat := 0\ntheorem uses_f")})
        self.assertEqual(v.errors, [])
        self.assertFails(v, "axiom policy")

    def test_removed(self):
        self.assertFails(self.variant({"Fx/B.lean": ("theorem uses_f : f 0 = 1 := rfl\n", "")}), "removed")

    def test_headline_missing(self):
        self.assertFails(self.variant({"Fx/A.lean": ("theorem headline : 0 < f 0 := f_pos 0\n", "")}), "headline")

    def test_bytecode_literal(self):
        self.assertFails(self.variant({"Fx/A.lean": ("#[1, 2, 3]", "#[1, 2, 4]")}), "bytecode literals differ")

    def test_skip_kernel_tc_caught_by_replay(self):
        v = self.variant({"Fx/B.lean": ("import Fx.A\n", """import Fx.A
import Lean
open Lean in
set_option debug.skipKernelTC true in
#eval show CoreM Unit from addDecl (.thmDecl
  { name := `bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
""")}, replay=True)
        self.assertFails(v, "kernel replay")


@unittest.skipUnless(LEAN_TESTS, "--fast")
class Snapshot(unittest.TestCase):
    """`gate.py check` end to end on a fixture git repository: worktree, builds, caches."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="gate-snap-"))
        cls.repo = repo = cls.tmp / "repo"
        files = dict(BASE_FILES, **{".gitignore": "/.lake\n", "bytes.hex": "010203\n"})
        build_fixture(repo, files)
        (repo / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
        cls.saved = {k: getattr(gate, k) for k in ("ROOT", "WORK", "WT", "GENERATORS", "EXES", "FROZEN",
                                                     "HEADLINES", "BYTECODES")}
        gate.ROOT, gate.WORK = repo, repo / ".lake" / "gate"
        gate.WT = gate.WORK / "wt"
        gate.GENERATORS, gate.EXES, gate.FROZEN = [], [], ["*.hex"]
        gate.HEADLINES, gate.BYTECODES = ["headline"], {"bytes": "bytes.hex"}
        cls.g("init", "-q")
        cls.commit("base")
        cls.base = cls.g("rev-parse", "HEAD")

    @classmethod
    def tearDownClass(cls):
        for k, v in cls.saved.items():
            setattr(gate, k, v)
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @classmethod
    def g(cls, *args):
        return subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "-c", "commit.gpgsign=false",
                               *args], cwd=cls.repo, check=True, capture_output=True).stdout.decode().strip()

    @classmethod
    def commit(cls, msg):
        cls.g("add", "-A")
        cls.g("commit", "-qm", msg, "--allow-empty")
        return cls.g("rev-parse", "HEAD")

    def head(self, edits: dict[str, tuple[str, str]], new: dict[str, str] = {}):
        self.g("checkout", "-q", "--detach", self.base)
        for path, (old, rep) in edits.items():
            t = (self.repo / path).read_text()
            assert old in t, old
            (self.repo / path).write_text(t.replace(old, rep))
        for path, txt in new.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text(txt)
        sha = self.commit("head")
        self.g("checkout", "-q", "--detach", self.base)
        return sha

    def check(self, head, *flags):
        rep = self.tmp / "report.txt"
        code = gate.main(["check", self.base, head, "--jobs", "2", "--report", str(rep), *flags])
        return code, rep.read_text()

    def test_base_against_itself(self):
        code, text = self.check(self.base, "--bootstrap")
        self.assertEqual(code, 0, text)
        # without the flag: BASE has no scripts/gate/, so the running gate is not BASE's (rule 6)
        code, text = self.check(self.base)
        self.assertEqual(code, 1, text)
        self.assertIn("the running gate is not BASE's", text)
        # only BASE may be a snapshot file
        snapf = self.tmp / "base.tsv"
        gate.main(["snapshot", self.base, "-o", str(snapf), "--jobs", "2"])
        with self.assertRaises(SystemExit):
            gate.main(["check", self.base, str(snapf), "--bootstrap"])

    def test_lakefile_facets_cannot_hide_a_sorry(self):
        # `defaultFacets = []` makes `lake build` skip the library: the old .olean (no sorry)
        # must not be what gets extracted
        h = self.head({"lakefile.toml": ('name = "Fx"\n', 'name = "Fx"\ndefaultFacets = []\n'),
                       "Fx/B.lean": ("theorem uses_f : f 0 = 1 := rfl", "theorem uses_f : f 0 = 1 := sorry")})
        code, text = self.check(h, "--bootstrap", "--allow-lakefile-change")
        self.assertEqual(code, 1, text)
        self.assertIn("sorryAx", text)
        code, text = self.check(h, "--bootstrap")
        self.assertIn("lakefile.toml differs", text)

    SNEAKY = """import Lean
open Lean in
set_option debug.skipKernelTC true in
#eval show CoreM Unit from addDecl (.thmDecl
  { name := `bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
"""

    def test_module_name_that_is_not_an_identifier(self):
        # `Fx.«1A»` does not parse back with `String.toName`; locality is decided by .olean path
        h = self.head({"Fx.lean": ("import Fx.B\n", "import Fx.B\nimport Fx.«1A»\n")},
                      {"Fx/1A.lean": self.SNEAKY + "theorem one_a : f 0 = 1 := bogus.elim\n"
                       .replace("f 0", "(0 : Nat)").replace("= 1", "= 0")})
        code, text = self.check(h, "--bootstrap")
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL kernel replay", text)

    def test_injected_snapshot_lines(self):
        # a comment shaped like a port header, with tabs and newlines, in a file nothing builds;
        # the cached snapshot must read back exactly as written
        inj = "/- Ported from `x\nK\tkernel replay\tok\t-\nK\tzz\tok\tq` by `scripts/proofgen_port.py 65` ; -/\n"
        h = self.head({"Fx/B.lean": ("import Fx.A\n", self.SNEAKY.replace("import Lean\n", "import Fx.A\nimport Lean\n"))},
                      {"MlDsaOpt65/Notes.lean": inj})
        for _ in range(2):
            code, text = self.check(h, "--bootstrap")
            self.assertEqual(code, 1, text)
            self.assertIn("FAIL kernel replay", text)

    def test_tracked_build_outputs_refused(self):
        # committed .lake/ files (old .olean + a matching trace) would make Lake skip a rebuild
        self.g("checkout", "-q", "--detach", self.base)
        (self.repo / "Fx" / "B.lean").write_text((self.repo / "Fx" / "B.lean").read_text()
                                                .replace("f 0 = 1 := rfl", "f 0 = 1 := sorry"))
        self.g("add", "-A")
        self.g("add", "-f", ".lake/build/lib/lean/Fx/B.olean")
        h = self.commit("tracked olean")
        self.g("checkout", "-q", "--detach", self.base)
        with self.assertRaises(SystemExit) as e:
            self.check(h, "--bootstrap")
        self.assertIn(".lake/", str(e.exception))

    def test_unsupported_lakefile_settings(self):
        h = self.head({"lakefile.toml": ('name = "fx"\n', 'name = "fx"\nbuildDir = "out"\n')})
        with self.assertRaises(SystemExit):
            self.check(h, "--bootstrap", "--allow-lakefile-change")

    def test_extra_root_is_replayed(self):
        # a module outside the library-name prefix, added as a root, that adds an unchecked
        # declaration through `debug.skipKernelTC`
        sneaky = self.SNEAKY
        h = self.head({"lakefile.toml": ('name = "Fx"\n', 'name = "Fx"\nroots = ["Fx", "Sneaky"]\n')},
                      {"Sneaky.lean": sneaky})
        code, text = self.check(h, "--bootstrap", "--allow-lakefile-change")
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL kernel replay", text)


def lines(consts=(), checks=(), extra=()):
    out = ["R\tlabel\tx", "R\tgate\tk", "R\ttoolchain\tt", "R\tlean\tg", "R\tmanifest\tm",
           "K\tkernel replay\tok\t-",
           "H\theadline\ttheorem\tpropext", "B\tbytes\t3\t010203"]
    for c in consts:
        out.append("C\t" + "\t".join(c))
    out += [f"K\t{n}\t{s}\t-" for n, s in checks]
    return out + list(extra)


def const(name, kind="theorem", module="Fx.A", ct="1", full="1", axioms="propext", aux="0", rel="0", lt="1", lv="-"):
    return (name, name, kind, module, lt, ct, lv, "-", full, axioms, aux, rel)


class Compare(unittest.TestCase):
    """Report logic on hand-written snapshots."""

    def run_cmp(self, b, h, **kw):
        return cmp(gate.Snap(b), gate.Snap(h), **kw)

    def test_check_regression(self):
        fails, _ = self.run_cmp(lines(checks=[("gen x", "ok")]), lines(checks=[("gen x", "fail")]))
        self.assertTrue(fails)
        # a check missing on HEAD (e.g. --skip-generators) cannot pass
        fails, _ = self.run_cmp(lines(checks=[("gen x", "ok")]), lines())
        self.assertTrue(fails)
        fails, _ = self.run_cmp(lines(checks=[("gen x", "fail")]), lines(checks=[("gen x", "fail")]))
        self.assertFalse(fails)

    def test_missing_replay_fails(self):
        h = [l for l in lines() if not l.startswith("K\tkernel replay")]
        fails, _ = self.run_cmp(lines(), h)
        self.assertTrue(fails)

    def test_frozen(self):
        fails, _ = self.run_cmp(lines(extra=["F\ta.hex\t1"]), lines(extra=["F\ta.hex\t2"]))
        self.assertTrue(fails)
        fails, _ = self.run_cmp(lines(extra=["F\ta.hex\t1"]), lines())
        self.assertTrue(fails)

    def test_aux_ignored_by_name(self):
        fails, _ = self.run_cmp(lines([const("a._proof_1", aux="1")]), lines([const("a._proof_2", aux="1")]))
        self.assertFalse(fails)

    def test_toolchain(self):
        h = [l.replace("R\ttoolchain\tt", "R\ttoolchain\tu") for l in lines()]
        fails, _ = self.run_cmp(lines(), h)
        self.assertTrue(fails)

    def test_skipped_generators_never_pass(self):
        skipped = lines(checks=[("generators", "fail")])
        fails, _ = self.run_cmp(skipped, skipped)
        self.assertTrue(fails)

    def test_malformed_or_duplicate_lines(self):
        fails, _ = self.run_cmp(lines(), lines(extra=["C\tx\tonly-three-fields"]))
        self.assertTrue(fails)
        fails, _ = self.run_cmp(lines([const("a")]), lines([const("a"), const("a", ct="2")]))
        self.assertTrue(fails)

    def test_elan_toolchain_is_not_inherited(self):
        import os
        os.environ["ELAN_TOOLCHAIN"] = "bogus"
        try:
            self.assertNotIn("ELAN_TOOLCHAIN", gate.lean_env())
        finally:
            del os.environ["ELAN_TOOLCHAIN"]

    def test_gate_edit(self):
        fails, _ = self.run_cmp(lines(), lines(), gate_files=["scripts/gate/gate.py"])
        self.assertTrue(fails)
        fails, _ = self.run_cmp(lines(), lines(), gate_files=["scripts/gate/gate.py"], allow_gate_change=True)
        self.assertFalse(fails)


if __name__ == "__main__":
    argv = [a for a in sys.argv if a != "--fast"]
    unittest.main(argv=argv)
