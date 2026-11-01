"""Copy the chunked tactic into scratch for a same-orb isolated comparison."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
ref = "51cbbb9ecf233ede7482f2861d5862f1eae9267d"
def get(path):
    return subprocess.check_output(["git", "show", f"{ref}:{path}"], cwd=root, text=True)

chunk = get("MlDsaOptCommon/Chunk.lean")
(root / "Scratch/BaselineChunk.lean").write_text(chunk)
block = get("MlDsaOpt44/Infra/Block.lean")
macro = block[block.index('syntax "opt44_block"'):].replace("opt44_block", "scratch_chunk_block")
body = get("MlDsaOpt44/Fn/Blk/BodyA.lean")
body = body.replace("  opt44_reach ", "  scratch_chunk_reach ")
reach = '''
syntax "scratch_chunk_reach " term:max " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| scratch_chunk_reach $path:term with [$extra:simpLemma,*]) => `(tactic| (
      refine MlDsaOpt44.Proofs.Infra.reach_block (by assumption) $path
        (by decide +kernel) ?_
      scratch_chunk_block [$extra,*]))
'''
imports, rest = body.split("/-!", 1)
(root / "Scratch/BodyAChunked.lean").write_text(
    imports + "import Scratch.BaselineChunk\n" + macro + reach + "/-!" + rest)
