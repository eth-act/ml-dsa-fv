"""Generate isolated A/B inputs without changing production proof files."""
from pathlib import Path
import subprocess
import importlib.util

root = Path(__file__).resolve().parent.parent
out = Path('/tmp/reflect-sample')
out.mkdir(exist_ok=True)
spec = importlib.util.spec_from_file_location('artifact', root / 'scripts/proofgen_artifact.py')
artifact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(artifact)
# Only emit the new wrapper; do not regenerate unrelated artifact infrastructure.
(root / 'MlDsaOpt87/Infra/Reflect.lean').write_text(artifact.sub(artifact.REFLECT,
    {'NS': 'MlDsaOpt87', 'P': 'MlDsaOpt87.Proofs', 'TAC': 'opt87', 'N': '12299'}))
reference = artifact.sub(artifact.REFLECT,
    {'NS': 'MlDsa44.Proofs', 'P': 'MlDsa44.Proofs', 'TAC': 'evm', 'N': '3375'})
reference = reference.replace('MlDsa44.Proofs.Infra.tables',
    '(do return (← MlDsa44.Proofs.Infra.instrExprs, ← MlDsa44.Proofs.Infra.pcValues))')
# The reference artifact uses definitionally equal, independently named words/states.
reference = reference.replace('MlDsaOptCommon.callState,', 'MlDsaOptCommon.callState, MlDsa44.Proofs.callState, MlDsa44.Proofs.wd,')
(root / 'Scratch/ReferenceReflect.lean').write_text(reference)
samples = [
    ('Fix', 'MlDsaOpt44/Fn/Fix/Blocks.lean', 'opt44', 'MlDsaOpt44.Infra.Reflect'),
    ('Hint', 'MlDsaOpt87/Fn/Decode/HintBlocks.lean', 'opt87', 'MlDsaOpt87.Infra.Reflect'),
    ('Ginit', 'MlDsaOpt44/Fn/Sponge/Ginit.lean', 'opt44', 'MlDsaOpt44.Infra.Reflect'),
    ('Trabs', 'MlDsaOpt44/Fn/Sponge/Trabs.lean', 'opt44', 'MlDsaOpt44.Infra.Reflect'),
    ('Keccak', 'MlDsa44/Proofs/Fn/Keccak/Blocks2.lean', 'evm', 'Scratch.ReferenceReflect'),
]
for name, path, tactic, imp in samples:
    original = subprocess.check_output(['git', 'show', f'origin/master:{path}'], cwd=root, text=True)
    (out / f'{name}Base.lean').write_text(original)
    changed = original.replace(tactic + '_reach', tactic + '_rreach')
    if name == 'Ginit':
        finish = artifact.REFLECT.split('@TAC@_reflect_core\n')[1].split('           done)')[0]
        finish = finish.split('           all_goals first')[0]
        finish = artifact.sub(finish, {'P': 'MlDsaOpt44.Proofs'})
        finish = finish.replace('Nat.shiftRight_eq_div_pow, $extra,*]', '''Nat.shiftRight_eq_div_pow,
              Option.some.injEq, EvmSemantics.EVM.State.mk.injEq,
              EvmSemantics.SharedState.mk.injEq, EvmSemantics.MachineState.mk.injEq,
              List.cons.injEq, $extra,*]''')
        macro = '''
syntax "sample_rblock " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sample_rblock [$extra,*]) => `(tactic| (
      first
      | (opt44_reflect_core
FINISH
         all_goals try omega
         all_goals try (intro; trivial)
         all_goals try (solve | repeat' constructor))
      | opt44_block [$extra,*]))
'''.replace('FINISH', finish)
        changed = macro + changed.replace('opt44_block [', 'sample_rblock [')
        # Imports must precede the scratch macro.
        lines = changed.splitlines()
        imports = [line for line in lines if line.startswith('import ')]
        changed = '\n'.join(imports + [line for line in lines if not line.startswith('import ')])
    (out / f'{name}Reflect.lean').write_text(f'import {imp}\n' + changed)
