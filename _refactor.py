import os, subprocess, glob

ROOT = 'FormalRV/PauliRotation'

# (old root-relative name, new root-relative name)
MOVES = [
    ('Semantics.lean',         'Semantics/Core.lean'),
    ('CommBridge.lean',        'Semantics/CommBridge.lean'),
    ('BasisAction.lean',       'Semantics/BasisAction.lean'),
    ('PauliPhase.lean',        'Semantics/PauliPhase.lean'),
    ('Compile.lean',           'Compiler/GateDictionary.lean'),
    ('GateBridge.lean',        'Compiler/GateBridge.lean'),
    ('CircuitCompile.lean',    'Compiler/CircuitCompile.lean'),
    ('QFTLadder.lean',         'Compiler/QFTLadder.lean'),
    ('SchedulerK.lean',        'Compiler/SchedulerK.lean'),
    ('Scheduler.lean',         'Compiler/Scheduler.lean'),
    ('Rules.lean',             'Compiler/Rules.lean'),
    ('PushRules.lean',         'Compiler/PushRules.lean'),
    ('Optimizer.lean',         'Compiler/Optimizer.lean'),
    ('Dictionary.lean',        'Correctness/SingleQubitRows.lean'),
    ('CircuitIdentities.lean', 'Correctness/CircuitIdentities.lean'),
    ('GateRows.lean',          'Correctness/GateRows.lean'),
    ('CCZRow.lean',            'Correctness/CCZRow.lean'),
    ('CCXRow.lean',            'Correctness/CCXRow.lean'),
    ('QFTRows.lean',           'Correctness/QFTRows.lean'),
    ('Assembly.lean',          'Correctness/Assembly.lean'),
    ('ShorEndToEnd.lean',      'Correctness/ShorEndToEnd.lean'),
]

def mod(rel):
    return 'FormalRV.PauliRotation.' + rel[:-5].replace('/', '.').replace('\\', '.')

# rename map, ordered: SchedulerK before Scheduler (prefix collision at same anchor)
RENAMES = [(mod(a), mod(b)) for a, b in MOVES]

os.makedirs(f'{ROOT}/Semantics', exist_ok=True)
os.makedirs(f'{ROOT}/Compiler', exist_ok=True)
os.makedirs(f'{ROOT}/Correctness', exist_ok=True)

for a, b in MOVES:
    subprocess.run(['git', 'mv', f'{ROOT}/{a}', f'{ROOT}/{b}'], check=True)
print('moved', len(MOVES))

# sweep every .lean file in the library for module-name updates
count = 0
for path in glob.glob('FormalRV/**/*.lean', recursive=True) + ['FormalRV.lean']:
    src = open(path, encoding='utf-8').read()
    out = src
    for old, new in RENAMES:
        out = out.replace(old, new)
    if out != src:
        open(path, 'w', encoding='utf-8').write(out)
        count += 1
print('rewired', count, 'files')
