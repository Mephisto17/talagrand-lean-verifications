#!/usr/bin/env python3
"""Compile both deliverables and reject nonstandard axiom dependencies."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
out = root/'verification'
out.mkdir(exist_ok=True)
commands = [(['lean', '--version'], 'lean-version.txt'),
            (['lake', 'build'], 'project-build.log'),
            (['lake', 'env', 'lean', 'Audit.lean'], 'axioms.txt'),
            (['lake', 'env', 'lean', 'TalagrandFiveConjectures.lean'], 'standalone-build.log')]
results = []
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
expected = re.findall(r'^#print axioms (\S+)$', (root/'Audit.lean').read_text(), re.M)
if len(expected) != len(set(expected)) or not expected:
    raise SystemExit('Audit.lean must list distinct theorem names.')
passed = True
for command, log in commands:
    print('Running: '+' '.join(command), flush=True)
    with (out/log).open('w') as stream:
        run = subprocess.run(command, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
    results.append({'command': command, 'exit_code': run.returncode, 'log': log})
    print(f'Exit code: {run.returncode}', flush=True)
    text = (out/log).read_text()
    if run.returncode:
        print(text[-16000:])
        passed = False
        break
    if log in {'axioms.txt', 'standalone-build.log'}:
        reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
        valid = (len(reports) == len(expected)
                 and {name for name, _ in reports} == set(expected)
                 and all({a.strip() for a in report.split(',')} <= allowed
                         for _, report in reports))
        results[-1]['standard_axioms_only'] = valid
        results[-1]['theorems_checked'] = [name for name, _ in reports]
        print(f'Axiom audit: {len(reports)} reports, standard axioms only = {valid}', flush=True)
        if not valid:
            passed = False
            break
record = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'passed': passed and len(results) == len(commands), 'commands': results}
(out/'results.json').write_text(json.dumps(record, indent=2)+'\n')
if record['passed']:
    files = [root/'TalagrandFiveConjectures.lean', root/'TalagrandConjectures.lean',
             root/'Audit.lean', root/'lakefile.toml', root/'lake-manifest.json',
             root/'lean-toolchain', root/'README.md', root/'verification'/'source-articles.json']
    files += sorted((root/'TalagrandConjectures').glob('*.lean'))
    files += sorted((root/'scripts').glob('*.py'))
    hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (out/'source-sha256.json').write_text(json.dumps(hashes, indent=2)+'\n')
    print('All compilation and axiom checks passed.', flush=True)
sys.exit(0 if record['passed'] else 1)
