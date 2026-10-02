#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p verification
lean --version | tee verification/lean-version.txt
lake build 2>&1 | tee verification/build.log
lake env lean Audit.lean > verification/axioms.txt
cat verification/axioms.txt
python3 - <<'PY'
import re
from pathlib import Path
s = Path('verification/axioms.txt').read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", s)
expected = {
    'KahnKalai.covering_theorem', 'KahnKalai.park_pham',
    'ParkPhamPaper.exists_minimumFragment', 'ParkPhamPaper.equation_16',
    'ParkPhamPaper.fragmentPairs_card_le', 'ParkPhamPaper.weighted_fragmentPairs_bound',
    'ParkPhamPaper.proposition_2_3', 'ParkPhamPaper.success_of_cheap_cover',
    'ParkPhamPaper.theorem_1_1_explicit', 'ParkPhamPaper.theorem_1_1_increasing',
    'ParkPhamPaper.theorem_1_1',
}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert {name for name, _ in reports} == expected, 'Missing or unexpected axiom report'
for name, text in reports:
    axioms = {a.strip() for a in text.split(',') if a.strip()}
    assert axioms <= allowed, (name, axioms - allowed)
print('PASS: all audited theorems use only the standard three axioms.')
PY
if [[ -f KahnKalaiVerified.lean ]]; then
    lake env lean KahnKalaiVerified.lean > verification/standalone.log 2>&1
    cat verification/standalone.log
fi
