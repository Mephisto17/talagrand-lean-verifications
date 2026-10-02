#!/usr/bin/env python3
"""Generate the self-contained Mathlib-only version of the proofs."""
from pathlib import Path

root = Path(__file__).resolve().parent.parent
modules = ['Basic', 'Fourier', 'Extrapolation', 'Energy', 'FangWang', 'Logarithmic',
           'Certificates', 'Unions', 'Li', 'Main']
header = '''import Mathlib

/-!
# Complete Lean proofs of five Talagrand conjectures

Conjectures 9.1, 7.12, 7.3: alpha = 1/2.
Conjecture 7.9: every 0 < alpha <= (sqrt(5)-1)/2, by Fang--Wang's direct proof.
Conjecture 7.2: q = 3, with the original fractional-cover cost <= 1/2.
Li's stronger two-union results: no p-spread law at density >= 1/2;
an explicit weak p-smallness certificate at density >= 2/3.
Includes Li Theorem 1.9 and Fang--Wang Theorem 1.2 with their exact parameters
(arXiv:2609.08967v1 and arXiv:2609.18458v1, respectively).
Also proves Theorem 2.1 of Park--Talagrand, arXiv:2609.33644v1.

Main names are TalagrandConjectures.conjecture_9_1, conjecture_7_12,
conjecture_7_9, conjecture_7_3, conjecture_7_2; all supporting lemmas are proved.

Conjecture 9.1 is interpreted consistently with formula (9.2): the printed
up-class formula (9.1) needs a minus sign on its right. The explicit up-class
and multiplicative forms are provided below.
For 7.12 we use displayed formula (7.13), whose empty-set kernel is 1.
The inconsistent adjacent convention h(empty,J)=0 is not used.

Lean 4.32.0; Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997.
No proof placeholders or custom axioms. Run in the supplied Lake project:
  lake env lean TalagrandFiveConjectures.lean
This file imports only Mathlib; do not combine it with the modular library,
which intentionally defines the same names.
-/
'''
parts = [header]
for module in modules:
    source = (root/'TalagrandConjectures'/f'{module}.lean').read_text()
    lines = [line for line in source.splitlines() if not line.startswith('import ')]
    parts.append(f'\n/-! ## {module} -/\n\n' + '\n'.join(lines).strip() + '\n')
audit = (root/'Audit.lean').read_text()
parts.append('\n'+'\n'.join(line for line in audit.splitlines() if not line.startswith('import ')))
output = root/'TalagrandFiveConjectures.lean'
output.write_text('\n'.join(parts)+'\n')
print(f'Generated {output.name}: {len(output.read_text().splitlines())} lines')
