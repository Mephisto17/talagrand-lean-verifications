#!/usr/bin/env python3
"""Rebuild the standalone Lean file from the verified modules."""
from pathlib import Path

root = Path(__file__).resolve().parent.parent
modules = [
    "Reduction", "Threshold", "Witness", "Bernoulli", "Counting",
    "Numeric", "CoverCost", "Main", "Extended",
]
header = '''import Mathlib

/-!
# Corrected Park--Pham Conjecture 5.7: complete proof

For an arbitrary collection of nonnegative weights on a finite ground set,
0 < p < 1 and 0 < E[Z] < infinity imply that {S | Z(S) >= 2048 * E[Z]}
is p-small.

Final theorem: TalagrandSelector.conjecture_5_7_finite_expectation.
The normalized bound is PROVED in this file, not assumed.
The proof adapts the clipped-threshold witness argument of
Bednorz--Martynek--Meller, arXiv:2212.14636v3, Section 3.1.
Target: Park--Pham, arXiv:2204.10309v2, Conjecture 5.7 with positive finite
expectation. No proof placeholders or custom axioms are used.

Lean 4.32.0; mathlib commit 81a5d257c8e410db227a6665ed08f64fea08e997.
Run within the supplied project: lake env lean TalagrandConjecture57.lean
This single file imports only Mathlib. Do not combine it with imports of
the modular TalagrandSelector library, which defines the same names.
-/
'''
parts = [header]
for module in modules:
    source = (root / "TalagrandSelector" / f"{module}.lean").read_text()
    lines = [line for line in source.splitlines()
             if not line.startswith("import ") and not line.startswith("#print axioms ")]
    parts.append(f"\n/-! ## {module} -/\n\n" + "\n".join(lines).strip() + "\n")
parts.append('''
set_option pp.fullNames true
#print axioms TalagrandSelector.normalized_selector_bound
#print axioms TalagrandSelector.conjecture_5_7_finite_expectation
''')
output = root / "TalagrandConjecture57.lean"
output.write_text("\n".join(parts))
print(f"Generated {output.name}: {len(output.read_text().splitlines())} lines")
