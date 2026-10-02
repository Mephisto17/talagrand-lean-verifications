# Talagrand Lean Verifications

This repository collects Lean formalizations and verification artifacts for Talagrand-related theorems and conjectures. Each new result should be kept as a reproducible project with its source, build configuration, documentation, and verification records.

## Projects

### Kahn–Kalai conjecture

The first project is the Kahn–Kalai verification. Its original files are currently kept at the repository root for compatibility with the initial upload:

- [KahnKalaiVerified.lean](KahnKalaiVerified.lean): self-contained Lean source.
- [Paper.lean](Paper.lean): paper-specific statements and bridges.
- [KahnKalai/](KahnKalai/): modular source files.
- [verification/](verification/): compiler, build, axiom, and checksum records.

The project proves the stated quantitative bound through the Tran–Vu route and documents its exact scope in the source comments and verification files. The upstream formalization and Apache-2.0 attribution are recorded in the project materials.

### Talagrand / Park–Pham Theorem 1.2

The second project is organized under [talagrand-theorem-1-2/](talagrand-theorem-1-2/). It contains a complete Lean 4.32.0 project for the corrected positive-finite-expectation form of Theorem 1.2, with the explicit constant L = 2048.

- [TalagrandTheorem12.lean](talagrand-theorem-1-2/TalagrandTheorem12.lean): standalone theorem file.
- [TalagrandSelector/](talagrand-theorem-1-2/TalagrandSelector/): modular development.
- [verification/](talagrand-theorem-1-2/verification/): build logs, result data, axiom report, and source hashes.
- [README](talagrand-theorem-1-2/README.md): theorem scope and reproduction instructions.

The theorem file and project README describe the hypotheses precisely, including nonnegative weights, positive parameter, positive extended expectation, and finite extended expectation.

## Repository layout

New formalizations should use one top-level directory per theorem or conjecture, for example:

~~~text
talagrand-theorem-1-2/
  source files and Lean configuration
  TalagrandSelector/
  verification/
~~~

The root Kahn–Kalai files are retained as the initial project snapshot. A later cleanup may move them under a dedicated directory once compatibility with existing links is no longer needed.

## Reproduce the projects

Install the Lean toolchain required by the project and make sure lake is available.

For the Kahn–Kalai project, from the repository root run:

~~~sh
lake exe cache get
./verify.sh
~~~

For Theorem 1.2, run:

~~~sh
cd talagrand-theorem-1-2
lake build
lake env lean TalagrandTheorem12.lean
~~~

Each project pins its Lean and mathlib versions in its lean-toolchain, lakefile.toml, and lake-manifest.json. The recorded logs under each verification/ directory are the results supplied with that project; rerun the commands when changing the source.

## Add a future result

Clone the repository once, create a directory named after the theorem, and keep the source and its verification data together:

~~~sh
git clone https://github.com/Mephisto17/talagrand-lean-verifications.git
cd talagrand-lean-verifications
mkdir talagrand-new-result
# add Lean files, README, lake configuration, and verification/
git add .
git commit -m "Add Talagrand new result"
git push
~~~

For a small change, the GitHub web interface also works: open the target project directory, choose Add file then Upload files, upload the files, write a commit message, and commit directly to main.

## Licenses and attribution

Keep the license and copyright notices supplied with each formalization. The Kahn–Kalai materials include Apache-2.0 text and attribution to the upstream formalization. For each future project, record its mathematical sources, code sources, exact revisions, theorem scope, and permitted axioms in that project's README and verification directory.
