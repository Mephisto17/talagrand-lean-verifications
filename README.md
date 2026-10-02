# Talagrand Lean Verifications

This repository collects Lean formalizations and verification artifacts for Talagrand-related theorems and conjectures. Each result lives in an independent project directory with its sources, dependency pins, mathematical scope, and verification records.

## Projects

### Kahn–Kalai conjecture

The complete project is in **[Kahn-Kalai/](Kahn-Kalai/)**.

- [Project README and exact scope](Kahn-Kalai/README.md)
- [KahnKalaiVerified.lean](Kahn-Kalai/KahnKalaiVerified.lean): standalone source, apart from mathlib.
- [Paper.lean](Kahn-Kalai/Paper.lean): paper-specific statements and bridges.
- [KahnKalai/](Kahn-Kalai/KahnKalai/): modular source files.
- [verification/](Kahn-Kalai/verification/): supplied build logs, axiom reports, and checksums.
- [LICENSE](Kahn-Kalai/LICENSE): Apache-2.0 license text.

The quantitative bound is proved through the Tran–Vu route, using Dan Clemens Posch's upstream formalization. Several Park–Pham proof steps are also formalized; the complete original randomized Park–Pham argument is not transcribed line by line. See the project README for the precise statements, attribution, and limitations.

### Talagrand / Park–Pham Conjecture 5.7

The complete project is in **[talagrand-conjecture-5-7/](talagrand-conjecture-5-7/)**. It formalizes the corrected positive-finite-expectation version of Conjecture 5.7 with the explicit constant L = 2048.

- [Project README and exact hypotheses](talagrand-conjecture-5-7/README.md)
- [TalagrandConjecture57.lean](talagrand-conjecture-5-7/TalagrandConjecture57.lean): standalone theorem file.
- [TalagrandSelector/](talagrand-conjecture-5-7/TalagrandSelector/): modular development.
- [verification/](talagrand-conjecture-5-7/verification/): supplied build logs, axiom reports, results, and source hashes.

The public theorem assumes a finite ground set, 0 < p < 1, nonnegative weights, and positive finite extended expectation. The weight collection may be infinite; attainment of the supremum is not assumed.

### Talagrand's five conjectures

The third project is [talagrand-five-conjectures/](talagrand-five-conjectures/). It contains complete Lean proofs for five Talagrand conjectures, together with supporting results by Li, Fang–Wang, and Park–Talagrand.

- [Project README and conjecture scope](talagrand-five-conjectures/README.md)
- [TalagrandFiveConjectures.lean](talagrand-five-conjectures/TalagrandFiveConjectures.lean): standalone source.
- [TalagrandConjectures/](talagrand-five-conjectures/TalagrandConjectures/): modular proofs.
- [verification/](talagrand-five-conjectures/verification/): build, axiom, result, source, and article records.

The project records the exact interpretation of Conjectures 9.1, 7.12, 7.9, 7.3, and 7.2 in its own README. Its theorem and supporting-result names are preserved as Lean declarations; the supplied verification reports document the proof dependencies.
## Repository layout

```text
talagrand-lean-verifications/
├── README.md
├── Kahn-Kalai/
│   ├── README.md
│   ├── MIGRATION.md
│   ├── LICENSE
│   ├── KahnKalaiVerified.lean
│   ├── KahnKalai.lean, Paper.lean, Solution.lean, Audit.lean
│   ├── KahnKalai/
│   ├── verification/
│   ├── lakefile.toml, lake-manifest.json, lean-toolchain
│   └── verify.sh
├── talagrand-conjecture-5-7/
└── talagrand-five-conjectures/
    ├── README.md
    ├── TalagrandConjecture57.lean, TalagrandSelector.lean, Audit.lean
    ├── TalagrandSelector/
    ├── verification/
    ├── scripts/
    └── lakefile.toml, lake-manifest.json, lean-toolchain
```

There is no shared Lake project at the repository root. Keep each result's dependencies and audit records within its own directory. The internal directory `Kahn-Kalai/KahnKalai/` retains the Lean module name `KahnKalai`, so existing `import KahnKalai...` declarations still work within that project.

## Reproduce the projects

Install Lean/Elan and Git. Each project's `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin its environment. Run the following blocks separately from the repository root.

Kahn–Kalai (Bash, including Git Bash or WSL on Windows; Python 3 is also used by the audit script):

```sh
cd Kahn-Kalai
lake exe cache get
bash verify.sh
```

Conjecture 5.7:

```sh
cd talagrand-conjecture-5-7
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean TalagrandConjecture57.lean
```

Five conjectures:

~~~sh
cd talagrand-five-conjectures
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean TalagrandFiveConjectures.lean
~~~

The standalone file and modular library in each project define the same names. Check them separately rather than importing both into one Lean file. The records under `verification/` are supplied build evidence; rerun the checks after editing proofs. The directory migration itself does not constitute a fresh Lean compilation.

## Path migration and existing links

All former root-level Kahn–Kalai project files and the old `KahnKalai/` and `verification/` directories now live under `Kahn-Kalai/`. The collection README remains here; the original Kahn–Kalai README is restored at [Kahn-Kalai/README.md](Kahn-Kalai/README.md).

See the **[complete old-to-new path map](Kahn-Kalai/MIGRATION.md)** for updated file links and a permanent link to the pre-migration snapshot. GitHub does not provide repository-controlled redirects for arbitrary moved file URLs. Update bookmarks or external references that use old `main` paths; links pinned to old commit IDs remain available through Git history.

## Add a future result

Create one top-level directory per theorem or conjecture. Include its own README, Lean sources, Lake configuration, toolchain pin, verification records, and applicable license/attribution information. Then add it to the project list above.

```sh
git clone https://github.com/Mephisto17/talagrand-lean-verifications.git
cd talagrand-lean-verifications
mkdir talagrand-new-result
# Add the complete project under talagrand-new-result/.
# Update this README with links and reproduction commands.
git add talagrand-new-result README.md
git commit -m "Add Talagrand new result"
git push
```

If already cloned, pull the latest changes before adding a result. In the GitHub web interface, open the target project directory before choosing **Add file → Upload files**, and preserve nested directories when uploading modules and reports.

## Licenses and attribution

The Kahn–Kalai license and upstream attribution are kept with that project in [Kahn-Kalai/LICENSE](Kahn-Kalai/LICENSE) and [Kahn-Kalai/README.md](Kahn-Kalai/README.md). Relocating that license does not change any existing license terms. Preserve all applicable licenses and copyright notices when adding future results, and record mathematical sources, code sources, exact revisions, theorem scope, and audited axioms in each project's documentation.
