# Kahn–Kalai project path migration

The Kahn–Kalai project was moved into `Kahn-Kalai/` on 2026-10-02. From the repository root, enter `Kahn-Kalai/` before running Lake. Within the project, Lean module names, dependency paths, and verification paths retain their original layout.

[Collection home](../README.md) · [Project README](README.md) · [Pre-migration repository snapshot](https://github.com/Mephisto17/talagrand-lean-verifications/tree/9c5ea6d3c242de6c0d853b0298a093f7df1b4444)

## Path map

Paths in the first column are relative to the former repository root. Every link in the second column points to the current file or directory.

| Previous path | Current path |
| --- | --- |
| `Audit.lean` | [Kahn-Kalai/Audit.lean](Audit.lean) |
| `KahnKalai.lean` | [Kahn-Kalai/KahnKalai.lean](KahnKalai.lean) |
| `KahnKalaiVerified.lean` | [Kahn-Kalai/KahnKalaiVerified.lean](KahnKalaiVerified.lean) |
| `Paper.lean` | [Kahn-Kalai/Paper.lean](Paper.lean) |
| `Solution.lean` | [Kahn-Kalai/Solution.lean](Solution.lean) |
| `lakefile.toml` | [Kahn-Kalai/lakefile.toml](lakefile.toml) |
| `lake-manifest.json` | [Kahn-Kalai/lake-manifest.json](lake-manifest.json) |
| `lean-toolchain` | [Kahn-Kalai/lean-toolchain](lean-toolchain) |
| `verify.sh` | [Kahn-Kalai/verify.sh](verify.sh) |
| `LICENSE` | [Kahn-Kalai/LICENSE](LICENSE) |
| `KahnKalai/` | [Kahn-Kalai/KahnKalai/](KahnKalai/) |
| `KahnKalai/Basic.lean` | [Kahn-Kalai/KahnKalai/Basic.lean](KahnKalai/Basic.lean) |
| `KahnKalai/Cost.lean` | [Kahn-Kalai/KahnKalai/Cost.lean](KahnKalai/Cost.lean) |
| `KahnKalai/Covering.lean` | [Kahn-Kalai/KahnKalai/Covering.lean](KahnKalai/Covering.lean) |
| `KahnKalai/DoubleCount.lean` | [Kahn-Kalai/KahnKalai/DoubleCount.lean](KahnKalai/DoubleCount.lean) |
| `KahnKalai/Numeric.lean` | [Kahn-Kalai/KahnKalai/Numeric.lean](KahnKalai/Numeric.lean) |
| `KahnKalai/ParkPham.lean` | [Kahn-Kalai/KahnKalai/ParkPham.lean](KahnKalai/ParkPham.lean) |
| `verification/` | [Kahn-Kalai/verification/](verification/) |
| `verification/RESULT.txt` | [Kahn-Kalai/verification/RESULT.txt](verification/RESULT.txt) |
| `verification/axioms.txt` | [Kahn-Kalai/verification/axioms.txt](verification/axioms.txt) |
| `verification/build.log` | [Kahn-Kalai/verification/build.log](verification/build.log) |
| `verification/lean-version.txt` | [Kahn-Kalai/verification/lean-version.txt](verification/lean-version.txt) |
| `verification/sha256.json` | [Kahn-Kalai/verification/sha256.json](verification/sha256.json) |
| `verification/standalone.log` | [Kahn-Kalai/verification/standalone.log](verification/standalone.log) |
| Original Kahn–Kalai project `README.md` | [Kahn-Kalai/README.md](README.md) |

The repository-root [README.md](../README.md) remains the collection overview. The original detailed Kahn–Kalai README from the supplied verification package is restored here, including its full proof-scope explanation and attribution.

## Updating URLs and commands

For current Kahn–Kalai file links, insert `Kahn-Kalai/` after `/blob/main/`. For directory links, insert it after `/tree/main/`. For raw links, add the same directory after the branch name, for example `/raw/refs/heads/main/Kahn-Kalai/…` on GitHub or `/main/Kahn-Kalai/…` on raw.githubusercontent.com. Root README links remain links to the collection overview; use `Kahn-Kalai/README.md` for the theorem documentation.

GitHub does not offer repository-controlled redirects for moved file URLs. An old `main` path can return 404; external bookmarks must use the new path. Existing commit-pinned links keep their historical meaning. To access a file at its old path, replace `main` with the pre-migration commit `9c5ea6d3c242de6c0d853b0298a093f7df1b4444`, for example this [historical Audit.lean](https://github.com/Mephisto17/talagrand-lean-verifications/blob/9c5ea6d3c242de6c0d853b0298a093f7df1b4444/Audit.lean).

From the repository root:

```sh
cd Kahn-Kalai
lake exe cache get
bash verify.sh
```

`bash verify.sh` works even when the script's executable bit was not preserved by a browser upload. The script resolves its own directory before invoking Lake. Alternatively, check the standalone file from this project directory with `lake env lean KahnKalaiVerified.lean`.

## Source and verification compatibility

The internal `KahnKalai/` module directory remains named `KahnKalai`; changing the outer project directory does not require editing Lean imports or declarations. All original proof sources, toolchain/dependency pins, scripts, and supplied verification records retain their content.

Entries in [verification/sha256.json](verification/sha256.json) are relative to this project directory, `Kahn-Kalai/`. They therefore continue to resolve after the move, including the entry for the restored original project README. The root collection README and this new migration guide are documentation outside the original checksum set. The saved build logs document the supplied verification run, not a new compilation performed during this migration.
