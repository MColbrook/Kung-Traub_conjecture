# Verification

## Build and axiom dependencies

Use Python 3.11 or later, with `lake` on `PATH`. After obtaining the Mathlib cache as described in the [README](../README.md), run from the repository root:

```sh
python3 scripts/check_axioms.py
```

On Windows, `py -3` can be used in place of `python3`. The checker first confirms the Lean version and commit, then runs `lake build` and `lake env lean Verification/Axioms.lean`. Every command must finish successfully, and all Lean source files must remain unchanged.

[Verification/Axioms.lean](../Verification/Axioms.lean) explicitly requests the dependencies of 1,202 declarations. The checker requires exactly one result for every requested name and allows only `propext`, `Classical.choice` and `Quot.sound`. It also checks that the four comparison configurations have empty definition lists, the same axiom allowlist, and `enable_nanoda: false`.

| Configuration | Theorem targets |
| --- | ---: |
| [Principals](../Verification/principals.json) | 12 |
| [Real supporting results](../Verification/real-support.json) | 646 |
| [Hermite supporting results](../Verification/hermite-support.json) | 199 |
| [Complex supporting results](../Verification/complex-support.json) | 922 |

These lists overlap. Their union contains 1,058 distinct theorem targets, all included in the explicit axiom audit, together with 144 additional declarations.

Each invocation produces a new `.verification/axioms-…/` directory containing `report.json` and the complete build and Lean output. The report contains commands, exit codes, input and output hashes, the requested inventory, and the actual axiom dependencies. A failure returns a nonzero exit status. Use `--output DIRECTORY` to select another parent directory for the reports.

## Independent statement comparison

[Lean Comparator](https://github.com/leanprover/comparator) checks the solution declarations against [Challenge.lean](../Challenge.lean) and the supporting references under [Verification/References](../Verification/References). The reference files contain statement placeholders for the comparison. The solution is the import closure of `All`; its modules cannot import a reference file.

Comparator exports the specified declarations from each side and checks the solution with Lean's default kernel. The four configurations have empty definition lists and permit only `propext`, `Classical.choice` and `Quot.sound`. The checker requires both complete export inventories, kernel acceptance and a successful process exit.

This check uses Linux, Python 3.11 or later, Git, Go 1.24 or later, a C compiler, and a kernel with Landlock support. The release tool build used Go 1.27.1. The commands below use systemd to disable Unix-domain sockets and external networking during proof checking. Tool installation and the Mathlib cache download take place first, with network access.

From the repository root:

```sh
python3 scripts/setup_comparator.py
```

The setup script uses the pinned Lean installation selected by elan. An existing standalone installation can be selected with `--lean-bin /path/to/lean/bin`. The default tool directory is `.verification/tools`; `--prefix DIRECTORY` selects a different, initially absent directory.

| Tool | Revision |
| --- | --- |
| Comparator | `3927ad383f208ae977c340a91c48ac9b497d2097` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The [compatibility patch](../Verification/comparator-4.33.1.patch) updates three Comparator build files for the pinned Lean and exporter versions. Comparator's verification code is unchanged. The setup report includes the tool-source revisions, build commands and binary hashes.

Run the comparisons as the current unprivileged user:

```sh
sudo systemd-run --wait --pipe --collect \
  --property=User="$(id -un)" \
  --property=PrivateNetwork=yes \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --property=CPUQuota=400% \
  --working-directory="$PWD" \
  -- python3 "$PWD/scripts/check_comparator.py"
```

The checker tests the network and filesystem restrictions before starting Comparator. Each configuration receives a fresh copy of the sources and public dependency cache. Project build objects are compiled afresh. Source files, tool binaries and the original dependency cache are checked for changes throughout the run. The report retains the exact commands, exit codes, exported names, file hashes and complete Comparator output.

Use `--case principals`, `--case real-support`, `--case hermite-support` or `--case complex-support` for an individual configuration. `--tools DIRECTORY` selects the setup directory, `--dependencies DIRECTORY` selects a public `.lake/packages` cache, and `--output DIRECTORY` selects the report parent directory. Successful temporary workspaces are removed after their results have been retained; `--keep-workspaces` retains them. Failed workspaces remain available for inspection.

## Release checks

The release sources passed a clean Linux build, the explicit axiom audit and all four secure Comparator configurations with Lean 4.33.1. Comparator accepted all 1,058 distinct theorem targets, including the 12 principal results. The audit checked 1,202 declarations; their axiom dependencies contain only `propext`, `Classical.choice` and `Quot.sound`.

The [check report](../Verification/Results/results.json) contains the actual commands, exit codes, tool and dependency revisions, source hashes, and isolation and integrity results. Machine-specific path prefixes in commands are replaced by named placeholders, as specified in the report.

- Complete output: [Lean version](../Verification/Results/lean-version.txt), [build](../Verification/Results/build.txt), and [axiom dependencies](../Verification/Results/axioms.txt).
- Comparator output excerpts: [principal results](../Verification/Results/principals-excerpt.txt), [real supporting results](../Verification/Results/real-support-excerpt.txt), [Hermite supporting results](../Verification/Results/hermite-support-excerpt.txt), and [complex supporting results](../Verification/Results/complex-support-excerpt.txt).

Each Comparator excerpt contains the export inventories, build success and kernel and Comparator acceptance lines in their original order. Its header gives the hash of the complete output. The scripts above reproduce the checks and retain their complete output locally.
