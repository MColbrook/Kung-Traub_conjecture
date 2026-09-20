# Palomar preparation and manual preflight

The repository includes a candidate configuration for Palomar's independent verification of the 12 principal results. It has not been submitted or registered. A passing Palomar full-preflight report for the eventual public commit is still required; adding these preparation files does not provide one.

## Candidate and scope

| Field | Value |
| --- | --- |
| Public repository | `MColbrook/Kung-Traub_conjecture` |
| Candidate commit | The future full 40-character SHA containing the reviewed preparation changes |
| Project path | Repository root; omit `project_path` |
| Metadata | [`formalization.yaml`](../formalization.yaml) |
| Comparator configuration | [`Verification/palomar-principals.json`](../Verification/palomar-principals.json) |
| Challenge module | [`PalomarChallenge`](../PalomarChallenge.lean) |
| Solution module | [`All`](../All.lean) |
| Licence | Apache-2.0; see the root [`LICENSE`](../LICENSE) |
| Manual workflow | [`.github/workflows/palomar.yml`](../.github/workflows/palomar.yml) |

The standalone Challenge supplies the relevant definitions and theorem statements using trusted Mathlib imports. The solution remains the complete `All` import closure. The selected configuration compares the 12 listed principal results; it does not request the three supporting-result configurations as additional registry entries. The existing [verification results](Verification.md#release-checks) retain their original tool versions, source hashes and scope. Their Comparator run with NanoDa disabled is separate evidence and does not establish a Palomar preflight pass.

This preparation targets the following immutable upstream revisions, inspected on 2026-09-20:

| Component | Revision |
| --- | --- |
| [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/3561d237dcc4b28482558ad28a64d767d7cc8615) | `3561d237dcc4b28482558ad28a64d767d7cc8615` |
| [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/792c7c0b9e798bd02719e795ef11fa2b5929e067) | `792c7c0b9e798bd02719e795ef11fa2b5929e067` |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The last three pins come from the [verification profile](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/verification-profile.json). Recheck the live policy and [submission protocol](https://submit.palomar-registry.org/llms.txt) before any future submission. If the target verifier revision changes, update both workflow pins together and obtain a new full report.

## Review before publication

- Review the Challenge against the paper and the solution definitions, including the real and complex observation models, partial-method domain conditions, uniform-order quantifiers, and inverse Hermite assumptions. Use the [mathematical review guide](Review.md). Challenge statement placeholders belong only to the reference module, and the solution must not import it.
- Check all 12 theorem names and any explicitly compared definitions in the candidate configuration. Keep its permitted axioms limited to `propext`, `Classical.choice` and `Quot.sound`. Palomar forces NanoDa on in its protected configuration even if a supplied `enable_nanoda` value is false.
- Review the metadata's title, abstract, authors, responsible maintainers, mathematical sources, classifications, automation disclosure and review status for accuracy. Confirm that Apache-2.0 is the intended licence and that the root licence and attribution documents agree.
- Keep `lean-toolchain`, the Lake configuration and `lake-manifest.json` together. This project pins Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Palomar requires an authenticated matching Mathlib toolchain and accepted dependency history; the full run checks those conditions.
- Keep the Challenge within 100 KiB and 1,000 lines. Its warnings above 32 KiB or 300 lines are advisory. Source and configuration limits are 500 MiB and 1 MiB. Avoid Git LFS pointers and substantive Git submodules; dependencies must satisfy the pinned verifier's public-GitHub and commit requirements.
- Review all source changes before creating a commit or pushing it. Publication and a remote preflight run are future actions requiring the user's instruction; neither follows automatically from preparing these files.

The [pinned verifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/scripts/verify_submission.py) authenticates the Challenge import closure separately from the solution's dependencies. A project-local import cannot make its own definitions trusted. The prepared standalone Challenge is the intended boundary for that check.

## Local checks

From the repository root, with the pinned Lean toolchain and matching dependency cache available:

```sh
python3 scripts/check_palomar.py
lake exe cache get
lake build
lake env lean PalomarChallenge.lean
python3 scripts/check_axioms.py
git diff --check
git status --short
```

The read-only `scripts/check_palomar.py` checks the exact copied source blocks and declaration contexts, the twelve statements, imports, configuration, and Challenge size. It does not replace Lean elaboration or kernel comparison.

On Windows, use `py -3` in place of `python3` if appropriate. The existing axiom checker also runs the project build and validates the original four comparison configurations; it is not a validator for the new Palomar configuration. The Challenge intentionally contains reference theorem placeholders, so placeholder warnings from compiling that module are expected. They must not appear in the solution proof closure.

The [existing verification instructions](Verification.md) describe how to reproduce the historical Comparator checks with their original tool pins. Those checks are useful supplementary evidence. The complete Palomar run additionally uses its current Comparator, an independent NanoDa kernel, authenticated Challenge dependencies, and its resource and source-provenance checks. A local build or standalone Comparator invocation does not replace it.

## Preparation checks recorded on 2026-09-20

The following checks passed on the uncommitted preparation in the Windows checkout:

- `python scripts/check_palomar.py`: exact source copies and declaration contexts, twelve principal statements, configuration, imports, and size. The Challenge is 498 lines and 23,197 bytes (SHA-256 `70472f02647ac45dec620858212f3084d54dda7542d141900e34a1d5a6b69eed`).
- `lake env lean PalomarChallenge.lean` using Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`: exit status 0, with exactly the twelve expected reference-placeholder warnings. The local output is retained in the ignored `.verification/palomar-preparation/challenge.log`.
- The pinned PalomarSubmission `load_formalization_metadata` validator accepted `formalization.yaml`. Both the declared formalization v0.4 JSON schema and the Citation File Format 1.2.0 schema accepted their respective files.
- Workflow YAML, manual-only dispatch, matching verifier pins, read-only permissions, and both authorization choices passed local parsing and the pinned `submission_request` input parser. This was a local function call, not a service request or workflow dispatch.
- All nine installed dependencies matched `lake-manifest.json`; `git diff --check` passed. Existing proof sources, the original Challenge/configurations, and historical verification records were unchanged. Nothing was staged or committed.

These checks cover the preparation files. The complete solution build and axiom audit were not rerun in this preparation; their recorded release results remain historical evidence. The new configuration has not yet passed Comparator, NanoDa, or the full remote workflow. Rerun the relevant checks after further changes and obtain the full report for the eventual public commit before submission.

## First full preflight and shared model

[The first full run](https://github.com/MColbrook/Kung-Traub_conjecture/actions/runs/35506289009), for commit `61ee4ba147cfbf3a04ef2d17d7d3813fd4b9d8b1`, passed the complete Lean solution build and the canonical Challenge provenance audit. Comparator then rejected a mismatch at `KungTraub.RealAlgorithm.run`; NanoDa replay was not reached.

The standalone Challenge's additional Mathlib imports selected a different real normed-space instance in `RealQuery.answer`, which also changed downstream reducibility-height metadata. A complete local comparison then identified differences caused by Lean reusing generated matchers and auxiliary proofs within one file. The pinned Comparator compares exported definitions exactly, so copying source text alone did not ensure a match across different import environments and module boundaries.

The shared model definitions now live together in [`KungTraub/Model.lean`](../KungTraub/Model.lean), with the same Mathlib imports and declaration order as the standalone Challenge. The previous definition modules re-export this model, and the surrounding theorem proofs retain their existing modules. Mathematical definition bodies and theorem statements are unchanged, and no definitions have been exempted from comparison. The static source checker compares the complete shared-model body with the standalone copy. The rebuilt model and both reference modules compile. An independent local comparison of the twelve principal statement closures checked 19,246 declarations, including generated helpers and reducibility metadata, with zero mismatches or missing declarations. This local comparison does not check the solution proofs or replace NanoDa; a fresh full report for the corrected commit is required.

## Run the full preflight after an approved push

The workflow has only a `workflow_dispatch` trigger: pushing does not start it. It requests read-only repository access, inherits no secrets, and calls the pinned reusable verifier. It contains no Palomar intake, authorization-tag, gist, or registration action.

1. After the user approves the publication changes, make the reviewed commit available in the public repository. GitHub requires this workflow on the [default branch](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#workflow_dispatch) for manual dispatch to be available. Record the intended candidate's full SHA with `git rev-parse HEAD` in the matching checkout; uncommitted files are never included in the remote check.
2. In GitHub Actions, select **Palomar full preflight**, choose **Run workflow**, and select the branch or ref containing that candidate. Choose the truthful authorization relationship. The workflow accepts the exact upstream sentences **I am a responsible author or maintainer** and **I have approval from a responsible author or maintainer**. This choice describes the person requesting the run.
3. The job checks `${{ github.repository }}` at `${{ github.sha }}` for the selected dispatch. Confirm the run's SHA matches the intended candidate, especially if the branch moved. It uses the root project, `formalization.yaml`, and `Verification/palomar-principals.json`, with `mode: full` and `palomar-standard-v1`.
4. Wait for the complete run and download **mechanical-report-preflight001** from its artifacts. The archive contains `mechanical-report.json`; retention is 90 days. Save the run URL and report with the candidate SHA and verifier revision before that retention period expires.
5. Require both a successful workflow and report `status: pass`. Check that `source.repository` and `source.commit` identify the intended public candidate, and inspect the configuration, tool revisions, diagnostics and resource evidence. A `pending`, `fail` or `error` report, cancelled job, missing report, OOM, timeout or incomplete resource evidence does not satisfy this step. Follow the reported diagnostics before rerunning.

The fixed `preflight001` is a caller-selected identifier of exactly 12 lowercase alphanumeric characters. It labels the artifact within each run; it is not a Palomar submission ID obtained from the registry. The reusable workflow scopes concurrency to the caller run and attempt.

The standard [resource profile](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/verification-profile.json) uses Ubuntu 24.04 x86-64, a 350-minute job timeout and 19,800-second verification budget. It requires at least 20 GiB of free workspace and 14 GiB of host memory. A passing report covers this immutable candidate and selected configuration; changes to the source, metadata, configuration, paths or verifier require a matching new preflight.

The [upstream caller workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/.github/workflows/submission.yml) and [input contract](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/scripts/submission_contract.py) define the exact arguments. `mode: preflight` runs only preparation; this caller deliberately uses `mode: full`. A full preflight does not perform Challenge rendering, editorial review or registry registration, and the later server run may differ.

## Future submission and registration

These are manual instructions only. Preparing files or obtaining a passing preflight does not authorize submission. Before starting intake, show the user the exact repository, full candidate SHA, configuration path and proposed relationship, together with the passing report, and obtain their explicit instruction to proceed. The service records that relationship permanently. Review the current [policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md) and [service instructions](https://submit.palomar-registry.org/llms.txt) again at that time.

The human submitter can use [Palomar's submission page](https://submit.palomar-registry.org/) and complete their own GitHub sign-in. An agent must not automate that sign-in. After explicit user approval, the alternative agent protocol uses authenticated `gh` to establish repository write access:

1. Start `POST /api/submit` for the approved repository, SHA and paths. API relationship codes are `maintainer` or `approved`; the workflow uses full sentences. Supply an existing ID only for a new entry version.
2. Create the challenge's temporary authorization tag at the approved commit and a new **secret** gist with the exact challenge.
3. Complete `POST /api/verify` with the pending secret and gist ID within the 15-minute intake lifetime. Keep the returned access token private, then delete the temporary tag and gist.
4. Monitor using the token in the authorization header; respect cooldowns. If authentication cannot be completed, hand the browser flow to the user. Keep tokens and unregistered reviews out of public files and logs.

Registration is a separate decision: show the actual review, explain publication, and obtain explicit user approval before `POST /register` with that review's exact `review_sha256`. Follow the linked live protocol for request bodies and error handling. Preflight does not establish editorial acceptance or authorize registration.
