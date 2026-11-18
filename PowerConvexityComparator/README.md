# Independent Comparator verification

The [challenge](ReleaseChallenge.lean) checks 15 statements with the pinned Comparator. Its imports follow the Mathlib-only problem modules. The [solution](ReleaseSolution.lean) assigns the verified adapters to the same types. In particular, the two-dimensional main answer uses the [C114 original-route proof](OriginalRoute.lean). The placeholders in the challenge designate the tasks to be solved.

| Frozen paper group | Targets in `PowerConvexityComparator.Targets` |
| --- | --- |
| Main theorem and Appendix C | `main_theorem`, `appendix_c` |
| Section 3 | `sigma_estimate`, `zero_contact`, `perturbation_stability` |
| Appendix A | `determinant_identity`, `arrow_matrix`, `perturbation_minimizer`, `every_perturbation_minimizer`, `robustness`, `uniform_robustness` |
| Appendix B | `maximum_eigenvalue_derivatives`, `minimum_eigenvalue_derivatives` |
| Dimension remark | `scalar_algebra`, `higher_dimension_algebra` |

[Exact target IDs and axiom allowlist](config.json) · [Manuscript scope and corrections](../docs/PAPER_COVERAGE.md)

## Reproduce on Linux

Use an unprivileged Linux account with Landlock and a working systemd user session. From a separate tools checkout, build Comparator and lean4export with Lean 4.33.1. Use Comparator at `3927ad383f208ae977c340a91c48ac9b497d2097` and its locked lean4export at `15f6055e299ad5b89345e533cc2192f4cc00f659`. The reference run uses Landrun at `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` and the Nanoda 0.4.19 binary from Lean 4.35.0. [Pinned Comparator guide](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097) · [Landrun](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4)

From the project root, set the executable paths and run the following. The proof toolchain and dependency revisions come from the project lock.

```sh
lake exe cache get
lake build PowerConvexity.C114Complete
export POWER_COMPARATOR=/absolute/path/to/comparator
export COMPARATOR_LEAN4EXPORT=/absolute/path/to/lean4export
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
export COMPARATOR_NANODA=/absolute/path/to/nanoda_bin
bash verification/run-comparator-linux.sh
```

A successful run reports `Nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`. The receipt gives the platform, sandbox controls, build and tool hashes, exact targets, and input hashes. [Linux verification receipt](../verification/linux-verification.json)
