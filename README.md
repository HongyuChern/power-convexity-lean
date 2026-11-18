# Power Convexity for the Complex Monge–Ampère Equation in Lean

This Lean 4 development formalizes the mathematical results of *Power Convexity of Solutions to the Complex Monge–Ampère Equation* by Hongyu Chen, Jingchen Hu and Li Sheng, frozen at arXiv:2607.06895v1. It covers the two main endpoints, the two propositions and five lemmas, and the proof dependencies, including the actual intermediate-domain Dirichlet family and the return from truncated domains. The source audit records the necessary corrections to the printed formulas and hypotheses. [Paper](https://arxiv.org/abs/2607.06895v1) · [Coverage and corrections](docs/PAPER_COVERAGE.md)

| Paper | Lean declaration | Result | Proof |
| --- | --- | --- | --- |
| Main theorem | `actual_original_route_mainTheorem` | Strict convexity of the negative square root in complex dimension two | [Lean source](PowerConvexity/Targets/ActualOriginalRouteMainTheorem.lean) |
| Domain deformation | `actual_paper_family_common_collar_exhaustion_two` | Same classical family, common small truncation, and convexity on each full domain | [Lean source](PowerConvexity/Calculus/ActualPaperFamilyAssemblyTwo.lean) |
| Appendix C | `appendixC_geometric_main_strictConvexOn` | Strict convexity in complex dimension one | [Lean source](PowerConvexity/Targets/GeometricTargetContracts.lean) |

The [full manuscript map](docs/TEX_DECLARATION_MAP.md) links the frozen LaTeX labels to assembled identities and Lean declarations. The [proof report](docs/C114_FINAL_PROOF_REPORT.md) describes the intermediate-domain existence argument, boundary estimates on strong outer approximants, and comparison back to the prescribed solution.

## Build and verify

Install Elan and use the Lean 4.33.1 toolchain and the pinned Lake dependencies. The complete entry is `PowerConvexity.C114Complete`.

```sh
lake exe cache get
lake build PowerConvexity.C114Complete
lake build +PowerConvexityComparator.ReleaseSolution
lake env lean verification/PaperCoverageAudit.lean
lake env lean verification/C114CompleteFinalAudit.lean
```

The external Comparator suite checks 15 Mathlib-only statement types with Lean and Nanoda on Linux. The project audit covers the C114 proof interfaces and the dependency chain separately. [Comparator guide](PowerConvexityComparator/README.md) · [Linux verification receipt](verification/linux-verification.json)

The release contains **128,174 lines of Lean**. The full source import closure of `PowerConvexity.C114Complete` contains **1,909,500 lines**, including locked dependencies and the Lean toolchain. Both counts include blank lines and comments.

Licensed under Apache-2.0. [License](LICENSE) · [Third-party provenance](THIRD_PARTY.md)
