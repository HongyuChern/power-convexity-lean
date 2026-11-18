# Power Convexity for the Complex Monge–Ampère Equation in Lean

This repository contains the Lean 4 formalization of *Power Convexity of Solutions to the Complex Monge–Ampère Equation* by Hongyu Chen, Jingchen Hu, and Li Sheng. The source paper is [arXiv:2607.06895v1](https://arxiv.org/abs/2607.06895v1).

`import PowerConvexity.C114Complete` exposes all nine numbered results. The two theorems are listed below. The two propositions and five lemmas are indexed in the [paper coverage table](docs/PAPER_COVERAGE.md).

| Paper | Lean declaration | Result | Proof |
| --- | --- | --- | --- |
| Theorem 1.1 | `PowerConvexity.actual_original_route_mainTheorem` | Strict convexity of the negative square root in complex dimension two | [Main theorem](PowerConvexity/Targets/ActualOriginalRouteMainTheorem.lean#L19) |
| Theorem C.1 | `PowerConvexity.appendixC_geometric_main_strictConvexOn` | The same conclusion in complex dimension one | [Appendix C proof](PowerConvexity/Targets/GeometricTargetContracts.lean#L18) |

The proof constructs the classical solutions on the intermediate Minkowski domains. It proves spectral positivity on a common inner truncation and recovers strict convexity on each full domain. [Domain deformation](PowerConvexity/Calculus/ActualPaperFamilyAssemblyTwo.lean#L26) · [Proof report](docs/C114_FINAL_PROOF_REPORT.md) · [Manuscript map and corrections](docs/TEX_DECLARATION_MAP.md)

## Build

With [Elan](https://github.com/leanprover/elan) installed, run the following from the repository root. The project uses Lean 4.33.1 and the dependencies pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build PowerConvexity.C114Complete
```

The v0.1.0 source release contains **128,174 lines of Lean**, including comments and blank lines. The complete import closure of `PowerConvexity.C114Complete` contains **1,909,500 lines**, counting each source file once and including imports from Mathlib, the Lean toolchain, and other dependencies.

## Comparator

The independent challenge specifies 15 statements using only Mathlib, including both theorem statements and the supporting results. The `sorry` placeholders mark the proofs supplied by the solution.

[Challenge](PowerConvexityComparator/ReleaseChallenge.lean) · [Main statements](PowerConvexityComparator/Problem.lean) · [Main theorem bridge](PowerConvexityComparator/OriginalRoute.lean) · [Solution](PowerConvexityComparator/ReleaseSolution.lean) · [Configuration](PowerConvexityComparator/config.json) · [Targets and reproduction](PowerConvexityComparator/README.md)

The standalone challenge built with Mathlib as its sole direct dependency. On Ubuntu 24.04 ARM64, Lean and Nanoda accepted all 15 proofs under Landrun and systemd on [source commit `d1f6f3a`](https://github.com/HongyuChern/power-convexity-lean/commit/d1f6f3ae0715b36bb1d2ca2a512163c60edf7eb9). The allowed axioms were `propext`, `Classical.choice`, and `Quot.sound`. [Linux verification receipt](https://github.com/HongyuChern/power-convexity-lean/blob/8bc4a3dc83c58f450ee3996aead27c14faa85713/verification/linux-verification.json) · [Paper coverage audit](verification/PaperCoverageAudit.lean)

## Source and attribution

The proofs use the pinned CHS development and its De Giorgi theory for weak Harnack estimates and boundary regularity. [Upstream sources, credits, and licenses](THIRD_PARTY.md)

The Lean code is licensed under [Apache-2.0](LICENSE).
