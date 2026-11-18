# Source provenance

The mathematics formalized here is by Hongyu Chen, Jingchen Hu and Li Sheng. The Lean project is licensed under Apache-2.0. The frozen manuscript is cited by version and source hash. [Paper, arXiv:2607.06895v1](https://arxiv.org/abs/2607.06895v1) · [License](LICENSE)

## Adapted Lean source

The source tree preserves the following related upstream proof code. Module paths in the right column refer to the pinned CHS revision, `b8d5bcd0bba52f39ec63e5011c9a07eedc52102a`. The adaptations change statements, namespaces, imports and proof interfaces for power convexity.

| This repository | Upstream proof source |
| --- | --- |
| `PowerConvexity/Calculus/ConstantDensity.lean` | `CHS/Calculus/DetOneSecondVariation.lean` |
| `PowerConvexity/Analysis/FiniteOscillationWithError.lean` | `CHS/Analysis/FiniteOscillation.lean` |
| `PowerConvexity/Analysis/ActualZeroTraceBallTransportTwo.lean` and `ActualScalarWeakScalingTwo.lean` | `DifferentialGeometry/External/DeGiorgi/BallScaling.lean` |

CHS's De Giorgi sources come from DifferentialGeometry v0.1.3, revision `7a48598d35109aa99d1cc678e2724c213cdf4ff3`, which adapts the work of Scott Armstrong and Julia Kempe. The notices and Apache-2.0 licenses accompany the adapted code. [CHS pinned source and provenance](https://github.com/HongyuChern/pogorelov-liouville-lean/blob/b8d5bcd0bba52f39ec63e5011c9a07eedc52102a/THIRD_PARTY.md) · [Armstrong–Kempe development](https://github.com/scottnarmstrong/DeGiorgi/tree/4c1b3077d3782b24065184df4ba59501b2e56fc7) · [Notices and license texts](LICENSES/) · [Source hashes](docs/adapted-source.json)

## Dependencies and verification tools

Lake obtains CHS, Mathlib and all transitive packages using [the dependency lock](lake-manifest.json). The proof checker and its tooling are installed separately and retain their own licenses. [Comparator configuration](PowerConvexityComparator/README.md)
