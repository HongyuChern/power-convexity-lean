import PowerConvexityComparator.AppendixASolution
import PowerConvexityComparator.AppendixBSolution
import PowerConvexityComparator.DimensionRemarkSolution
import PowerConvexityComparator.OriginalRoute
import PowerConvexityComparator.SeparationSolution
import PowerConvexityComparator.SeparationUniversalSolution
import PowerConvexityComparator.SigmaSolution
import PowerConvexityComparator.Solution
import PowerConvexityComparator.SupportSolution
import PowerConvexityComparator.UniformSolution

namespace PowerConvexityComparator.Targets

theorem main_theorem : Problem.MainStatement := OriginalRoute.newMainAnswer

theorem appendix_c : Problem.AppendixCStatement := Solution.appendixCAnswer

theorem determinant_identity : AppendixAProblem.A1Statement := AppendixASolution.a1Answer

theorem arrow_matrix : AppendixAProblem.A2Statement := AppendixASolution.a2Answer

theorem maximum_eigenvalue_derivatives : AppendixBProblem.MaximumStatement := AppendixBSolution.maximumAnswer

theorem minimum_eigenvalue_derivatives : AppendixBProblem.MinimumStatement := AppendixBSolution.minimumAnswer

theorem perturbation_minimizer : SeparationProblem.SeparationStatement := SeparationSolution.separationAnswer

theorem every_perturbation_minimizer : SeparationUniversalProblem.UniversalSeparationStatement := SeparationUniversalSolution.universalSeparationAnswer

theorem robustness : SupportProblem.RobustnessStatement := SupportSolution.robustnessAnswer

theorem zero_contact : SupportProblem.TouchStatement := SupportSolution.touchAnswer

theorem perturbation_stability : SupportProblem.StabilityStatement := SupportSolution.stabilityAnswer

theorem sigma_estimate : SigmaProblem.SigmaStatement := SigmaSolution.sigmaAnswer

theorem uniform_robustness : UniformProblem.UniformRobustnessStatement := UniformSolution.uniformRobustnessAnswer

theorem scalar_algebra : DimensionRemarkProblem.ScalarIdentityStatement := DimensionRemarkSolution.scalarIdentityAnswer

theorem higher_dimension_algebra : DimensionRemarkProblem.CounterexampleStatement := DimensionRemarkSolution.counterexampleAnswer

end PowerConvexityComparator.Targets
