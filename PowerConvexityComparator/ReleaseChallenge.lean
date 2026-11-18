import PowerConvexityComparator.AppendixAProblem
import PowerConvexityComparator.AppendixBProblem
import PowerConvexityComparator.DimensionRemarkProblem
import PowerConvexityComparator.Problem
import PowerConvexityComparator.SeparationProblem
import PowerConvexityComparator.SeparationUniversalProblem
import PowerConvexityComparator.SigmaProblem
import PowerConvexityComparator.SupportProblem
import PowerConvexityComparator.UniformProblem

namespace PowerConvexityComparator.Targets

theorem main_theorem : Problem.MainStatement := by
  sorry

theorem appendix_c : Problem.AppendixCStatement := by
  sorry

theorem determinant_identity : AppendixAProblem.A1Statement := by
  sorry

theorem arrow_matrix : AppendixAProblem.A2Statement := by
  sorry

theorem maximum_eigenvalue_derivatives : AppendixBProblem.MaximumStatement := by
  sorry

theorem minimum_eigenvalue_derivatives : AppendixBProblem.MinimumStatement := by
  sorry

theorem perturbation_minimizer : SeparationProblem.SeparationStatement := by
  sorry

theorem every_perturbation_minimizer : SeparationUniversalProblem.UniversalSeparationStatement := by
  sorry

theorem robustness : SupportProblem.RobustnessStatement := by
  sorry

theorem zero_contact : SupportProblem.TouchStatement := by
  sorry

theorem perturbation_stability : SupportProblem.StabilityStatement := by
  sorry

theorem sigma_estimate : SigmaProblem.SigmaStatement := by
  sorry

theorem uniform_robustness : UniformProblem.UniformRobustnessStatement := by
  sorry

theorem scalar_algebra : DimensionRemarkProblem.ScalarIdentityStatement := by
  sorry

theorem higher_dimension_algebra : DimensionRemarkProblem.CounterexampleStatement := by
  sorry

end PowerConvexityComparator.Targets
