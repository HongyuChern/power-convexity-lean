import PowerConvexityComparator.AppendixBProblem
import PowerConvexity.Calculus.ExtremalEigenvalueRealDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PowerConvexityComparator.AppendixBSolution
open AppendixBProblem

theorem maximumAnswer : MaximumStatement := by
  intro n K x hK i d hd hm hr
  have h := PowerConvexity.largestRealEigenvalue_jet hK i d hd hm hr
  refine ⟨h.1,h.2.1,?_⟩
  intro a c
  exact h.real_derivatives a c

theorem minimumAnswer : MinimumStatement := by
  intro n K x hK i d hd hm hr
  have h := PowerConvexity.smallestRealEigenvalue_jet hK i d hd hm hr
  refine ⟨h.1,h.2.1,?_⟩
  intro a c
  exact h.real_derivatives a c

end PowerConvexityComparator.AppendixBSolution
