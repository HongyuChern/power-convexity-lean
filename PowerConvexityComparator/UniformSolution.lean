import PowerConvexityComparator.UniformProblem
import PowerConvexityComparator.SupportSolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace PowerConvexityComparator.UniformSolution
open AppendixAProblem SeparationProblem SupportProblem UniformProblem PowerConvexity

theorem uniformRobustnessAnswer : UniformRobustnessStatement := by
  intro n μ hμ K X hK hX ε m hε hm
  letI : IsFiniteMeasureOnCompacts μ := hμ
  obtain ⟨C,hC,hbound⟩ := uniform_L2_quadratic_robustness μ hK hX xAxis hε hm
  refine ⟨C,hC,?_⟩
  intro u x hx hu hmx hux hfamily
  apply hbound u x hx hu hmx hux
  intro q hq hEq v
  exact hfamily q ((SeparationSolution.class_eq q).mp hq) hEq v

end PowerConvexityComparator.UniformSolution
