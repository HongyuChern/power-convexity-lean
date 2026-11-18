import PowerConvexity.Calculus.FiniteParameterGraphLocalInverse

/-! # Actual fiber derivatives for finite-dimensional joint parameters -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {P E G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem finite_parameter_fiber_fderiv_eq
    {F : P × E → G} {p : P × E} (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ (fun y => F (p.1,y)) p.2 =
      (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ P E) :=
  (hF.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

theorem finite_parameter_fiber_fderiv_contDiffAt
    {F : P × E → G} {p : P × E} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ (n+1) F p) :
    ContDiffAt ℝ n (fun q : P × E => fderiv ℝ (fun y => F (q.1,y)) q.2) p := by
  have h1 : ContDiffAt ℝ 1 F p := hF.of_le (by simp)
  have heq : (fun q : P × E => fderiv ℝ (fun y => F (q.1,y)) q.2) =ᶠ[𝓝 p]
      (fun q => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ P E)) := by
    filter_upwards [h1.eventually (by norm_num)] with q hq
    exact finite_parameter_fiber_fderiv_eq (hq.differentiableAt (by norm_num))
  exact ((hF.fderiv_right le_rfl).clm_comp contDiffAt_const).congr_of_eventuallyEq heq

end PowerConvexity
