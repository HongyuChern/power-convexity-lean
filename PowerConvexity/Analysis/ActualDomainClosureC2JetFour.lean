import PowerConvexity.Analysis.ActualDomainBoundaryJetControlFour
import CHS.Calculus.ClosureRegularity

/-! # Actual closure C2 jets from proved uniform original-coordinate boundary expansions
Uniform boundary expansions are the explicit remaining analytic input here;
the closure jet itself and its continuous boundary fields are constructed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_domain_closure_C2_jet_of_expansion_four
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter R gamma M T lam Lambda alpha Ka Kf : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hball : closedBall o rho ⊆ U) (hbound : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    (D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (J : ActualDomainBoundaryExpansionFour D R gamma M T) :
    Nonempty (ClosureC2Jet D.solution U) := by
  obtain ⟨C,hC,hcontrol⟩ := actual_domain_boundary_interior_jet_control_four
    hlam hLambda halpha hg hga hKa hKf hM hT
  obtain ⟨hgfield,hhfield⟩ := actual_domain_boundary_polynomial_jets_continuous_four
    hU hconv hrho hdia hR hg hM hball hbound D J
  let g := fun c : E => fderiv ℝ (J.polynomial c) c
  let h := fun c : E => realHessian (J.polynomial c) c
  have hd : ContDiffOn ℝ 1 (fderiv ℝ D.solution) U := D.solution_regular.fderiv_of_isOpen hU (by norm_num)
  have hDc : ContinuousOn (fderiv ℝ D.solution) U := hd.continuousOn
  have hHc : ContinuousOn (realHessian D.solution) U := hd.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have heps : 0 < min 1 (R/2) := lt_min zero_lt_one (half_pos hR)
  have hgrad : ContinuousOn (actualDomainJetExtensionFour U (fderiv ℝ D.solution) g) (closure U) := by
    apply actual_domain_jet_extension_continuous_four hU hproper hDc hgfield heps
      (w := fun s : ℝ => (C+4*T)*(s/4)) (by fun_prop) (by ring)
    intro x hx hnear
    exact (hcontrol U hU hproper D R hR J x hx hnear).1
  have hhess : ContinuousOn (actualDomainJetExtensionFour U (realHessian D.solution) h) (closure U) := by
    have hw : Continuous (fun s : ℝ => C*(s/4)^gamma) :=
      continuous_const.mul ((Real.continuous_rpow_const hg.le).comp (continuous_id.div_const 4))
    apply actual_domain_jet_extension_continuous_four hU hproper hHc hhfield heps
      (w := fun s : ℝ => C*(s/4)^gamma) hw.continuousAt
      (by simp only [zero_div,Real.zero_rpow hg.ne',mul_zero])
    intro x hx hnear
    exact (hcontrol U hU hproper D R hR J x hx hnear).2
  exact ⟨{
    derivative := actualDomainJetExtensionFour U (fderiv ℝ D.solution) g
    hessian := actualDomainJetExtensionFour U (realHessian D.solution) h
    continuous_value := D.solution_continuous
    continuous_derivative := hgrad
    continuous_hessian := hhess
    derivative_eq := by intro x hx; exact if_pos hx
    hessian_eq := by intro x hx; exact if_pos hx
  }⟩

end PowerConvexity
