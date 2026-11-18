import PowerConvexity.Analysis.ActualDomainJetExtensionFour
import PowerConvexity.Analysis.ActualConvexBoundaryGradientComparisonFour
import PowerConvexity.Analysis.ActualLocalHolderContinuityFour

/-! # Actual original-domain boundary jet control from uniform boundary expansions
The uniform boundary expansion remains an explicit input. This file does not
assert its construction from arbitrary curved-boundary Dirichlet data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualDomainLinearDataFour (U : Set E) (lam Lambda alpha Ka Kf : ℝ) where
  coeff : EllipticCoeff (2+2) U
  source : E → ℝ
  solution : E → ℝ
  lower : lam ≤ coeff.lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ U, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) U
  divergence : ∀ x ∈ U, ∀ j, (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  holder : ∀ x ∈ closure U, ∀ y ∈ closure U,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (coeff.a y)‖ ≤ Ka*‖x-y‖^alpha
  source_regular : ContDiffOn ℝ 1 source U
  source_holder : ∀ x ∈ closure U, ∀ y ∈ closure U, |source x-source y| ≤ Kf*‖x-y‖^alpha
  solution_regular : ContDiffOn ℝ 2 solution U
  solution_continuous : ContinuousOn solution (closure U)
  equation : ∀ x ∈ U, (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

structure ActualDomainBoundaryExpansionFour {U : Set E} {lam Lambda alpha Ka Kf : ℝ}
    (D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf) (R gamma M T : ℝ) where
  polynomial : E → E → ℝ
  quadratic : ∀ c ∈ frontier U, IsQuadraticPolynomial (polynomial c)
  hessian_bound : ∀ c ∈ frontier U, ‖realHessian (polynomial c) 0‖ ≤ T
  frozen : ∀ c ∈ frontier U,
    (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian (polynomial c) c i j) = -D.source c
  remainder : ∀ c ∈ frontier U, ∀ z ∈ U, ‖z-c‖ < R →
    |D.solution z-polynomial c z| ≤ M*‖z-c‖^2*‖z-c‖^gamma

theorem actual_domain_boundary_polynomial_jets_continuous_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {o : E} {rho diameter R gamma M T lam Lambda alpha Ka Kf : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R) (hg : 0 < gamma) (hM : 0 ≤ M)
    (hball : closedBall o rho ⊆ U) (hbound : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    (D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (J : ActualDomainBoundaryExpansionFour D R gamma M T) :
    ContinuousOn (fun c => fderiv ℝ (J.polynomial c) c) (frontier U) ∧
    ContinuousOn (fun c => realHessian (J.polynomial c) c) (frontier U) := by
  have hsub : frontier U ⊆ closure U := frontier_subset_closure
  constructor
  · apply actual_local_holder_continuousOn_four
      (lt_min (by positivity : 0 < R/4) (lt_min (by positivity : 0 < diameter+rho) (by norm_num : (0 : ℝ) < 1/4)))
      (by norm_num : (0 : ℝ) < 1)
    intro c hc d hd hnear
    simpa only [Real.rpow_one] using actual_convex_boundary_gradient_lipschitz_four
      hU hconv hrho hdia hR hM hg.le hball hsub hbound J.quadratic J.hessian_bound J.remainder c hc d hd hnear
  · apply actual_local_holder_continuousOn_four
      (lt_min (by positivity : 0 < R/4) (by positivity : 0 < diameter+rho)) hg
    intro c hc d hd hnear
    exact actual_convex_boundary_hessian_holder_four hU hconv hrho hdia hR hM hg.le
      hball hsub hbound J.quadratic J.remainder c hc d hd hnear

theorem actual_domain_boundary_interior_jet_control_four {lam Lambda alpha gamma Ka Kf M T : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ C ≥ 0, ∀ U : Set E, ∀ hU : IsOpen U, ∀ hproper : U ≠ univ,
    ∀ D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf,
    ∀ R > 0, ∀ J : ActualDomainBoundaryExpansionFour D R gamma M T,
    ∀ x ∈ U, infDist x (frontier U) < min 1 (R/2) →
    let c := actualBoundaryFootOnDomainFour U hproper x
    let r := infDist x (frontier U)/4
    ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖ ≤ (C+4*T)*r ∧
      ‖realHessian D.solution x-realHessian (J.polynomial c) c‖ ≤ C*r^gamma := by
  obtain ⟨C,hC,hestimate⟩ := actual_boundary_set_interior_jet_error_four
    hlam hLambda halpha hg hga hKa hKf hM hT
  refine ⟨C,hC,?_⟩
  intro U hU hproper D R hR J x hx hsmall
  let d := infDist x (frontier U)
  let r := d/4
  let c := actualBoundaryFootOnDomainFour U hproper x
  obtain ⟨hd,c0,hc0,_,hmap,_⟩ := actual_boundary_distance_ball_four hU hproper hx
  have hr : 0 < r := by dsimp [r,d]; positivity
  have hd1 : d ≤ 1 := (hsmall.trans_le (min_le_left _ _)).le
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hrR : 6*r < R := by
    have hh : d < R/2 := hsmall.trans_le (min_le_right _ _)
    dsimp [r]; linarith
  have hfoot := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)
  have hc : c ∈ frontier U := hfoot.1
  have hxc : ‖x-c‖=4*r := by
    have he : ‖x-c‖=d := by simpa only [dist_eq_norm] using hfoot.2
    rw [he]; dsimp [r]; ring
  have hnear : ∀ z ∈ ball (0 : E) 2, ‖(x+r • z)-c‖ ≤ 6*r := by
    intro z hz
    have hz2 : ‖z‖ ≤ 2 := (show ‖z‖ < 2 from by simpa only [mem_ball,dist_zero_right] using hz).le
    have he : (x+r • z)-c=(x-c)+r • z := by abel
    rw [he]
    apply (norm_add_le (x-c) (r • z)).trans
    rw [hxc,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hh := hestimate U hU D.coeff D.lower D.upper D.positive D.regular D.divergence D.holder
    D.source D.solution D.source_regular D.solution_regular D.source_holder D.equation
    c (frontier_subset_closure hc) (J.polynomial c) (J.quadratic c hc) (J.hessian_bound c hc)
    (J.frozen c hc) R (J.remainder c hc) x r hr hr1 hrR hmap hnear
  have hgrad := actual_quadratic_gradient_difference_bound_four (J.quadratic c hc) (J.hessian_bound c hc) x c
  rw [hxc] at hgrad
  have hscale : r^gamma ≤ 1 := Real.rpow_le_one hr.le hr1 hg.le
  change ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖ ≤ (C+4*T)*r ∧
    ‖realHessian D.solution x-realHessian (J.polynomial c) c‖ ≤ C*r^gamma
  constructor
  · have htriangle : ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖ ≤
        ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) x‖+
          ‖fderiv ℝ (J.polynomial c) x-fderiv ℝ (J.polynomial c) c‖ := by
      simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ D.solution x)
        (fderiv ℝ (J.polynomial c) x) (fderiv ℝ (J.polynomial c) c)
    have hfac : (r^gamma*r)*C ≤ r*C := by
      simpa only [mul_assoc,one_mul] using mul_le_mul_of_nonneg_right hscale (mul_nonneg hr.le hC)
    exact (htriangle.trans (add_le_add hh.1 hgrad)).trans
      ((add_le_add hfac (le_refl (T*(4*r)))).trans_eq (by ring))
  · have he : realHessian (J.polynomial c) x=realHessian (J.polynomial c) c := by
      rw [quadratic_realHessian_from_jet_zero (J.quadratic c hc) x,
        quadratic_realHessian_from_jet_zero (J.quadratic c hc) c]
    simpa only [he,mul_comm] using hh.2

end PowerConvexity
