import PowerConvexity.Analysis.ActualBoundarySetPrescribedHolderErrorFour
import PowerConvexity.Analysis.ActualDomainBoundaryJetControlFour

/-! # Actual boundary jets and local Hessian Holder control for continuous loads

The boundary expansions remain an explicit input. The source is continuous
and Holder; no derivative of the source occurs in the estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualContinuousDomainLinearDataFour (U : Set E) (lam Lambda alpha Ka Kf : ℝ) where
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
  source_continuous : ContinuousOn source U
  source_holder : ∀ x ∈ closure U, ∀ y ∈ closure U, |source x-source y| ≤ Kf*‖x-y‖^alpha
  solution_regular : ContDiffOn ℝ 2 solution U
  solution_continuous : ContinuousOn solution (closure U)
  equation : ∀ x ∈ U, (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

structure ActualContinuousDomainBoundaryExpansionFour
    {U : Set E} {lam Lambda alpha Ka Kf : ℝ}
    (D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf) (R M T : ℝ) where
  polynomial : E → E → ℝ
  quadratic : ∀ c ∈ frontier U, IsQuadraticPolynomial (polynomial c)
  hessian_bound : ∀ c ∈ frontier U, ‖realHessian (polynomial c) 0‖ ≤ T
  frozen : ∀ c ∈ frontier U,
    (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian (polynomial c) c i j) = -D.source c
  remainder : ∀ c ∈ frontier U, ∀ z ∈ U, ‖z-c‖ < R →
    |D.solution z-polynomial c z| ≤ M*‖z-c‖^2*‖z-c‖^alpha

def ActualDomainLinearDataFour.toContinuous
    {U : Set E} {lam Lambda alpha Ka Kf : ℝ}
    (D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf) :
    ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf where
  coeff := D.coeff
  source := D.source
  solution := D.solution
  lower := D.lower
  upper := D.upper
  positive := D.positive
  regular := D.regular
  divergence := D.divergence
  holder := D.holder
  source_continuous := D.source_regular.continuousOn
  source_holder := D.source_holder
  solution_regular := D.solution_regular
  solution_continuous := D.solution_continuous
  equation := D.equation

def ActualDomainBoundaryExpansionFour.toContinuous
    {U : Set E} {lam Lambda alpha Ka Kf R M T : ℝ}
    {D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf}
    (J : ActualDomainBoundaryExpansionFour D R alpha M T) :
    ActualContinuousDomainBoundaryExpansionFour D.toContinuous R M T where
  polynomial := J.polynomial
  quadratic := J.quadratic
  hessian_bound := J.hessian_bound
  frozen := J.frozen
  remainder := J.remainder

theorem actual_continuous_domain_boundary_local_holder_four
    {lam Lambda alpha Ka Kf M T : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (halpha1 : alpha < 1) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ delta > 0, delta ≤ (1/8 : ℝ) ∧ ∃ C ≥ 0,
    ∀ U : Set E, ∀ hU : IsOpen U, ∀ hproper : U ≠ univ,
    ∀ D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf,
    ∀ R > 0, ∀ J : ActualContinuousDomainBoundaryExpansionFour D R M T,
    ∀ x ∈ U, infDist x (frontier U) < min 1 (R/2) →
    let c := actualBoundaryFootOnDomainFour U hproper x
    let r := infDist x (frontier U)/4
    ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖ ≤ (C+4*T)*r ∧
      ‖realHessian D.solution x-realHessian (J.polynomial c) c‖ ≤ C*r^alpha ∧
      ∀ y ∈ U, ‖x-y‖ < r*delta →
        ‖realHessian D.solution x-realHessian D.solution y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨delta,hd,hd8,C,hC,hestimate⟩ := actual_boundary_set_prescribed_holder_error_four
    hlam hLambda halpha halpha1 hKa hKf hM hT
  refine ⟨delta,hd,hd8,C,hC,?_⟩
  intro U hU hproper D R hR J x hx hsmall
  let d := infDist x (frontier U)
  let r := d/4
  let c := actualBoundaryFootOnDomainFour U hproper x
  obtain ⟨hdist,c0,hc0,_,hmap,_⟩ := actual_boundary_distance_ball_four hU hproper hx
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
    D.source D.solution D.source_continuous D.solution_regular D.source_holder D.equation
    c (frontier_subset_closure hc) (J.polynomial c) (J.quadratic c hc) (J.hessian_bound c hc)
    (J.frozen c hc) R (J.remainder c hc) x r hr hr1 hrR hmap hnear
  have hgrad := actual_quadratic_gradient_difference_bound_four (J.quadratic c hc) (J.hessian_bound c hc) x c
  rw [hxc] at hgrad
  have hscale : r^alpha ≤ 1 := Real.rpow_le_one hr.le hr1 halpha.le
  change ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖ ≤ (C+4*T)*r ∧
    ‖realHessian D.solution x-realHessian (J.polynomial c) c‖ ≤ C*r^alpha ∧ _
  refine ⟨?_,?_,?_⟩
  · have htriangle : ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) c‖ ≤
        ‖fderiv ℝ D.solution x-fderiv ℝ (J.polynomial c) x‖+
          ‖fderiv ℝ (J.polynomial c) x-fderiv ℝ (J.polynomial c) c‖ := by
      simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ D.solution x)
        (fderiv ℝ (J.polynomial c) x) (fderiv ℝ (J.polynomial c) c)
    have hfac : (r^alpha*r)*C ≤ r*C := by
      simpa only [mul_assoc,one_mul] using mul_le_mul_of_nonneg_right hscale (mul_nonneg hr.le hC)
    exact (htriangle.trans (add_le_add hh.1 hgrad)).trans
      ((add_le_add hfac (le_refl (T*(4*r)))).trans_eq (by ring))
  · have he : realHessian (J.polynomial c) x=realHessian (J.polynomial c) c := by
      rw [quadratic_realHessian_from_jet_zero (J.quadratic c hc) x,
        quadratic_realHessian_from_jet_zero (J.quadratic c hc) c]
    simpa only [he,mul_comm] using hh.2.1
  · intro y hy hxy
    let z := r⁻¹ • (y-x)
    have hzn : ‖z‖=r⁻¹*‖x-y‖ := by
      rw [show z=r⁻¹ • (y-x) from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),norm_sub_rev]
    have hz : z ∈ ball (0 : E) delta := by
      rw [mem_ball,dist_zero_right,hzn]
      exact (inv_mul_lt_iff₀ hr).mpr hxy
    have hxyz : x+r • z=y := by
      dsimp [z]
      rw [smul_inv_smul₀ hr.ne']
      abel
    have hp := hh.2.2 0 (mem_ball_self hd) z hz
    rw [smul_zero,add_zero,hxyz,zero_sub,norm_neg] at hp
    have hcanc : r^alpha*C*‖z‖^alpha=C*‖x-y‖^alpha := by
      rw [hzn,Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg _),Real.inv_rpow hr.le]
      field_simp
    exact hp.trans_eq hcanc

end PowerConvexity
