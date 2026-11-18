import PowerConvexity.Analysis.ActualFlatBoundaryGradientCompatibilityFour
import PowerConvexity.Analysis.ActualFlatInteriorBoundaryJetErrorFour

/-! # Actual boundary jets with uniform interior-to-boundary derivative errors -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualFlatFullJetControlFour {N : E} {lam Lambda alpha Ka Kf F B : ℝ}
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B)
    (R gamma M T beta H C : ℝ) where
  polynomial : E → E → ℝ
  quadratic : ∀ c ∈ actualFlatBoundaryDiskFour N, IsQuadraticPolynomial (polynomial c)
  zero : ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ x : E, inner ℝ N x=0 → polynomial c x=0
  first_jet : ∀ c ∈ actualFlatBoundaryDiskFour N,
    HasFDerivWithinAt D.solution (fderiv ℝ (polynomial c) c) {x : E | 0 ≤ inner ℝ N x} c
  frozen : ∀ c ∈ actualFlatBoundaryDiskFour N,
    (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian (polynomial c) c i j) = -D.source c
  remainder : ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ z : E,
    0 ≤ inner ℝ N z → ‖z-c‖ < R/2 →
    |D.solution z-polynomial c z| ≤ M*‖z-c‖^2*‖z-c‖^gamma
  gradient_bound : ∀ c ∈ actualFlatBoundaryDiskFour N, ‖fderiv ℝ (polynomial c) c‖ ≤ T
  hessian_bound : ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ z : E, ‖realHessian (polynomial c) z‖ ≤ T
  gradient_compatibility : ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ d ∈ actualFlatBoundaryDiskFour N,
    ‖c-d‖ < R/8 → ‖fderiv ℝ (polynomial c) c-fderiv ℝ (polynomial d) d‖ ≤ (1088*M+T)*‖c-d‖
  hessian_compatibility : ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ d ∈ actualFlatBoundaryDiskFour N,
    ‖c-d‖ < R/4 → ‖realHessian (polynomial c) c-realHessian (polynomial d) d‖ ≤ H*‖c-d‖^beta
  interior_error : ∀ x ∈ actualFlatUpperBallFour N (1/4 : ℝ), 6*(inner ℝ N x/4) < R/2 →
    let c := actualFlatBoundaryFootFour N x
    ‖fderiv ℝ D.solution x-fderiv ℝ (polynomial c) c‖ ≤ (C+4*T)*(inner ℝ N x/4) ∧
      ‖realHessian D.solution x-realHessian (polynomial c) c‖ ≤ C*(inner ℝ N x/4)^gamma

theorem actual_flat_full_jet_control_four {lam Lambda alpha Ka Kf F B : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧ gamma ≤ alpha ∧ ∃ M ≥ 0, ∃ T ≥ 0,
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ H ≥ 0, ∃ C ≥ 0,
    ∀ D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B,
      Nonempty (ActualFlatFullJetControlFour D R gamma M T beta H C) := by
  intro N hN
  obtain ⟨R,hR,hR1,gamma,hg,hg1,hga,M,hM,beta,hbeta,hbeta1,H,hH,hfield⟩ :=
    actual_flat_boundary_jet_field_four hlam hLambda halpha hKa hKf hF hB N hN
  obtain ⟨T,hT,hbound⟩ := actual_flat_quadratic_remainder_jet_bound_four hR hg.le hM hB
  obtain ⟨C,hC,hinterior⟩ := actual_flat_interior_boundary_jet_error_four
    hlam hLambda halpha hg hga hKa hKf hM hT
  refine ⟨R,hR,hR1,gamma,hg,hg1,hga,M,hM,T,hT,beta,hbeta,hbeta1,H,hH,C,hC,?_⟩
  intro D
  obtain ⟨P,hdata,hholder⟩ := hfield D
  have hbounds (c : E) (hc : c ∈ actualFlatBoundaryDiskFour N) :=
    hbound N hN c hc D.solution (P c) (hdata c hc).1 D.solution_bound (hdata c hc).2.2.2.2
  refine ⟨{
    polynomial := P
    quadratic := fun c hc => (hdata c hc).1
    zero := fun c hc => (hdata c hc).2.1
    first_jet := fun c hc => (hdata c hc).2.2.1
    frozen := fun c hc => (hdata c hc).2.2.2.1
    remainder := fun c hc => (hdata c hc).2.2.2.2
    gradient_bound := fun c hc => (hbounds c hc).1
    hessian_bound := fun c hc => (hbounds c hc).2
    gradient_compatibility := actual_halfspace_quadratic_field_gradient_lipschitz_four hN
      (fun c hc => le_of_eq hc.1.symm) hR hR1 hg.le hM
      (fun c hc => (hdata c hc).1) (fun c hc => (hbounds c hc).2 0)
      (fun c hc => (hdata c hc).2.2.2.2)
    hessian_compatibility := hholder
    interior_error := ?_
  }⟩
  intro x hx hsmall
  let c := actualFlatBoundaryFootFour N x
  let r := inner ℝ N x/4
  obtain ⟨hr,hr1,hc,hdist,hmap,hnear⟩ := actual_flat_interior_ball_geometry_four hN hx
  have hh := hinterior N hN D x hx R hR (P c) (hdata c hc).1 ((hbounds c hc).2 0)
    (hdata c hc).2.2.2.1 (hdata c hc).2.2.2.2 hsmall
  have hgrad := actual_quadratic_gradient_difference_bound_four (hdata c hc).1 ((hbounds c hc).2 0) x c
  rw [hdist] at hgrad
  change 0 < r at hr
  change r ≤ 1 at hr1
  change ‖fderiv ℝ D.solution x-fderiv ℝ (P c) x‖ ≤ (r^gamma*r)*C ∧
    ‖realHessian D.solution x-realHessian (P c) x‖ ≤ r^gamma*C at hh
  change ‖fderiv ℝ (P c) x-fderiv ℝ (P c) c‖ ≤ T*(4*r) at hgrad
  change ‖fderiv ℝ D.solution x-fderiv ℝ (P c) c‖ ≤ (C+4*T)*r ∧
    ‖realHessian D.solution x-realHessian (P c) c‖ ≤ C*r^gamma
  have hscale : r^gamma ≤ 1 := Real.rpow_le_one hr.le hr1 hg.le
  constructor
  · have htriangle : ‖fderiv ℝ D.solution x-fderiv ℝ (P c) c‖ ≤
        ‖fderiv ℝ D.solution x-fderiv ℝ (P c) x‖+‖fderiv ℝ (P c) x-fderiv ℝ (P c) c‖ := by
      simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ D.solution x) (fderiv ℝ (P c) x) (fderiv ℝ (P c) c)
    have hfirst := htriangle.trans (add_le_add hh.1 hgrad)
    have hfac : (r^gamma*r)*C ≤ r*C := by
      simpa only [mul_assoc,one_mul] using mul_le_mul_of_nonneg_right hscale (mul_nonneg hr.le hC)
    calc
      _ ≤ (r^gamma*r)*C+T*(4*r) := hfirst
      _ ≤ r*C+T*(4*r) := add_le_add hfac (le_refl _)
      _ = (C+4*T)*r := by ring
  · have he : realHessian (P c) x=realHessian (P c) c := by
      rw [quadratic_realHessian_from_jet_zero (hdata c hc).1 x,
        quadratic_realHessian_from_jet_zero (hdata c hc).1 c]
    simpa only [he,mul_comm] using hh.2

end PowerConvexity
