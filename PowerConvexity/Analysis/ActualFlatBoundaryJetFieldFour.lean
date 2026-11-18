import PowerConvexity.Analysis.ActualFlatCenteredFirstDerivativeFour

/-! # The actual boundary first jet and a compatible quadratic Hessian field -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_boundary_jet_field_four {lam Lambda alpha Ka Kf F B : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧ gamma ≤ alpha ∧ ∃ M ≥ 0,
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ H ≥ 0,
    ∀ D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B,
    ∃ P : E → E → ℝ,
      (∀ c ∈ actualFlatBoundaryDiskFour N,
        IsQuadraticPolynomial (P c) ∧
        (∀ x : E, inner ℝ N x=0 → P c x=0) ∧
        HasFDerivWithinAt D.solution (fderiv ℝ (P c) c) {x : E | 0 ≤ inner ℝ N x} c ∧
        (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian (P c) c i j) = -D.source c ∧
        ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ < R/2 →
          |D.solution x-P c x| ≤ M*‖x-c‖^2*‖x-c‖^gamma) ∧
      ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ d ∈ actualFlatBoundaryDiskFour N,
        ‖c-d‖ < R/4 →
        ‖realHessian (P c) c-realHessian (P d) d‖ ≤ H*‖c-d‖^beta := by
  obtain ⟨s,hs,hs8,hsa,hfield⟩ := actual_flat_boundary_quadratic_field_four
    hlam hLambda halpha hKa hKf hF hB
  intro N hN
  obtain ⟨R,hR,hR1,C,hC,beta,hbeta,hbeta1,H,hH,hP⟩ := hfield N hN
  obtain ⟨gamma₀,hg₀,hg₀1,M,hM,hrem⟩ :=
    actual_flat_centered_geometric_remainder_four hR hs (hs8.trans_lt (by norm_num)) hC.le
  let gamma := min gamma₀ alpha
  have hg : 0 < gamma := lt_min hg₀ halpha
  have hgg : gamma ≤ gamma₀ := min_le_left _ _
  refine ⟨R,hR,hR1,gamma,hg,hgg.trans_lt hg₀1,min_le_right _ _,M,hM,beta,hbeta,hbeta1,H,hH,?_⟩
  intro D
  obtain ⟨P,hdata,hholder⟩ := hP D
  refine ⟨P,?_,hholder⟩
  intro c hc
  have hp := hdata c hc
  have hzero : D.solution c=P c c := by
    rw [D.solution_zero c (by
      simpa only [mem_closedBall,dist_zero_right] using hc.2.trans (by norm_num : (1/2 : ℝ) ≤ 1)) hc.1,
      hp.2.1 c hc.1]
  have herr := hrem N c D.solution (P c) hc.1 hzero hp.2.2.2
  refine ⟨hp.1,hp.2.1,
    actual_flat_centered_remainder_hasFDerivWithinAt_four hp.1 hc.1 hR hM hg₀.le herr,hp.2.2.1,?_⟩
  intro x hx hnear
  have hn : ‖x-c‖ ≤ 1 := by linarith
  have hpw : ‖x-c‖^gamma₀ ≤ ‖x-c‖^gamma :=
    Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hn hg.le hgg
  exact (herr x hx hnear).trans (mul_le_mul_of_nonneg_left hpw (by positivity))

end PowerConvexity
