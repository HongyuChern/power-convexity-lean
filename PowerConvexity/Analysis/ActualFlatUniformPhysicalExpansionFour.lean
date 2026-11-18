import PowerConvexity.Analysis.ActualFlatQuadraticPullbackFour

/-! # Uniform actual physical boundary expansions without an assumed frozen identity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_uniform_physical_expansion_four {lam Lambda alpha Ka Kf F B : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∃ s > 0, s ≤ (1/8 : ℝ) ∧ s^alpha ≤ (1/2 : ℝ) ∧
    ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧ ∃ C > 0,
    ∀ D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B,
    ∀ c : E, inner ℝ N c=0 → ‖c‖ ≤ (1/2 : ℝ) →
    ∃ P : E → ℝ, IsQuadraticPolynomial P ∧
      (∀ x : E, inner ℝ N x=0 → P x=0) ∧
      (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian P c i j) = -D.source c ∧
      ∀ n : ℕ, ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ R*s^n →
        |D.solution x-P x| ≤ C*(1/2 : ℝ)^n*(R*s^n)^2 := by
  obtain ⟨r,hr,hr1,s,hs,hs8,hsa,hexp⟩ := actual_flat_uniform_centered_expansion_four
    hlam hLambda halpha hKa hKf hF hB
  let L : ℝ := max 1 ((Real.sqrt lam)⁻¹)
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨s,hs,hs8,hsa,?_⟩
  intro N hN
  obtain ⟨R,hR,hR1,C,hC,hP⟩ := hexp N hN
  have hsmall : r*R/L ≤ 1 := by
    apply (div_le_one hLp).mpr
    have hh := mul_le_mul hr1 hR1 hR.le zero_le_one
    exact (by simpa only [one_mul] using hh : r*R ≤ 1).trans hL
  refine ⟨r*R/L,div_pos (mul_pos hr hR) hLp,hsmall,
    C*(L/r)^2,mul_pos hC (sq_pos_of_pos (div_pos hLp hr)),?_⟩
  intro D c hc hcn
  obtain ⟨G,hfreeze,hGn,hInv,⟨k,hk,hNv⟩,p,hpq,hp0,hpD,hpH,hptr,herr⟩ := hP D c hc hcn
  let P := actualPhysicalQuadraticTwo G (G.symm c) r p
  refine ⟨P,actual_physical_quadratic_isQuadratic_two G (G.symm c) r hpq,
    actual_flat_physical_quadratic_zero_four G hk hc hNv hp0,?_,?_⟩
  · simpa only [G.apply_symm_apply] using
      actual_physical_quadratic_frozen_equation_two G (G.symm c) hr hfreeze hpq (hptr 0)
  · exact actual_flat_physical_quadratic_error_four G hr hLp hk hc hNv hInv herr

end PowerConvexity
