import PowerConvexity.Analysis.ActualFlatCenteredNormalizationFour
import PowerConvexity.Analysis.ActualFlatPhysicalExpansionFour

/-! # Uniform actual boundary-centred expansions before choosing the solution -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_uniform_centered_expansion_four {lam Lambda alpha Ka Kf F B : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∃ r > 0, r ≤ 1 ∧ ∃ s > 0, s ≤ (1/8 : ℝ) ∧ s^alpha ≤ (1/2 : ℝ) ∧
    ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧ ∃ C > 0,
    ∀ D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B,
    ∀ c : E, inner ℝ N c=0 → ‖c‖ ≤ (1/2 : ℝ) →
    ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G (D.coeff.a c)=1 ∧
      ‖G.toContinuousLinearMap‖ ≤ max 1 (Real.sqrt Lambda) ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ max 1 ((Real.sqrt lam)⁻¹) ∧
      (∃ k > 0, ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v) ∧
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        ‖fderiv ℝ p 0‖ ≤ C ∧ (∀ x, ‖realHessian p x‖ ≤ C) ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace = -(r^2*D.source c)) ∧
        ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (R*s^n),
          |D.solution (c+G (r • x))-p x| ≤ C*(1/2 : ℝ)^n*(R*s^n)^2 := by
  let M : ℝ := max 1 (Real.sqrt Lambda)
  let L : ℝ := max 1 ((Real.sqrt lam)⁻¹)
  have hM : 1 ≤ M := le_max_left _ _
  have hL : 1 ≤ L := le_max_left _ _
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hLp : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨r,hr,hr1,hrM⟩ := actual_flat_centered_physical_scale_four hMp
  obtain ⟨s,hs,hs8,hsa,hexp⟩ := actual_flat_physical_quadratic_expansion_four
    (div_pos hlam (sq_pos_of_pos hMp)) (mul_pos hLambda (sq_pos_of_pos hLp)) halpha
    (show 0 ≤ L^2*Ka*(r*M)^alpha by positivity)
    (show 0 ≤ r^2*Kf*(r*M)^alpha by positivity) hB
    (show 0 ≤ r^2*F by positivity)
  refine ⟨r,hr,hr1,s,hs,hs8,hsa,?_⟩
  intro N hN
  obtain ⟨R,hR,hR1,C,hC,hP⟩ := hexp N hN
  refine ⟨R,hR,hR1,C,hC,?_⟩
  intro D c hc hcn
  obtain ⟨G,hfreeze,hGn,hInv,k,hk,hNv⟩ := actual_flat_closed_input_normalizer_four
    hN hlam hLambda D hc hcn
  have hmap := actual_flat_centered_physical_maps_four G hk hr hMp hc hcn hNv hGn hrM
  let D' := actualFlatCenteredNormalizeFour G hr halpha.le hKa hKf hM hL D hc hNv
    hGn hInv hmap.1 hmap.2 hfreeze
  have hfc : |D'.source 0| ≤ r^2*F := by
    change |r^2*D.source (c+G (r • (0 : E)))| ≤ r^2*F
    simp only [smul_zero,map_zero,add_zero,abs_mul,abs_of_nonneg (sq_nonneg r)]
    apply mul_le_mul_of_nonneg_left (D.source_bound c ?_) (sq_nonneg r)
    refine ⟨?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hcn.trans (by norm_num : (1/2 : ℝ) ≤ 1)
    · change 0 ≤ inner ℝ N c; rw [hc]
  obtain ⟨p,hpq,hp0,hpD,hpH,hptr,herr⟩ := hP D' hfc
  refine ⟨G,hfreeze,hGn,hInv,⟨k,hk,hNv⟩,p,hpq,hp0,hpD,hpH,?_,?_⟩
  · intro x
    simpa only [D',actualFlatCenteredNormalizeFour_source,smul_zero,map_zero,add_zero] using hptr x
  · intro n x hx
    exact herr n x hx

end PowerConvexity
