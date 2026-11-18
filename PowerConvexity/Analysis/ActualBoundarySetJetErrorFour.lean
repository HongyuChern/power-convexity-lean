import PowerConvexity.Analysis.ActualBoundaryResidualScalingBoundsFour
import PowerConvexity.Analysis.ActualUniformCenteredResidualJetsFour

/-! # Boundary-to-interior jet control in the original domain, without flattening -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_boundary_set_residual_bound_four {U : Set E} {c x : E} {u q : E → ℝ}
    {R r gamma M : ℝ} (hr : 0 < r) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M)
    (hsmall : 6*r < R)
    (herr : ∀ y ∈ U, ‖y-c‖ < R → |u y-q y| ≤ M*‖y-c‖^2*‖y-c‖^gamma)
    (hmap : MapsTo (fun z : E => x+r • z) (ball (0 : E) 2) U)
    (hnear : ∀ z ∈ ball (0 : E) 2, ‖(x+r • z)-c‖ ≤ 6*r) :
    ∀ z ∈ ball (0 : E) 2,
      |actualCenteredResidualFour x r (r^gamma) u q z| ≤ 36*(6 : ℝ)^gamma*M := by
  intro z hz
  have hp := Real.rpow_pos_of_pos hr gamma
  have hh := herr _ (hmap hz) ((hnear z hz).trans_lt hsmall)
  simp only [actualCenteredResidualFour,abs_mul,abs_of_pos (inv_pos.mpr hp),
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr))]
  exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (r^gamma)⁻¹*(r^2)⁻¹)).trans
    (actual_boundary_scaled_remainder_bound_four hr hgamma hM (norm_nonneg _) (hnear z hz))

theorem actual_boundary_set_interior_jet_error_four {lam Lambda alpha gamma Ka Kf M T : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (hga : gamma ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ C ≥ 0, ∀ U : Set E, IsOpen U → ∀ A : EllipticCoeff (2+2) U,
    lam ≤ A.lam → A.Λ ≤ Lambda → (∀ x ∈ U, (A.a x).PosDef) →
    (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U) →
    (∀ x ∈ U, ∀ j, (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) →
    (∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha) →
    ∀ f u : E → ℝ, ContDiffOn ℝ 1 f U → ContDiffOn ℝ 2 u U →
    (∀ x ∈ closure U, ∀ y ∈ closure U, |f x-f y| ≤ Kf*‖x-y‖^alpha) →
    (∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j) = -f x) →
    ∀ c ∈ closure U, ∀ q : E → ℝ, IsQuadraticPolynomial q → ‖realHessian q 0‖ ≤ T →
    ((∑ i, ∑ j, A.a c i j*euclideanHessian q c i j) = -f c) →
    ∀ R : ℝ, (∀ y ∈ U, ‖y-c‖ < R → |u y-q y| ≤ M*‖y-c‖^2*‖y-c‖^gamma) →
    ∀ x : E, ∀ r : ℝ, 0 < r → r ≤ 1 → 6*r < R →
    MapsTo (fun z : E => x+r • z) (ball (0 : E) 2) U →
    (∀ z ∈ ball (0 : E) 2, ‖(x+r • z)-c‖ ≤ 6*r) →
    ‖fderiv ℝ u x-fderiv ℝ q x‖ ≤ (r^gamma*r)*C ∧
      ‖realHessian u x-realHessian q x‖ ≤ r^gamma*C := by
  let K := Kf+16*Ka*T
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨C,hC,hestimate⟩ := actual_uniform_centered_residual_jets_four hlam hLambda hKa hK
    (show 0 ≤ K*(6 : ℝ)^alpha by positivity)
    (show 0 ≤ 36*(6 : ℝ)^gamma*M by positivity) halpha
  refine ⟨C,hC,?_⟩
  intro U hU A hlo hhi hpos hreg hdiv hA f u hf hu hfH hpde c hc q hq hqH heq R herr x r hr hr1 hsmall hmap hnear
  have hmapC : MapsTo (fun z : E => x+r • z) (ball (0 : E) 2) (closure U) :=
    fun z hz => subset_closure (hmap hz)
  have hpow := actual_boundary_scale_exponent_bound_four hr hr1 hga
  have hAhold := actual_affine_holder_comp_four x hr hmapC hA
  have hqhold := actual_quadratic_residual_source_holder_four hq hT hqH hA hfH
  have hfhold := actual_centered_scaled_source_holder_four x hr (Real.rpow_pos_of_pos hr gamma) hmapC hqhold
  have hfgrowth := actual_quadratic_residual_source_growth_four hq hT hqH hA hfH hc heq
  apply hestimate U hU A hlo hhi hpos hreg hdiv x r (r^gamma) hr
    (Real.rpow_pos_of_pos hr gamma) hmap f u q hf hu hq hpde
  · intro z hz w hw
    have hKaR : Ka*r^alpha ≤ Ka :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_one hr.le hr1 halpha.le) hKa).trans_eq (mul_one Ka)
    exact (hAhold z hz w hw).trans (mul_le_mul_of_nonneg_right hKaR
      (Real.rpow_nonneg (norm_nonneg _) alpha))
  · intro z hz w hw
    have hfac : (r^gamma)⁻¹*K*r^alpha ≤ K := by
      calc
        _ = K*((r^gamma)⁻¹*r^alpha) := by ring
        _ ≤ K*1 := mul_le_mul_of_nonneg_left hpow hK
        _ = K := mul_one K
    exact (hfhold z hz w hw).trans (mul_le_mul_of_nonneg_right hfac
      (Real.rpow_nonneg (norm_nonneg _) alpha))
  · intro z hz
    rw [abs_mul,abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hr gamma))]
    exact (mul_le_mul_of_nonneg_left (hfgrowth _ (hmapC hz))
      (inv_pos.mpr (Real.rpow_pos_of_pos hr gamma)).le).trans
      (actual_boundary_scaled_source_growth_four hr hr1 halpha.le hga hK (norm_nonneg _) (hnear z hz))
  · exact actual_boundary_set_residual_bound_four hr hgamma.le hM hsmall herr hmap hnear

end PowerConvexity
