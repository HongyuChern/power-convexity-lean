import PowerConvexity.Analysis.ActualUniformRescaledDensityHessianHolderTwo
import PowerConvexity.Analysis.ActualUniformTangentialGradientModulusFour
import PowerConvexity.Calculus.RealHessianBlockNormTwo

/-! # Radius-uniform actual C1 Holder control of Du(T)

The nonlinear interior estimate is applied to the same solution and density.
The exponent and constant precede the physical radius, center and response;
only the already available C2 norm of u and C2 norm of T enter.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_uniform_rescaled_tangential_gradient_four
    {M D L Csrc G T₀ D₀ K₀ : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc) (hG : 0 ≤ G)
    (hT₀ : 0 ≤ T₀) (hD₀ : 0 ≤ D₀) (hK₀ : 0 ≤ K₀) :
    ∃ beta C : ℝ, 0 < beta ∧ beta < 1 ∧ 0 < C ∧
      ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ (c : E) (u f : E → ℝ) (T : E → E),
      ContDiffOn ℝ 4 u (ball c (2*R)) → ContDiffOn ℝ 2 f (ball c (2*R)) →
      (∀ x ∈ ball c (2*R),
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball c (2*R), (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball c (2*R), 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball c (2*R), ‖realHessian u x‖ ≤ M) →
      (∀ x ∈ ball c (2*R), ∀ y ∈ ball c (2*R), |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball c (2*R), ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      (∀ x ∈ ball c R, ‖fderiv ℝ u x‖ ≤ G) → ContDiffOn ℝ 2 T (ball c R) →
      (∀ x ∈ ball c R, ‖T x‖ ≤ T₀) →
      (∀ x ∈ ball c R, ‖fderiv ℝ T x‖ ≤ D₀) →
      (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ T) x‖ ≤ K₀) →
      ∀ x ∈ ball c R, ∀ y ∈ ball c R,
        ‖fderiv ℝ (fun z => fderiv ℝ u z (T z)) x-
          fderiv ℝ (fun z => fderiv ℝ u z (T z)) y‖ ≤ C*(‖x-y‖/R)^beta := by
  obtain ⟨beta,C0,hb,hb1,hC0,hholder⟩ :=
    actual_uniform_rescaled_density_hessian_holder_two hM hD hL hCsrc
  let A := T₀*(16*C0)+2*(2*M*D₀+G*K₀)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨beta,A+1,hb,hb1,by positivity,?_⟩
  intro R hR hR1 c u f T hu hf hdet hpos hfb hH hLip hsource huD hT hTv hTD hTH
  have hsub : ball c R ⊆ ball c (2*R) := ball_subset_ball (by linarith)
  have hreal : ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖realHessian u x-realHessian u y‖ ≤ (16*C0)*(‖x-y‖/R)^beta := by
    intro x hx y hy
    apply (realHessian_norm_sub_le_sixteen_block_norm_two u x y).trans
    exact (mul_le_mul_of_nonneg_left
      (hholder R hR hR1 c u f hu hf hdet hpos hfb hH hLip hsource x hx y hy)
      (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)
  have hh := actual_variable_directional_gradient_holder_ball_four hR hR1 hG hM hT₀ hD₀ hK₀
    (show 0 ≤ 16*C0 by positivity) hb.le hb1.le ((hu.of_le (by norm_num)).mono hsub) hT
    huD (fun x hx => hH x (hsub hx)) hTv hTD hTH hreal
  intro x hx y hy
  exact (hh x hx y hy).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith)
      (Real.rpow_nonneg (div_nonneg (norm_nonneg _) hR.le) beta))

end PowerConvexity
