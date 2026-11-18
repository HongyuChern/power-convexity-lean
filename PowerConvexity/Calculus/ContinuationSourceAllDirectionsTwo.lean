import PowerConvexity.Calculus.ContinuationDensityDerivativeBoundsTwo

/-! # The actual density source bound in arbitrary real directions.
The already constructed unit-direction constant is retained. Homogeneity
introduces exactly norm(v)^2; no direction-dependent compactness is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem density_second_source_smul_direction
    (f : E → ℝ) (x v : E) (a : ℝ) :
    (realHessian f x (a • v) (a • v)*f x-(fderiv ℝ f x (a • v))^2)/(f x)^2 =
      a^2*((realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) := by
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem density_second_source_lower_all_directions
    {f : E → ℝ} {x : E} {C : ℝ}
    (hunit : ∀ v : E, ‖v‖ = 1 →
      -C ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) (v : E) :
    -(C*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2 := by
  by_cases hv : v = 0
  · subst v
    simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : ‖v‖ • w = v := by
    dsimp only [w]
    rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have hl := mul_le_mul_of_nonneg_left (hunit w hw) (sq_nonneg ‖v‖)
  rw [← density_second_source_smul_direction f x w ‖v‖,he] at hl
  nlinarith only [hl]

theorem dirichletContinuationDensityTwo_uniform_second_source_all_directions
    [FiniteDimensional ℝ E]
    (a b : Fin 2 → E) {V : Set E} (hK : IsCompact (closure V))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V, ∀ v : E,
      -(C*‖v‖^2) ≤ (realHessian (dirichletContinuationDensityTwo a b w s) x v v*
          dirichletContinuationDensityTwo a b w s x-
          (fderiv ℝ (dirichletContinuationDensityTwo a b w s) x v)^2)/
            (dirichletContinuationDensityTwo a b w s x)^2 := by
  obtain ⟨C,hC,hunit⟩ := dirichletContinuationDensityTwo_uniform_second_source a b hK hw hd
  exact ⟨C,hC,fun s hs x hx => density_second_source_lower_all_directions (hunit s hs x hx)⟩

end PowerConvexity
