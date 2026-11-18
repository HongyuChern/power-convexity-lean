import PowerConvexity.Calculus.StrictSubsolutionBoundaryJetBoundsTwo

/-! # Actual tangential bilinear Hessian bounds from a fixed subsolution

The coefficient in the true boundary identity Du=mu Df is controlled by the
fixed C1 estimate. Both tangent directions are arbitrary real tangent vectors.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem positive_multiple_coefficient_le_norm_bound
    (D L : E →L[ℝ] ℝ) (hD : D ≠ 0) {mu C : ℝ} (hmu : 0 < mu)
    (hL : L = mu • D) (hbound : ‖L‖ ≤ C) : mu ≤ C/‖D‖ := by
  have hn : 0 < ‖D‖ := (norm_pos_iff (a := D)).mpr hD
  have hh := hbound
  rw [hL,norm_smul mu D,Real.norm_eq_abs,abs_of_pos hmu] at hh
  exact (le_div_iff₀ hn).mpr hh

theorem strict_subsolution_boundary_tangent_bilinear_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ U, (complexHessian a b w y).PosDef)
    (hwd : ∀ y ∈ U, (1 : ℂ) < (complexHessian a b w y).det)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (v z : E) (hv : fderiv ℝ f x v = 0) (hz : fderiv ℝ f x z = 0) :
    ∃ M ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian a b u y).PosDef) →
      (∀ y ∈ U, (complexHessian a b u y).det = 1) → |J.hessian x v z| ≤ M := by
  obtain ⟨C,hC,hfirst⟩ := strict_subsolution_uniform_boundary_first_tangent_bounds_two
    hU hconv hK hboundary a b hab hw hwb hwp hwd
  let M : ℝ := C/‖fderiv ℝ f x‖*|realHessian f x v z|
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro u J hu hub hup hud
  obtain ⟨mu,hmu,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  have hm := positive_multiple_coefficient_le_norm_bound (fderiv ℝ f x) (J.derivative x)
    hDf hmu hJ ((hfirst u J hu hub hup hud x hx).1)
  rw [hH v z hv hz,abs_mul,abs_of_pos hmu]
  exact mul_le_mul_of_nonneg_right hm (abs_nonneg _)

end PowerConvexity
