import PowerConvexity.Algebra.VariableDensityBoundaryNormalTwo
import PowerConvexity.Calculus.ClosureVariableDensity
import PowerConvexity.Calculus.VariableDensityBoundaryNormalTwo
import PowerConvexity.Calculus.ConvexDefiningCurvature

/-! # A genuine bounded-density pure normal boundary estimate from mixed entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem classicalDirichlet_boundary_normal_upper_of_mixed_variable_density_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    {ρ : E → ℝ} (hρ : ContinuousOn ρ (closure U))
    (hρlower : ∀ x ∈ closure U, 1 ≤ ρ x)
    {D : ℝ} (hρupper : ∀ x ∈ closure U, ρ x ≤ D)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (ρ x : ℂ))
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (htan : fderiv ℝ f x (b 1) = 0)
    {delta M : ℝ} (hd : 0 < delta)
    (hLevi : delta ≤ (J.complexField a b x 0 0).re)
    (hmixed : Complex.normSq (J.complexField a b x 0 1) ≤ M) :
    J.hessian x (a 1) (a 1) ≤ 4*(D+M)/delta := by
  have hdlo (y : E) (hy : y ∈ U) : 1 ≤ (complexHessian a b u y).det.re := by
    rw [hdet y hy,Complex.ofReal_re]
    exact hρlower y (subset_closure hy)
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_of_det_lower_two
    hU hconv hK hu J hb a b hab hpsh hdlo hx hf hfx hDf hdef
  have hbt : 0 ≤ J.hessian x (b 1) (b 1) := by
    rw [hH (b 1) (b 1) htan htan]
    exact mul_nonneg hlam.le
      (definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef (b 1) htan)
  have hρc : ContinuousOn (fun y => (ρ y : ℂ)) (closure U) :=
    Complex.continuous_ofReal.comp_continuousOn hρ
  have hA := closure_complexField_posDef_of_variableDensity J hU hu a b hρc
    (fun y hy => Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (hρlower y hy))))
    hdet hpsh x (frontier_subset_closure hx)
  have hAd : (J.complexField a b x).det.re ≤ D := by
    rw [closure_complexField_variableDensity J hU hu a b hρc hdet x (frontier_subset_closure hx),
      Complex.ofReal_re]
    exact hρupper x (frontier_subset_closure hx)
  have hn := hermitian_det_upper_normal_diagonal_bound_two hA hAd hd hLevi hmixed
  have he : (J.complexField a b x 1 1).re =
      (J.hessian x (a 1) (a 1)+J.hessian x (b 1) (b 1))/4 := by
    simp [ClosureC2Jet.complexField,jetComplexHessian,Complex.mul_re,Complex.mul_im]
    <;> ring
  calc
    J.hessian x (a 1) (a 1) ≤ 4*(J.complexField a b x 1 1).re := by rw [he]; linarith
    _ ≤ 4*((D+M)/delta) := mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = 4*(D+M)/delta := by ring

end PowerConvexity
