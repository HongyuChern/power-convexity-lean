import PowerConvexity.Analysis.NonpositiveBoundaryMaximum
import CHS.Calculus.QuadraticPerturbation

/-! # A weak Hessian maximum principle with the actual Dirichlet barrier

The barrier has zero boundary values. Only pointwise positivity of its
linearization is used; no uniform ellipticity or boundary extension of the
coefficients is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nonpositive_of_nonnegative_contraction_with_zero_boundary_barrier
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f φ : E → ℝ} (hfc : ContinuousOn f (closure U))
    (hf : ContDiffOn ℝ 2 f U) (hfb : ∀ x ∈ frontier U, f x ≤ 0)
    (hφc : ContinuousOn φ (closure U)) (hφ : ContDiffOn ℝ 2 φ U)
    (hφb : ∀ x ∈ frontier U, φ x = 0)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ U, HessianPositive (L x))
    (hfL : ∀ x ∈ U, 0 ≤ L x (realHessian f x))
    (hφL : ∀ x ∈ U, 0 < L x (realHessian φ x)) :
    ∀ x ∈ closure U, f x ≤ 0 := by
  intro x hx
  by_cases hxU : x ∈ U
  · by_contra hn
    have hfx : 0 < f x := lt_of_not_ge hn
    let ε : ℝ := f x / (2 * (|φ x| + 1))
    have hden : 0 < 2 * (|φ x| + 1) := by positivity
    have hε : 0 < ε := div_pos hfx hden
    have he : ε * (2 * (|φ x| + 1)) = f x := by
      dsimp [ε]
      exact div_mul_cancel₀ _ hden.ne'
    let g : E → ℝ := fun y => f y + ε * φ y
    have hgc : ContinuousOn g (closure U) := hfc.add (continuousOn_const.mul hφc)
    have hg : ContDiffOn ℝ 2 g U := hf.add (contDiffOn_const.mul hφ)
    have hgb : ∀ y ∈ frontier U, g y ≤ 0 := by
      intro y hy
      simpa only [g,hφb y hy,mul_zero,add_zero] using hfb y hy
    have hgp : ∀ y ∈ U, 0 < L y (realHessian g y) := by
      intro y hy
      dsimp only [g]
      rw [realHessian_add (hf.contDiffAt (hU.mem_nhds hy))
        (contDiffAt_const.mul (hφ.contDiffAt (hU.mem_nhds hy))),
        realHessian_const_mul,map_add,map_smul,smul_eq_mul]
      exact add_pos_of_nonneg_of_pos (hfL y hy) (mul_pos hε (hφL y hy))
    have hneg := negative_of_positive_contraction_nonpositive_boundary
      hU hK hgc hg hgb L hL hgp x hxU
    have hlow : - (ε * |φ x|) ≤ ε * φ x := by
      have hh := mul_le_mul_of_nonneg_left (neg_abs_le (φ x)) hε.le
      simpa only [mul_neg] using hh
    change f x + ε * φ x < 0 at hneg
    nlinarith
  · exact hfb x (by rw [hU.frontier_eq]; exact ⟨hx,hxU⟩)

end PowerConvexity
