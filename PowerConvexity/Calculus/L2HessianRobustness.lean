import PowerConvexity.Calculus.QuadraticL2Control
import PowerConvexity.Calculus.QuadraticClass

/-! # Appendix A robustness for the genuine L2 ball of quadratic perturbations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}

/-- An actual quantitative lower bound from the full L2 perturbation ball.
This uses semidefinite real Hessians of the transforms, which follow from
local convexity and interior C2 regularity. -/
theorem L2_quadratic_robustness (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (a : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    {ε : ℝ} (hε : 0 < ε)
    (htest : ∀ q : E → ℝ,
      IsPluriharmonicQuadratic a (fun i => Complex.I • a i) q →
      quadraticL2Energy μ K q ≤ ε → ∀ v : E,
      0 ≤ realHessian (powerTransform (fun y => u y + q y)) x v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E,
      C * ‖v‖^2 ≤ realHessian (powerTransform u) x v v := by
  obtain ⟨δ, hδ, hrad⟩ := exists_square_test_L2_radius μ hK x hε
  refine ⟨2*δ*sqrtSlope (u x), mul_pos (mul_pos (by norm_num) hδ) (sqrtSlope_pos hx), ?_⟩
  apply powerHessian_lower_of_holomorphic_square_tests hu hx hδ.le
  intro ell hell v
  have hJ (i : ι) : ell.restrictScalars ℝ (Complex.I • a i) =
      Complex.I * ell.restrictScalars ℝ (a i) := by
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hq := IsPluriharmonicQuadratic_const_mul
    (realPartSquare_isPluriharmonicQuadratic (ell.restrictScalars ℝ) x a
      (fun i => Complex.I • a i) hJ) (-δ)
  have henergy := hrad (ell.restrictScalars ℝ)
    (by simpa only [ContinuousLinearMap.norm_restrictScalars] using hell)
  have h := htest (fun y => -δ * realPartSquare (ell.restrictScalars ℝ) x y) hq henergy v
  simpa only [sub_eq_add_neg, neg_mul] using h

end PowerConvexity
