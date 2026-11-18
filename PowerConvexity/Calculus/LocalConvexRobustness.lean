import PowerConvexity.Calculus.L2HessianRobustness
import PowerConvexity.Calculus.ConvexHessian

/-!
# Public local convexity hypotheses imply the quantitative robustness bound

A single strictly convex C2 function can have a degenerate Hessian.  Here the
positive Hessian bound is derived from the entire allowed quadratic family.
-/
set_option autoImplicit false
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_nonneg_of_local_convex {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) {U : Set E} (hU : IsOpen U) (hx : x ∈ U)
    (hconv : ConvexOn ℝ U f) (v : E) : 0 ≤ realHessian f x v v := by
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ContDiffAt ℝ 2 f y :=
    Filter.Eventually.and (hU.mem_nhds hx) (hf.eventually (by simp))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : ball x r ⊆ U := fun y hy => (hball hy).1
  exact realHessian_nonneg_of_convexOn isOpen_ball
    (fun y hy => (hball hy).2.contDiffWithinAt)
    (hconv.subset hsub (convex_ball x r)) (mem_ball_self hr) v

variable [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A quantitative form of frozen Appendix A `lemma:robustness`, stated using
actual local ConvexOn and genuine L2 energy rather than pointwise terminology. -/
theorem L2_quadratic_robustness_of_local_convexity {ι : Type*}
    (μ : MeasureTheory.Measure E) [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (a : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    {ε : ℝ} (hε : 0 < ε)
    (hfamily : ∀ q : E → ℝ,
      IsPluriharmonicQuadratic a (fun i => Complex.I • a i) q →
      quadraticL2Energy μ K q ≤ ε → u x + q x < 0 ∧
        ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
          ConvexOn ℝ V (powerTransform (fun y => u y + q y))) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E,
      C * ‖v‖^2 ≤ realHessian (powerTransform u) x v v := by
  apply L2_quadratic_robustness μ hK a hu hx hε
  intro q hq henergy v
  obtain ⟨hneg, V, hV, hxV, hconv⟩ := hfamily q hq henergy
  have hdiff := powerTransform_contDiffAt
    (hu.add (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt) hneg
  exact realHessian_nonneg_of_local_convex hdiff hV hxV hconv v

end PowerConvexity
