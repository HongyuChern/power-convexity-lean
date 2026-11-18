import PowerConvexity.Calculus.LocalConvexRobustness

/-!
# Uniform constants in the quadratic robustness estimate

The perturbation radius is uniform over a bounded set of centers.  The Hessian
constant is uniform when the negative values of u have a common lower bound.
These are the quantitative data needed before passing to a deformation limit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_uniform_square_test_L2_radius (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K X : Set E} (hK : IsCompact K) (hX : Bornology.IsBounded X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c ∈ X, ∀ ell : E →L[ℝ] ℂ, ‖ell‖ = 1 →
      quadraticL2Energy μ K (fun y => -δ * realPartSquare ell c y) ≤ ε := by
  obtain ⟨R,hR,hbR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨T,hT,hbT⟩ := hX.exists_pos_norm_le
  let S := R+T
  have hS : 0 ≤ S := by dsimp [S]; linarith
  let D := S^4 * μ.real K
  have hD : 0 ≤ D := mul_nonneg (pow_nonneg hS _) measureReal_nonneg
  let δ := min 1 (ε/(D+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδD : δ*(D+1) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < D+1)).mp (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro c hc ell hell
  have hb (y : E) (hy : y ∈ K) : ‖y-c‖ ≤ S :=
    (norm_sub_le y c).trans (add_le_add (hbR y hy) (hbT c hc))
  have h := realPartSquare_L2_bound μ hK ell c hS hb δ
  simp only [hell,one_pow,mul_one] at h
  have hs : δ^2 ≤ δ := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs hD
  have hf : δ^2*D ≤ ε := by nlinarith
  exact h.trans (by simpa only [D,mul_assoc] using hf)

theorem sqrtSlope_mono_negative {s t : ℝ} (hst : s ≤ t) (ht : t < 0) :
    sqrtSlope s ≤ sqrtSlope t := by
  unfold sqrtSlope
  apply one_div_le_one_div_of_le
  · exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (neg_pos.mpr ht))
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (neg_le_neg hst)) (by norm_num)

variable [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The lower bound depends only on the stated uniform data, not on a
chosen center or a particular potential in a deformation family. -/
theorem uniform_L2_quadratic_robustness (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K X : Set E} (hK : IsCompact K) (hX : Bornology.IsBounded X)
    {ι : Type*} (a : ι → E) {ε m : ℝ} (hε : 0 < ε) (hm : m < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : E → ℝ) (x : E), x ∈ X →
      ContDiffAt ℝ 2 u x → m ≤ u x → u x < 0 →
      (∀ q : E → ℝ, IsPluriharmonicQuadratic a (fun i => Complex.I • a i) q →
        quadraticL2Energy μ K q ≤ ε → ∀ v : E,
        0 ≤ realHessian (powerTransform (fun y => u y+q y)) x v v) →
      ∀ v : E, C*‖v‖^2 ≤ realHessian (powerTransform u) x v v := by
  obtain ⟨δ,hδ,hrad⟩ := exists_uniform_square_test_L2_radius μ hK hX hε
  refine ⟨2*δ*sqrtSlope m, mul_pos (mul_pos (by norm_num) hδ) (sqrtSlope_pos hm), ?_⟩
  intro u x hx hu hmx hux htest v
  have ht : ∀ ell : E →L[ℂ] ℂ, ‖ell‖ = 1 → ∀ w : E,
      0 ≤ realHessian (powerTransform (fun y =>
        u y-δ*realPartSquare (ell.restrictScalars ℝ) x y)) x w w := by
    intro ell hell w
    have hJ (i : ι) : ell.restrictScalars ℝ (Complex.I • a i) =
        Complex.I * ell.restrictScalars ℝ (a i) := by
      simp only [ContinuousLinearMap.coe_restrictScalars',map_smul,smul_eq_mul]
    have hq := IsPluriharmonicQuadratic_const_mul
      (realPartSquare_isPluriharmonicQuadratic (ell.restrictScalars ℝ) x a
        (fun i => Complex.I • a i) hJ) (-δ)
    have hE := hrad x hx (ell.restrictScalars ℝ)
      (by simpa only [ContinuousLinearMap.norm_restrictScalars] using hell)
    simpa only [sub_eq_add_neg,neg_mul] using
      htest (fun y => -δ*realPartSquare (ell.restrictScalars ℝ) x y) hq hE w
  have h := powerHessian_lower_of_holomorphic_square_tests hu hux hδ.le ht v
  apply le_trans _ h
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sqrtSlope_mono_negative hmx hux) (by positivity))
    (sq_nonneg _)

/-- A fixed quantitative constant survives an actual scalar Hessian limit.
The convergence is an explicit obligation, not an assertion of existence of
a Dirichlet deformation family. -/
theorem realHessian_uniform_lower_limit {α : Type*} {l : Filter α} [NeBot l]
    {f : α → E → ℝ} {g : E → ℝ} {x : E} {C : ℝ}
    (hbound : ∀ᶠ t in l, ∀ v : E, C*‖v‖^2 ≤ realHessian (f t) x v v)
    (hlim : ∀ v : E, Tendsto (fun t => realHessian (f t) x v v) l
      (𝓝 (realHessian g x v v))) :
    ∀ v : E, C*‖v‖^2 ≤ realHessian g x v v := by
  intro v
  exact ge_of_tendsto (hlim v) (hbound.mono fun t ht => ht v)

end PowerConvexity
