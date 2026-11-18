import PowerConvexity.Calculus.QuadraticEnergyPaths

/-! # Exact L2-energy radii under real scaling

The paper's radius is the integral of q squared, so scaling q by t changes
that radius by t squared, not by t.
-/
set_option autoImplicit false
open Set MeasureTheory
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem quadraticL2Energy_scaled_le (μ : Measure E) (K : Set E) (q : E → ℝ)
    {ε t : ℝ} (hE : quadraticL2Energy μ K q ≤ ε) (ht : t ∈ Icc (0:ℝ) 1) :
    quadraticL2Energy μ K (fun y => t*q y) ≤ ε := by
  rw [quadraticL2Energy_const_mul]
  have hε : 0 ≤ ε := (quadraticL2Energy_nonneg μ K q).trans hE
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
  exact (mul_le_mul_of_nonneg_left hE (sq_nonneg t)).trans
    (by nlinarith [mul_le_mul_of_nonneg_right ht2 hε])

theorem quadraticL2Energy_scaled_radius_le (μ : Measure E) (K : Set E) (q : E → ℝ)
    {ε t : ℝ} (hE : quadraticL2Energy μ K q ≤ ε) :
    quadraticL2Energy μ K (fun y => t*q y) ≤ t^2*ε := by
  rw [quadraticL2Energy_const_mul]
  exact mul_le_mul_of_nonneg_left hE (sq_nonneg t)

theorem exists_unscaled_pluriharmonic_quadratic {ι : Type*}
    (μ : Measure E) (K : Set E) (a b : ι → E)
    {q : E → ℝ} (hq : IsPluriharmonicQuadratic a b q) {ε t : ℝ} (ht : t ≠ 0)
    (hE : quadraticL2Energy μ K q ≤ t^2*ε) :
    ∃ r : E → ℝ, IsPluriharmonicQuadratic a b r ∧ quadraticL2Energy μ K r ≤ ε ∧
      (fun y => t*r y) = q := by
  refine ⟨fun y => t⁻¹*q y,IsPluriharmonicQuadratic_const_mul hq t⁻¹,?_,?_⟩
  · rw [quadraticL2Energy_const_mul]
    have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg t⁻¹)
    have he : t⁻¹^2*(t^2*ε) = ε := by field_simp
    rwa [he] at hh
  · funext y
    rw [← mul_assoc,mul_inv_cancel₀ ht,one_mul]

end PowerConvexity
