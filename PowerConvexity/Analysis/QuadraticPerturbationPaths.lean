import PowerConvexity.Analysis.ParameterMinimum
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Exact norm identities for Appendix A's perturbation paths -/
set_option autoImplicit false
open Metric Set
open scoped Topology
namespace PowerConvexity
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem linear_perturbation_norm_sq (q h : P) (t : ℝ) :
    ‖q + t • h‖^2 = ‖q‖^2 + 2*t*inner ℝ q h + t^2*‖h‖^2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

noncomputable def curvedPerturbationPath (q h : P) (γ t : ℝ) : P :=
  (1-γ*t^2) • q + t • h

theorem curved_perturbation_norm_sq (q h : P) (γ t : ℝ) :
    ‖curvedPerturbationPath q h γ t‖^2 =
      (1-γ*t^2)^2*‖q‖^2 + 2*t*(1-γ*t^2)*inner ℝ q h + t^2*‖h‖^2 := by
  simp only [curvedPerturbationPath, norm_add_sq_real, real_inner_smul_left,
    real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- In the orthogonal case the expansion is exactly quartic, with no
unquantified O(t^3) remainder. -/
theorem curved_perturbation_norm_difference (q h : P) (γ t : ℝ)
    (horth : inner ℝ q h = 0) :
    ‖curvedPerturbationPath q h γ t‖^2 - ‖q‖^2 =
      t^2 * (‖h‖^2 - 2*γ*‖q‖^2 + γ^2*t^2*‖q‖^2) := by
  rw [curved_perturbation_norm_sq, horth]
  ring

theorem exists_curved_perturbation_norm_decrease (q h : P) (hq : q ≠ 0)
    (horth : inner ℝ q h = 0) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧
      ∀ t : ℝ, |t| < δ → t ≠ 0 →
        ‖curvedPerturbationPath q h γ t‖^2 < ‖q‖^2 := by
  have hqn : 0 < ‖q‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  let γ := (‖h‖^2+1) / ‖q‖^2
  have hγ : 0 < γ := div_pos (by positivity) hqn
  have hγq : γ * ‖q‖^2 = ‖h‖^2+1 := by
    dsimp [γ]
    exact div_mul_cancel₀ _ hqn.ne'
  let A : ℝ → ℝ := fun t => ‖h‖^2 - 2*γ*‖q‖^2 + γ^2*t^2*‖q‖^2
  have hA0 : A 0 < 0 := by dsimp [A]; nlinarith [sq_nonneg ‖h‖, hγq]
  have hAc : ContinuousAt A 0 := by dsimp [A]; fun_prop
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), A t < 0 := hAc.eventually (gt_mem_nhds hA0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨γ, δ, hγ, hδ, ?_⟩
  intro t ht ht0
  have hAt : A t < 0 := hball (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht)
  have hprod : t^2 * A t < 0 := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht0) hAt
  rw [← curved_perturbation_norm_difference q h γ t horth] at hprod
  linarith

end PowerConvexity
