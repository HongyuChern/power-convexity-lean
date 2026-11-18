import PowerConvexity.Calculus.AppendixCGradientEstimate

/-! # A bounded gradient coefficient near a zero contact in Appendix C -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scalarGradientCoefficient (a b : E) (u : E → ℝ) (x : E) : ℝ :=
  4 * powerWeight (u x) * ‖dz a b (fun y => (u y : ℂ)) x‖ *
    ‖scalarRatio a b u x‖ / (1 - scalarSigma a b u x)

theorem scalarGradientCoefficient_continuousAt {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) (hσ : scalarSigma a b u x ≠ 1) :
    ContinuousAt (scalarGradientCoefficient a b u) x := by
  have hG := (complexGradient_contDiffAt_two (hu.of_le (by norm_num))
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0).continuousAt.norm
  have hQ := (scalarRatio_contDiffAt_two hu hx a b hα).continuousAt.norm
  have hS := (scalarSigma_contDiffAt_two hu hx a b hα).continuousAt
  exact (((continuousAt_const.mul (powerWeight_contDiffAt hu hx).continuousAt).mul hG).mul hQ).div
    (continuousAt_const.sub hS) (sub_ne_zero.mpr hσ.symm)

/-- Near a zero of sigma, its differential inequality has one finite positive
constant. Nonnegativity is the hypothesis at the evaluated point; the strong
minimum principle still has to use a neighborhood where it holds. -/
theorem scalarSigma_local_gradient_estimate {u : E → ℝ} {x : E} {ρ : ℝ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E) (hρpos : 0 < ρ)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => (ρ : ℂ))
    (hσ0 : scalarSigma a b u x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, 0 ≤ scalarSigma a b u y →
      (dz a (-b) (dz a b (fun z => (scalarSigma a b u z : ℂ))) y).re ≤
        C * ‖dz a b (fun z => (scalarSigma a b u z : ℂ)) y‖ := by
  have hαpos := scalarAlpha_re_pos_of_density hx a b hρpos hρ.self_of_nhds
  have hα : scalarAlpha a b u x ≠ 0 := by
    intro he
    rw [he, Complex.zero_re] at hαpos
    exact (lt_irrefl 0) hαpos
  have hS := (scalarSigma_contDiffAt_two hu hx a b hα).continuousAt
  have hK := scalarGradientCoefficient_continuousAt hu hx a b hα (by rw [hσ0]; norm_num)
  have hKn : 0 ≤ scalarGradientCoefficient a b u x := by
    unfold scalarGradientCoefficient
    rw [hσ0]
    have hh := (powerWeight_pos hx).le
    positivity
  refine ⟨scalarGradientCoefficient a b u x + 1, by linarith, ?_⟩
  have hKb := hK.eventually_lt_const (lt_add_one (scalarGradientCoefficient a b u x))
  have hS1 := hS.eventually_lt_const (show scalarSigma a b u x < 1 by rw [hσ0]; norm_num)
  have hnneg := hu.continuousAt.eventually_lt_const hx
  filter_upwards [hu.eventually (by simp), hnneg, hρ.eventuallyEq_nhds, hKb, hS1]
    with y hy hyneg hyρ hyK hyS1
  intro hyS
  have he := scalarSigma_gradient_estimate_constDensity hy hyneg a b hρpos hyρ hyS hyS1
  exact he.trans (mul_le_mul_of_nonneg_right hyK.le (norm_nonneg _))

end PowerConvexity
