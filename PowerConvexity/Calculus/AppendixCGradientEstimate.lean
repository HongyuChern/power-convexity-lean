import PowerConvexity.Calculus.AppendixCSigmaEquation
import PowerConvexity.Algebra.ScalarGradientBound

/-! # The Appendix C gradient estimate with an explicit coefficient -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem powerWeight_pos {t : ℝ} (ht : t < 0) : 0 < powerWeight t :=
  one_div_pos.mpr (mul_pos (by norm_num) (neg_pos.mpr ht))

theorem scalarAlpha_re_eq (a b : E) (u : E → ℝ) (x : E) :
    (scalarAlpha a b u x).re =
      (complexHessian (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0).re +
      powerWeight (u x) * Complex.normSq (dz a b (fun y => (u y : ℂ)) x) := by
  rw [scalarAlpha, modifiedA_eq_weight]
  simp only [complexGradient, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

theorem scalarAlpha_re_pos_of_density {u : E → ℝ} {x : E} {ρ : ℝ}
    (hx : u x < 0) (a b : E) (hρpos : 0 < ρ)
    (hρ : complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u x 0 0 = (ρ : ℂ)) :
    0 < (scalarAlpha a b u x).re := by
  rw [scalarAlpha_re_eq, hρ, Complex.ofReal_re]
  exact add_pos_of_pos_of_nonneg hρpos
    (mul_nonneg (powerWeight_pos hx).le (Complex.normSq_nonneg _))

/-- This is a genuine estimate of actual derivatives.  The coefficient is
finite on any neighborhood on which `1-sigma` is bounded below positively. -/
theorem scalarSigma_gradient_estimate {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hαpos : 0 < (scalarAlpha a b u x).re)
    (hσ : 0 ≤ scalarSigma a b u x) (hσ1 : scalarSigma a b u x < 1) :
    (dz a (-b) (dz a b (fun y => (scalarSigma a b u y : ℂ))) x).re ≤
      (4 * powerWeight (u x) * ‖dz a b (fun y => (u y : ℂ)) x‖ *
        ‖scalarRatio a b u x‖ / (1 - scalarSigma a b u x)) *
      ‖dz a b (fun y => (scalarSigma a b u y : ℂ)) x‖ := by
  have hα : scalarAlpha a b u x ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hαpos
    exact (lt_irrefl 0) hαpos
  have hR : Complex.normSq (scalarRatio a b u x) = 1 - scalarSigma a b u x := by
    rw [scalarSigma_eq_ratio (hu.of_le (by norm_num)) a b]
    ring
  have hRp : 0 < Complex.normSq (scalarRatio a b u x) := by rw [hR]; linarith
  have h := scalar_gradient_bound (powerWeight_pos hx).le hαpos.le hσ hRp
    (scalarSigma_equation_real hu hx a b hρ hα)
  rwa [hR] at h

theorem scalarSigma_gradient_estimate_constDensity {u : E → ℝ} {x : E} {ρ : ℝ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E) (hρpos : 0 < ρ)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => (ρ : ℂ))
    (hσ : 0 ≤ scalarSigma a b u x) (hσ1 : scalarSigma a b u x < 1) :
    (dz a (-b) (dz a b (fun y => (scalarSigma a b u y : ℂ))) x).re ≤
      (4 * powerWeight (u x) * ‖dz a b (fun y => (u y : ℂ)) x‖ *
        ‖scalarRatio a b u x‖ / (1 - scalarSigma a b u x)) *
      ‖dz a b (fun y => (scalarSigma a b u y : ℂ)) x‖ :=
  scalarSigma_gradient_estimate hu hx a b hρ
    (scalarAlpha_re_pos_of_density hx a b hρpos hρ.self_of_nhds) hσ hσ1

end PowerConvexity
