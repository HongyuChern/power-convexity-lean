import PowerConvexity.Calculus.ScalarDirichlet

/-! # The actual transformed Poisson equation in the complex line

This module prepares an independent two-point proof of the initial convexity
input in Appendix C. It does not replace the frozen appendix's a priori proof.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus

noncomputable def scalarRealTrace (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  realHessian f x 1 1+realHessian f x Complex.I Complex.I

noncomputable def scalarGradientSquare (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  (fderiv ℝ f x 1)^2+(fderiv ℝ f x Complex.I)^2

theorem scalarGradientSquare_nonneg (f : ℂ → ℝ) (x : ℂ) : 0 ≤ scalarGradientSquare f x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem scalarRealTrace_of_density {u : ℂ → ℝ} {x : ℂ} {ρ : ℝ}
    (hu : ContDiffAt ℝ 2 u x)
    (hρ : complexHessian (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    scalarRealTrace u x = 4*ρ := by
  have he := scalarContraction_eq_mixed_re hu
  rw [hρ,Complex.ofReal_re] at he
  change (realHessian u x 1 1+realHessian u x Complex.I Complex.I)/4 = ρ at he
  unfold scalarRealTrace
  linarith

theorem scalarPower_equation {u : ℂ → ℝ} {x : ℂ} {ρ : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (hρ : complexHessian (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    (-powerTransform u x)*scalarRealTrace (powerTransform u) x =
      2*ρ+scalarGradientSquare (powerTransform u) x := by
  have ht := scalarRealTrace_of_density hu hρ
  have hs : Real.sqrt (-u x) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hx)).ne'
  have hux : u x ≠ 0 := hx.ne
  have hsq : Real.sqrt (-u x)^2 = -u x := Real.sq_sqrt (by linarith)
  simp only [scalarRealTrace,scalarGradientSquare,realHessian_powerTransform hu hx,
    fderiv_powerTransform (hu.differentiableAt (by norm_num)) hx,
    ContinuousLinearMap.smul_apply,smul_eq_mul,powerTransform,negativeSqrt,neg_neg,sqrtSlope]
  unfold scalarRealTrace at ht
  field_simp [hs,hux]
  rw [hsq]
  linear_combination -2*(u x)^2 * ht

end PowerConvexity
