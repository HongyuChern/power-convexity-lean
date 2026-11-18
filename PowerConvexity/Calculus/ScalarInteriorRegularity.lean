import PowerConvexity.Calculus.WirtingerRealOperator
import Mathlib.Analysis.Complex.Harmonic.Analytic

/-! # Interior regularity of a classical constant-density scalar solution -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology Laplacian

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem realHessian_norm_sq (x : E) :
    realHessian (fun y : E => ‖y‖^2) x = (2 : ℝ) • (realInnerForm (E := E)) := by
  unfold realHessian
  rw [fderiv_norm_sq]
  change fderiv ℝ ((2 : ℕ) • (realInnerForm (E := E) : E → E →L[ℝ] ℝ)) x = _
  rw [← ofNat_smul_eq_nsmul ℝ 2]
  rw [fderiv_const_smul (realInnerForm (E := E)).differentiableAt,
    ContinuousLinearMap.fderiv]

theorem laplacian_eq_four_scalarContraction (f : ℂ → ℝ) (x : ℂ) :
    Δ f x = 4 * scalarHessianContraction (realHessian f x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, scalarHessianContraction,
    LinearMap.coe_mk, AddHom.coe_mk, realHessian]
  ring

theorem scalarContraction_eq_mixed_re {f : ℂ → ℝ} {x : ℂ}
    (hf : ContDiffAt ℝ 2 f x) :
    scalarHessianContraction (realHessian f x) =
      (complexHessian (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => Complex.I) f x 0 0).re := by
  rw [complexHessian_real_entry hf]
  simp only [scalarHessianContraction, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- No C4 assumption is needed for this bootstrap. A C2 classical solution
with constant mixed Hessian is a quadratic plus a real-analytic harmonic part. -/
theorem scalar_constDensity_contDiffAt {u : ℂ → ℝ} {x : ℂ} {ρ : ℝ}
    (hu : ContDiffAt ℝ 2 u x)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u y 0 0) =ᶠ[𝓝 x] fun _ => (ρ : ℂ))
    (n : WithTop ℕ∞) : ContDiffAt ℝ n u x := by
  let q : ℂ → ℝ := fun y => ρ * ‖y‖^2
  let f : ℂ → ℝ := fun y => u y - q y
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_norm_sq (𝕜 := ℝ))
  have hf : ContDiffAt ℝ 2 f x := hu.sub hq.contDiffAt
  have hharm : InnerProductSpace.HarmonicAt f x := by
    refine ⟨hf, ?_⟩
    filter_upwards [hu.eventually (by simp), hρ] with y hy hyr
    change Δ f y = 0
    rw [laplacian_eq_four_scalarContraction, realHessian_sub_at hy hq.contDiffAt]
    have hQ : realHessian q y = (2 * ρ) • (realInnerForm (E := ℂ)) := by
      rw [realHessian_const_mul_at (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt,
        realHessian_norm_sq, smul_smul]
      congr 1
      ring
    rw [map_sub scalarHessianContraction _ _, scalarContraction_eq_mixed_re hy, hyr,
      Complex.ofReal_re, hQ, map_smul, smul_eq_mul, scalarHessianContraction_trace]
    ring
  have hfa : ContDiffAt ℝ n f x := (HarmonicAt.analyticAt hharm).contDiffAt
  have hqa : ContDiffAt ℝ n q x :=
    contDiffAt_const.mul (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt
  convert hfa.add hqa using 1
  funext y
  dsimp only [f, q]
  ring

end PowerConvexity
