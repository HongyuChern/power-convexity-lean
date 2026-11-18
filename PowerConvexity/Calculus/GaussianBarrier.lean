import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Actual first and second derivatives of the classical annular barrier -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialGaussian (k : ℝ) (c x : E) : ℝ := Real.exp (-k * ‖x - c‖^2)

noncomputable def annularBarrier (k R : ℝ) (c x : E) : ℝ :=
  radialGaussian k c x - Real.exp (-k * R^2)

noncomputable def realInnerForm : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

noncomputable def realRankOneForm (v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ v).smulRight (innerSL ℝ v)

theorem radialGaussian_contDiff (k : ℝ) (c : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (radialGaussian k c) :=
  (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))).exp

theorem annularBarrier_contDiff (k R : ℝ) (c : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (annularBarrier k R c) :=
  (radialGaussian_contDiff k c).sub contDiff_const

theorem hasFDerivAt_radialGaussian (k : ℝ) (c x : E) :
    HasFDerivAt (radialGaussian k c)
      ((-2 * k * radialGaussian k c x) • innerSL ℝ (x-c)) x := by
  have h := (((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-k)).exp
  convert h using 1
  · rfl
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, radialGaussian, id_eq]
    ring

theorem fderiv_radialGaussian (k : ℝ) (c x : E) :
    fderiv ℝ (radialGaussian k c) x =
      (-2 * k * radialGaussian k c x) • innerSL ℝ (x-c) :=
  (hasFDerivAt_radialGaussian k c x).fderiv

theorem fderiv_annularBarrier (k R : ℝ) (c x : E) :
    fderiv ℝ (annularBarrier k R c) x =
      (-2 * k * radialGaussian k c x) • innerSL ℝ (x-c) :=
  ((hasFDerivAt_radialGaussian k c x).sub_const (Real.exp (-k * R^2))).fderiv

theorem realHessian_radialGaussian (k : ℝ) (c x : E) :
    realHessian (radialGaussian k c) x =
      (4 * k^2 * radialGaussian k c x) • realRankOneForm (x-c) -
      (2 * k * radialGaussian k c x) • (realInnerForm (E := E)) := by
  have he : fderiv ℝ (radialGaussian k c) =
      fun y => (-2 * k * radialGaussian k c y) • innerSL ℝ (y-c) :=
    funext fun y => fderiv_radialGaussian k c y
  have hlin : HasFDerivAt (fun y : E => innerSL ℝ (y-c)) (innerSL ℝ (E := E)) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (innerSL ℝ (E := E)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
  have h := (((hasFDerivAt_radialGaussian k c x).const_mul (-2*k)).smul hlin).fderiv
  change fderiv ℝ (fun y => (-2*k*radialGaussian k c y) • innerSL ℝ (y-c)) x = _ at h
  unfold realHessian
  rw [he, h]
  ext v w
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    realRankOneForm, realInnerForm, smul_eq_mul]
  ring

theorem realHessian_annularBarrier (k R : ℝ) (c x : E) :
    realHessian (annularBarrier k R c) x =
      (4 * k^2 * radialGaussian k c x) • realRankOneForm (x-c) -
      (2 * k * radialGaussian k c x) • (realInnerForm (E := E)) := by
  have he : fderiv ℝ (annularBarrier k R c) = fderiv ℝ (radialGaussian k c) := by
    funext y
    rw [fderiv_annularBarrier, fderiv_radialGaussian]
  change fderiv ℝ (fderiv ℝ (annularBarrier k R c)) x = _
  rw [he]
  exact realHessian_radialGaussian k c x

theorem norm_fderiv_annularBarrier {k : ℝ} (hk : 0 ≤ k) (R : ℝ) (c x : E) :
    ‖fderiv ℝ (annularBarrier k R c) x‖ =
      2 * k * radialGaussian k c x * ‖x-c‖ := by
  rw [fderiv_annularBarrier, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  have hp : 0 < radialGaussian k c x := Real.exp_pos _
  rw [abs_of_nonpos (by nlinarith : -2 * k * radialGaussian k c x ≤ 0)]
  ring

theorem annularBarrier_zero_on_sphere (k R : ℝ) (c x : E) (hx : ‖x-c‖ = R) :
    annularBarrier k R c x = 0 := by simp [annularBarrier, radialGaussian, hx]

theorem annularBarrier_le_gaussian (k R : ℝ) (c x : E) :
    annularBarrier k R c x ≤ radialGaussian k c x := by
  unfold annularBarrier
  linarith [Real.exp_pos (-k * R^2)]

end PowerConvexity
