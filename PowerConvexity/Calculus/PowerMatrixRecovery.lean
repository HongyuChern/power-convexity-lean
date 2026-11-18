import PowerConvexity.Calculus.PowerMixedPositive
import PowerConvexity.Algebra.PowerRankOneEquationTwo

/-! # Recovering actual original jets from the square-root jets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexGradient_powerTransform {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hx : u x < 0) (a b : ι → E) :
    complexGradient a b (powerTransform u) x = (sqrtSlope (u x):ℂ) • complexGradient a b u x := by
  have hv : DifferentiableAt ℝ (powerTransform u) x :=
    ((hasDerivAt_negativeSqrt hx).comp_hasFDerivAt x hu.hasFDerivAt).differentiableAt
  funext i
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [complexGradient_real_entry hv,complexGradient_real_entry hu,fderiv_powerTransform hu hx]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,Pi.smul_apply]
  ring

theorem complexHessian_recover_from_power {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E) :
    complexHessian a b u x = (2:ℂ) •
      ((Real.sqrt (-u x):ℂ) • complexHessian a b (powerTransform u) x-
        Matrix.vecMulVec (complexGradient a b (powerTransform u) x)
          (star (complexGradient a b (powerTransform u) x))) := by
  have hs : Real.sqrt (-u x) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hx)).ne'
  have hsc : (Real.sqrt (-u x):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsquare : ((Real.sqrt (-u x):ℂ))^2 = ((-u x:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (neg_pos.mpr hx).le
  have hgrad := complexGradient_powerTransform (hu.differentiableAt (by norm_num)) hx a b
  ext i j
  simp only [Matrix.smul_apply,Matrix.sub_apply,Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul]
  rw [complexHessian_powerTransform hu hx a b i j,hgrad]
  simp only [Pi.smul_apply,smul_eq_mul,star_mul,Complex.star_def,Complex.conj_ofReal]
  simp only [sqrtSlope,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_one,
    Complex.ofReal_ofNat,← hsquare]
  field_simp [hsc]
  ring

theorem actualPower_inverse_equation_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef)
    (hdet : (complexHessian a b u x).det = 1) :
    powerInverseValueTwo (complexGradient a b (powerTransform u) x)
      (complexHessian a b (powerTransform u) x)⁻¹ = -powerTransform u x := by
  have hH : (complexHessian a b (powerTransform u) x).PosDef :=
    (power_mixed_posDef_iff_modifiedA hu hx a b).mpr (modifiedA_posDef a b hx hA)
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det)
    (complexHessian_recover_from_power hu hx a b)
  rw [hdet,Matrix.det_smul] at he
  norm_num at he
  have hd : ((Real.sqrt (-u x):ℂ) • complexHessian a b (powerTransform u) x-
      Matrix.vecMulVec (complexGradient a b (powerTransform u) x)
        (star (complexGradient a b (powerTransform u) x))).det = (1/4:ℂ) := by
    linear_combination -he/4
  simpa only [powerTransform,negativeSqrt,neg_neg] using
    powerInverseValueTwo_eq_of_rankOne_det hH _ (Real.sqrt_pos.mpr (neg_pos.mpr hx)) hd

end PowerConvexity
