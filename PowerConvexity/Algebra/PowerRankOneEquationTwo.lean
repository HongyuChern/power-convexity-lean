import PowerConvexity.Algebra.PowerInverseConcavityTwo

/-! # The inverse-Hessian root of the transformed determinant equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped ComplexOrder
namespace PowerConvexity

theorem det_scalar_one_sub_vecMulVec_two (r : ℂ) (p q : Fin 2 → ℂ) :
    (r • (1 : Matrix (Fin 2) (Fin 2) ℂ)-vecMulVec p q).det = r^2-r*(q ⬝ᵥ p) := by
  simp only [det_fin_two,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,
    Matrix.one_apply_eq,Matrix.one_apply_ne (by decide : (0:Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1:Fin 2) ≠ 0),mul_one,mul_zero,zero_sub,
    dotProduct,Fin.sum_univ_two]
  ring

theorem inverse_determinant_rankOne_equation_two
    {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) (p : Fin 2 → ℂ) (r : ℂ) :
    H⁻¹.det*(r • H-vecMulVec p (star p)).det = r^2-r*covectorValueTwo p H⁻¹ := by
  rw [← Matrix.det_mul,Matrix.mul_sub,Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit),Matrix.mul_vecMulVec]
  exact det_scalar_one_sub_vecMulVec_two r (H⁻¹.mulVec p) (star p)

theorem powerInverseValueTwo_eq_of_rankOne_det
    {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) (p : Fin 2 → ℂ)
    {r : ℝ} (hr : 0 < r)
    (hdet : ((r:ℂ) • H-vecMulVec p (star p)).det = (1/4:ℂ)) :
    powerInverseValueTwo p H⁻¹ = r := by
  let t := (covectorValueTwo p H⁻¹).re
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp (covectorValueTwo_nonneg p hH.inv.posSemidef)).1
  have hd : 0 < H⁻¹.det.re := (Complex.pos_iff.mp hH.inv.det_pos).1
  have he := congrArg Complex.re (inverse_determinant_rankOne_equation_two hH p (r:ℂ))
  rw [hdet,show (1/4:ℂ) = ((1/4:ℝ):ℂ) by norm_num] at he
  norm_num only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,pow_two,
    mul_zero,zero_mul,sub_zero] at he
  change H⁻¹.det.re*(1/4) = r*r-r*t at he
  have htr : t < r := by
    by_contra hn
    have hh := mul_nonneg hr.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  have heq : (2*r-t)^2 = t^2+H⁻¹.det.re := by nlinarith
  rw [powerInverseValueTwo_eq_radical p hH.inv.posSemidef]
  change (t+Real.sqrt (t^2+H⁻¹.det.re))/2 = r
  rw [← heq,Real.sqrt_sq (by linarith : 0 ≤ 2*r-t)]
  ring

end PowerConvexity
