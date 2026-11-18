import PowerConvexity.Calculus.QuotientRatioQuadraticBoundTwo
import PowerConvexity.Calculus.QuotientRatioFirstGradientTwo
import PowerConvexity.Algebra.NormedGradientAbsorptionTwo

/-! # Actual ratio estimate under an elliptic contraction and diagonal matrix estimates

All derivatives are actual Frechet derivatives. The hypotheses on the two
matrix diagonal contractions remain explicit for later application to Schur.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hermitianQuotientRatioFieldTwo_elliptic_estimate
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hBvalue1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0)
    (ha0 : 0 ≤ a x) (hb0 : 0 ≤ b x) (ht : 0 < a x+b x)
    {K B0 B1 ell Λ : ℝ} (hK : 0 ≤ K) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hDA : ‖fderiv ℝ A x‖ ≤ K) (hDB : ‖fderiv ℝ B x‖ ≤ K)
    (hDC : ‖fderiv ℝ C x‖ ≤ K) (hDD : ‖fderiv ℝ D x‖ ≤ K)
    (hHA : ‖realHessian A x‖ ≤ K) (hHB : ‖realHessian B x‖ ≤ K)
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (hL : HessianPositive L)
    (hlow : ∀ v : E, ell*‖v‖^2 ≤ L (realRankOneForm v))
    (htrace : L (realInnerForm (E := E)) ≤ Λ)
    (hLa : L (realHessian a x) ≤ B0*(a x+b x)+
      B1*(‖fderiv ℝ a x‖+‖fderiv ℝ b x‖+‖fderiv ℝ c x‖+‖fderiv ℝ d x‖))
    (hLb : L (realHessian b x) ≤ B0*(a x+b x)+
      B1*(‖fderiv ℝ a x‖+‖fderiv ℝ b x‖+‖fderiv ℝ c x‖+‖fderiv ℝ d x‖)) :
    let Czero := 4*B0+Λ*(2*K+22*K^2)
    let Cgrad := 4*B1+8*Λ*K
    L (realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x) ≤
      (Czero+4*K*Cgrad+5*Cgrad^2/ell)*(a x+b x)+
      2*Cgrad*‖fderiv ℝ (hermitianQuotientRatioFieldTwo a b c d A B C D) x‖ := by
  let t := a x+b x
  let α := 1+(b x)^2/t^2
  let β := 1+(a x)^2/t^2
  let R : E →L[ℝ] ℝ := t⁻¹ • (b x • fderiv ℝ a x-a x • fderiv ℝ b x)
  let S := ‖fderiv ℝ a x‖+‖fderiv ℝ b x‖+‖fderiv ℝ c x‖+‖fderiv ℝ d x‖
  let H0 := α • realHessian a x+β • realHessian b x
  let C0 := (2*K+22*K^2)*t+8*K*S
  let Czero := 4*B0+Λ*(2*K+22*K^2)
  let Cgrad := 4*B1+8*Λ*K
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hCost0 : 0 ≤ C0 := by dsimp only [C0,t]; positivity
  have hCg : 0 ≤ Cgrad := by dsimp only [Cgrad]; positivity
  have hdiag : 0 ≤ B0*t+B1*S := by dsimp only [t]; positivity
  obtain ⟨hα,hβ⟩ := traceDetRatioTwo_first_coeff_bounds ha0 hb0 ht
  change 1 ≤ α ∧ α ≤ 2 at hα
  change 1 ≤ β ∧ β ≤ 2 at hβ
  have hα0 : 0 ≤ α := by linarith [hα.1]
  have hβ0 : 0 ≤ β := by linarith [hβ.1]
  have hquad := hermitianQuotientRatioFieldTwo_quadratic_bound ha hb hc hd hA hB hC hD
    hc0 hd0 hA1 hBvalue1 hC0 hD0 ha0 hb0 ht hK hDA hDB hDC hDD hHA hHB
  have hTop := hessian_contraction_of_three_square_bound_elliptic L hL hCost0
    (show 0 ≤ 1/t by dsimp only [t]; positivity) hlow htrace
    (realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x) H0
    R (fderiv ℝ c x) (fderiv ℝ d x) (by
      intro v
      simpa only [H0,α,β,C0,t,R,S,add_apply,smul_apply,smul_eq_mul] using hquad v)
  have hLA : α*L (realHessian a x) ≤ 2*(B0*t+B1*S) := by
    have hh1 := mul_le_mul_of_nonneg_left hLa hα0
    have hh2 := mul_le_mul_of_nonneg_right hα.2 hdiag
    nlinarith only [hh1,hh2]
  have hLB : β*L (realHessian b x) ≤ 2*(B0*t+B1*S) := by
    have hh1 := mul_le_mul_of_nonneg_left hLb hβ0
    have hh2 := mul_le_mul_of_nonneg_right hβ.2 hdiag
    nlinarith only [hh1,hh2]
  have hLF : L (realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x) ≤
      Czero*t+Cgrad*S-ell/t*(‖R‖^2+‖fderiv ℝ c x‖^2+‖fderiv ℝ d x‖^2) := by
    simp only [H0,map_add L,map_smul L,smul_eq_mul] at hTop
    dsimp only [Czero,Cgrad,C0]
    simp only [div_eq_mul_inv] at hTop ⊢
    nlinarith only [hTop,hLA,hLB]
  have hgrad := weighted_diagonal_norm_bound_metric ha0 hb0 ht hα.1 hα.2 hβ.1 hβ.2 hK
    (fderiv ℝ a x) (fderiv ℝ b x) (fderiv ℝ A x) (fderiv ℝ B x) hDA hDB
  have hDF := hermitianQuotientRatioFieldTwo_fderiv_normalized_map ha hb hc hd hA hB hC hD
    hc0 hd0 hA1 hBvalue1 hC0 hD0 ht.ne'
  change fderiv ℝ (hermitianQuotientRatioFieldTwo a b c d A B C D) x =
    α • (fderiv ℝ a x-a x • fderiv ℝ A x)+β • (fderiv ℝ b x-b x • fderiv ℝ B x) at hDF
  rw [← hDF] at hgrad
  have hfinal := norm_gradient_negative_square_absorption ht hell hCg
    (norm_nonneg R) (norm_nonneg (fderiv ℝ c x)) (norm_nonneg (fderiv ℝ d x))
    hgrad hLF
  dsimp only
  convert hfinal using 1 <;> dsimp only [Czero,Cgrad,t] <;> ring

end PowerConvexity
