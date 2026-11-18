import PowerConvexity.Calculus.HermitianQuotientRatioHessianTwo
import PowerConvexity.Algebra.TraceRatioGradientAbsorption

/-! # Actual first quotient derivative and the gradient used for absorption -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hermitianQuotientRatioFieldTwo_fderiv_normalized
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0) (ht : a x+b x ≠ 0) (v : E) :
    fderiv ℝ (hermitianQuotientRatioFieldTwo a b c d A B C D) x v =
      (1+(b x)^2/(a x+b x)^2)*(fderiv ℝ a x v-a x*fderiv ℝ A x v)+
      (1+(a x)^2/(a x+b x)^2)*(fderiv ℝ b x v-b x*fderiv ℝ B x v) := by
  let T := hermitianAdjTraceFieldTwo a b c d A B C D
  let Delta := hermitianDetFieldTwo A B C D
  let N := hermitianDetFieldTwo a b c d
  have hT := hermitianAdjTraceFieldTwo_contDiffAt ha hb hc hd hA hB hC hD
  have hDelta := hermitianDetFieldTwo_contDiffAt hA hB hC hD
  have hN := hermitianDetFieldTwo_contDiffAt ha hb hc hd
  change ContDiffAt ℝ 2 T x at hT
  change ContDiffAt ℝ 2 Delta x at hDelta
  change ContDiffAt ℝ 2 N x at hN
  have hTx : T x = a x+b x := by simp [T,hermitianAdjTraceFieldTwo,hA1,hB1,hC0,hD0]
  have hDx : Delta x = 1 := by simp [Delta,hermitianDetFieldTwo,hA1,hB1,hC0,hD0]
  have hNx : N x = a x*b x := by simp [N,hermitianDetFieldTwo,hc0,hd0]
  have hT0 : T x ≠ 0 := by rwa [hTx]
  have hDelta0 : Delta x ≠ 0 := by rw [hDx]; norm_num
  have hDT := hermitianAdjTraceFieldTwo_fderiv_normalized ha hb hc hd hA hB hC hD
    hc0 hd0 hA1 hB1 hC0 hD0 v
  have hDD := hermitianDetFieldTwo_fderiv_diagonal hA hB hC hD hC0 hD0 v
  have hDN := hermitianDetFieldTwo_fderiv_diagonal ha hb hc hd hc0 hd0 v
  simp only [hA1,hB1,one_mul] at hDD
  have htd := hT.differentiableAt (by norm_num)
  have hdd := hDelta.differentiableAt (by norm_num)
  have hnd := hN.differentiableAt (by norm_num)
  change fderiv ℝ (fun y => T y/Delta y+N y/T y) x v = _
  rw [fderiv_fun_add ((hT.fun_div hDelta hDelta0).differentiableAt (by norm_num))
    ((hN.fun_div hT hT0).differentiableAt (by norm_num)),add_apply,
    fderiv_real_div_at htd hdd hDelta0,fderiv_real_div_at hnd htd hT0]
  change fderiv ℝ T x v = _ at hDT
  change fderiv ℝ Delta x v = _ at hDD
  change fderiv ℝ N x v = _ at hDN
  rw [hTx,hDx,hNx,hDT,hDD,hDN]
  have hid := quotient_ratio_normalized_first_jet_two (a x) (b x)
    (fderiv ℝ a x v) (fderiv ℝ b x v) (fderiv ℝ A x v) (fderiv ℝ B x v) ht
  dsimp only at hid
  simp only [one_pow,div_one]
  linear_combination hid

theorem hermitianQuotientRatioFieldTwo_fderiv_normalized_map
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0) (ht : a x+b x ≠ 0) :
    fderiv ℝ (hermitianQuotientRatioFieldTwo a b c d A B C D) x =
      (1+(b x)^2/(a x+b x)^2) • (fderiv ℝ a x-a x • fderiv ℝ A x)+
      (1+(a x)^2/(a x+b x)^2) • (fderiv ℝ b x-b x • fderiv ℝ B x) := by
  ext v
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul]
  exact hermitianQuotientRatioFieldTwo_fderiv_normalized ha hb hc hd hA hB hC hD
    hc0 hd0 hA1 hB1 hC0 hD0 ht v

theorem normalized_quotient_diagonal_gradient_bound
    {a b α β p q x y G K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < a+b)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2)
    (hK : 0 ≤ K) (hx : |x| ≤ K) (hy : |y| ≤ K)
    (hG : G = α*(p-a*x)+β*(q-b*y)) :
    |p|+|q| ≤ 2*|G|+4*K*(a+b)+4*|(b*p-a*q)/(a+b)| := by
  have hα0 : 0 ≤ α := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have herr : |α*a*x+β*b*y| ≤ 2*K*(a+b) := by
    calc
      _ ≤ |α*a*x|+|β*b*y| := abs_add_le _ _
      _ = α*a*|x|+β*b*|y| := by
        simp only [abs_mul,abs_of_nonneg hα0,abs_of_nonneg hβ0,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ 2*a*K+2*b*K := by gcongr
      _ = _ := by ring
  have hgrad : |α*p+β*q| ≤ |G|+2*K*(a+b) := by
    have hid : α*p+β*q = G+(α*a*x+β*b*y) := by linear_combination -hG
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add_right herr _)
  have hh := weighted_diagonal_gradient_bound ha hb ht hα1 hα2 hβ1 hβ2 p q
  linarith

end PowerConvexity
