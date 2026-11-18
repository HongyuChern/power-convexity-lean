import PowerConvexity.Calculus.HermitianScalarJetsTwo
import PowerConvexity.Algebra.QuotientRatioSecondJetTwo

/-! # Actual normalized Hessian of the variable Hermitian quotient ratio

The scalar is tr(M adj A)/det A + det M/tr(M adj A).
The actual matrix identification is a separate algebraic bridge.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def hermitianQuotientRatioFieldTwo (a b c d A B C D : E → ℝ) (x : E) : ℝ :=
  hermitianAdjTraceFieldTwo a b c d A B C D x/hermitianDetFieldTwo A B C D x+
    hermitianDetFieldTwo a b c d x/hermitianAdjTraceFieldTwo a b c d A B C D x

theorem hermitianQuotientRatioFieldTwo_realHessian_normalized
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0) (ht : a x+b x ≠ 0) (v : E) :
    realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x v v =
      (1+(b x)^2/(a x+b x)^2)*(realHessian a x v v-
        2*fderiv ℝ a x v*fderiv ℝ A x v-
        2*(fderiv ℝ c x v*fderiv ℝ C x v+fderiv ℝ d x v*fderiv ℝ D x v)+
        2*a x*((fderiv ℝ A x v)^2+(fderiv ℝ C x v)^2+(fderiv ℝ D x v)^2)-
        a x*realHessian A x v v)+
      (1+(a x)^2/(a x+b x)^2)*(realHessian b x v v-
        2*fderiv ℝ b x v*fderiv ℝ B x v-
        2*(fderiv ℝ c x v*fderiv ℝ C x v+fderiv ℝ d x v*fderiv ℝ D x v)+
        2*b x*((fderiv ℝ B x v)^2+(fderiv ℝ C x v)^2+(fderiv ℝ D x v)^2)-
        b x*realHessian B x v v)-
      2*((b x*(fderiv ℝ a x v-a x*fderiv ℝ A x v)-
            a x*(fderiv ℝ b x v-b x*fderiv ℝ B x v))^2+
        (a x+b x)^2*((fderiv ℝ c x v-a x*fderiv ℝ C x v)*
          (fderiv ℝ c x v-b x*fderiv ℝ C x v)+
          (fderiv ℝ d x v-a x*fderiv ℝ D x v)*
          (fderiv ℝ d x v-b x*fderiv ℝ D x v)))/(a x+b x)^3 := by
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
  have hHT := hermitianAdjTraceFieldTwo_realHessian_normalized ha hb hc hd hA hB hC hD
    hc0 hd0 hA1 hB1 hC0 hD0 v
  have hDD := hermitianDetFieldTwo_fderiv_diagonal hA hB hC hD hC0 hD0 v
  have hHD := hermitianDetFieldTwo_realHessian_diagonal hA hB hC hD hC0 hD0 v
  have hDN := hermitianDetFieldTwo_fderiv_diagonal ha hb hc hd hc0 hd0 v
  have hHN := hermitianDetFieldTwo_realHessian_diagonal ha hb hc hd hc0 hd0 v
  simp only [hA1,hB1,one_mul] at hDD hHD
  change realHessian (fun y => T y/Delta y+N y/T y) x v v = _
  rw [realHessian_add (hT.fun_div hDelta hDelta0) (hN.fun_div hT hT0),add_apply,add_apply,
    realHessian_div_real_at hT hDelta hDelta0,realHessian_div_real_at hN hT hT0]
  change fderiv ℝ T x v = _ at hDT
  change realHessian T x v v = _ at hHT
  change fderiv ℝ Delta x v = _ at hDD
  change realHessian Delta x v v = _ at hHD
  change fderiv ℝ N x v = _ at hDN
  change realHessian N x v v = _ at hHN
  rw [hTx,hDx,hNx,hDT,hHT,hDD,hHD,hDN,hHN]
  have hid := quotient_ratio_normalized_second_jet_two (a x) (b x)
    (fderiv ℝ a x v) (fderiv ℝ b x v) (fderiv ℝ c x v) (fderiv ℝ d x v)
    (fderiv ℝ A x v) (fderiv ℝ B x v) (fderiv ℝ C x v) (fderiv ℝ D x v)
    (realHessian a x v v) (realHessian b x v v) (realHessian A x v v) (realHessian B x v v) ht
  dsimp only at hid
  simp only [one_pow,div_one]
  linear_combination hid

end PowerConvexity
