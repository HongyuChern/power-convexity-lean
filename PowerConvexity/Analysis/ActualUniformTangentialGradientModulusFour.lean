import PowerConvexity.Analysis.ActualUniformVariableDirectionalJetsFour
import PowerConvexity.Analysis.ActualUniformClosureTangentialResponseFour
import PowerConvexity.Analysis.ActualUniformDefiningTangentialFieldFour
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual interior derivative moduli for the tangential response

The derivative of Du(T) is controlled by the actual nonlinear Hessian modulus
and the common C2 bounds of u and T. No third derivative norm of u appears.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_variable_directional_fderiv_operator_four {u : E → ℝ} {T : E → E} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hT : DifferentiableAt ℝ T x) :
    fderiv ℝ (fun y => fderiv ℝ u y (T y)) x=
      (realHessian u x).flip (T x)+(fderiv ℝ u x).comp (fderiv ℝ T x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact actual_fderiv_variable_directional_four hu hT v

theorem actual_variable_directional_gradient_difference_four
    {u : E → ℝ} {T : E → E} {x y : E}
    (hux : ContDiffAt ℝ 2 u x) (huy : ContDiffAt ℝ 2 u y)
    (hTx : DifferentiableAt ℝ T x) (hTy : DifferentiableAt ℝ T y) :
    ‖fderiv ℝ (fun z => fderiv ℝ u z (T z)) x-
        fderiv ℝ (fun z => fderiv ℝ u z (T z)) y‖ ≤
      ‖realHessian u x-realHessian u y‖*‖T x‖+
        ‖realHessian u y‖*‖T x-T y‖+
        ‖fderiv ℝ u x-fderiv ℝ u y‖*‖fderiv ℝ T x‖+
        ‖fderiv ℝ u y‖*‖fderiv ℝ T x-fderiv ℝ T y‖ := by
  rw [actual_variable_directional_fderiv_operator_four hux hTx,
    actual_variable_directional_fderiv_operator_four huy hTy]
  have he : (realHessian u x).flip (T x)+(fderiv ℝ u x).comp (fderiv ℝ T x)-
      ((realHessian u y).flip (T y)+(fderiv ℝ u y).comp (fderiv ℝ T y))=
      ((realHessian u x-realHessian u y).flip (T x)+(realHessian u y).flip (T x-T y))+
        (fderiv ℝ u x-fderiv ℝ u y).comp (fderiv ℝ T x)+
        (fderiv ℝ u y).comp (fderiv ℝ T x-fderiv ℝ T y) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      _root_.add_apply,_root_.sub_apply,map_sub]
    ring
  rw [he]
  have h1 : ‖(realHessian u x-realHessian u y).flip (T x)‖ ≤
      ‖realHessian u x-realHessian u y‖*‖T x‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using
      (realHessian u x-realHessian u y).flip.le_opNorm (T x)
  have h2 : ‖(realHessian u y).flip (T x-T y)‖ ≤ ‖realHessian u y‖*‖T x-T y‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using (realHessian u y).flip.le_opNorm (T x-T y)
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2)) (ContinuousLinearMap.opNorm_comp_le _ _)))
    (ContinuousLinearMap.opNorm_comp_le _ _))

theorem actual_variable_directional_gradient_modulus_four
    {u : E → ℝ} {T : E → E} {x y : E} {G H T₀ D K d omega : ℝ}
    (hux : ContDiffAt ℝ 2 u x) (huy : ContDiffAt ℝ 2 u y)
    (hTx : DifferentiableAt ℝ T x) (hTy : DifferentiableAt ℝ T y)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hT₀ : 0 ≤ T₀) (hD : 0 ≤ D)
    (hHv : ‖realHessian u x-realHessian u y‖ ≤ omega)
    (hTv : ‖T x‖ ≤ T₀) (hHess : ‖realHessian u y‖ ≤ H)
    (hTdiff : ‖T x-T y‖ ≤ D*d) (hDdiff : ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ H*d)
    (hTD : ‖fderiv ℝ T x‖ ≤ D) (huD : ‖fderiv ℝ u y‖ ≤ G)
    (hDTdiff : ‖fderiv ℝ T x-fderiv ℝ T y‖ ≤ K*d) :
    ‖fderiv ℝ (fun z => fderiv ℝ u z (T z)) x-
        fderiv ℝ (fun z => fderiv ℝ u z (T z)) y‖ ≤ T₀*omega+(2*H*D+G*K)*d := by
  have homega : 0 ≤ omega := (realHessian u x-realHessian u y).opNorm_nonneg.trans hHv
  have hHd : 0 ≤ H*d := (fderiv ℝ u x-fderiv ℝ u y).opNorm_nonneg.trans hDdiff
  apply (actual_variable_directional_gradient_difference_four hux huy hTx hTy).trans
  calc
    _ ≤ omega*T₀+H*(D*d)+(H*d)*D+G*(K*d) :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul hHv hTv (norm_nonneg _) homega)
        (mul_le_mul hHess hTdiff (norm_nonneg _) hH))
        (mul_le_mul hDdiff hTD (norm_nonneg _) hHd))
        (mul_le_mul huD hDTdiff (norm_nonneg _) hG)
    _ = _ := by ring

theorem actual_distance_le_twice_scaled_power_four {d R beta : ℝ}
    (hd : 0 ≤ d) (hR : 0 < R) (hR1 : R ≤ 1) (hdR : d ≤ 2*R)
    (hb : 0 ≤ beta) (hb1 : beta ≤ 1) : d ≤ 2*(d/R)^beta := by
  have ht : 0 ≤ d/R := div_nonneg hd hR.le
  have ht2 : d/R ≤ 2 := (div_le_iff₀ hR).2 (by nlinarith)
  have hdt : d ≤ d/R := (le_div_iff₀ hR).2 (mul_le_of_le_one_right hd hR1)
  by_cases ht1 : d/R ≤ 1
  · have hh := Real.self_le_rpow_of_le_one ht ht1 hb1
    exact hdt.trans (hh.trans (by nlinarith [Real.rpow_nonneg ht beta]))
  · have hh : 1 ≤ (d/R)^beta := Real.one_le_rpow (le_of_lt (lt_of_not_ge ht1)) hb
    exact hdt.trans (by nlinarith)

theorem actual_variable_directional_gradient_holder_ball_four
    {u : E → ℝ} {T : E → E} {c : E} {R G H T₀ D K A beta : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hT₀ : 0 ≤ T₀) (hD : 0 ≤ D) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hb : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hu : ContDiffOn ℝ 2 u (ball c R)) (hT : ContDiffOn ℝ 2 T (ball c R))
    (huD : ∀ x ∈ ball c R, ‖fderiv ℝ u x‖ ≤ G)
    (huH : ∀ x ∈ ball c R, ‖realHessian u x‖ ≤ H)
    (hTval : ∀ x ∈ ball c R, ‖T x‖ ≤ T₀)
    (hTD : ∀ x ∈ ball c R, ‖fderiv ℝ T x‖ ≤ D)
    (hTH : ∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ T) x‖ ≤ K)
    (hHess : ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖realHessian u x-realHessian u y‖ ≤ A*(‖x-y‖/R)^beta) :
    ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖fderiv ℝ (fun z => fderiv ℝ u z (T z)) x-
        fderiv ℝ (fun z => fderiv ℝ u z (T z)) y‖ ≤
        (T₀*A+2*(2*H*D+G*K))*(‖x-y‖/R)^beta := by
  intro x hx y hy
  have hux := hu.contDiffAt (isOpen_ball.mem_nhds hx)
  have huy := hu.contDiffAt (isOpen_ball.mem_nhds hy)
  have hTx := hT.contDiffAt (isOpen_ball.mem_nhds hx)
  have hTy := hT.contDiffAt (isOpen_ball.mem_nhds hy)
  have hTdiff := (convex_ball c R).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hT.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)) hTD hy hx
  have huDdiff := (convex_ball c R).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ((hu.contDiffAt (isOpen_ball.mem_nhds hz)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)) huH hy hx
  have hTDdiff := (convex_ball c R).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ((hT.contDiffAt (isOpen_ball.mem_nhds hz)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)) hTH hy hx
  have hh := actual_variable_directional_gradient_modulus_four hux huy
    (hTx.differentiableAt (by norm_num)) (hTy.differentiableAt (by norm_num))
    hG hH hT₀ hD (hHess x hx y hy) (hTval x hx) (huH y hy) hTdiff huDdiff
    (hTD x hx) (huD y hy) hTDdiff
  have hdR : ‖x-y‖ ≤ 2*R := by
    have ht := dist_triangle x c y
    rw [dist_comm c y] at ht
    have hx' : dist x c < R := hx
    have hy' : dist y c < R := hy
    rw [dist_eq_norm] at ht
    linarith
  have hn := actual_distance_le_twice_scaled_power_four (norm_nonneg (x-y)) hR hR1 hdR hb hb1
  apply hh.trans
  have hc : 0 ≤ 2*H*D+G*K := by positivity
  have hm := mul_le_mul_of_nonneg_left hn hc
  nlinarith

end PowerConvexity
