import PowerConvexity.Analysis.ActualC1LocalLipschitzFour
import PowerConvexity.Calculus.SecondTaylorHessianModulus

/-! # An actual cubic Taylor error from local C3 regularity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_local_cubic_taylor_four {g : E → ℝ} (hg : ContDiffAt ℝ 3 g 0) :
    ∃ R > 0, R ≤ 1 ∧ ∃ K ≥ 0, ∀ x ∈ closedBall (0 : E) R,
      |g x-secondTaylorPolynomialZero g x| ≤ K*‖x‖^3 := by
  have hH : ContDiffAt ℝ 1 (realHessian g) 0 :=
    (hg.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  obtain ⟨R,hR,hR1,K,hK,hLip⟩ := actual_C1_closed_ball_lipschitz_four hH
  have hnear : ∀ᶠ x in 𝓝 (0 : E), ContDiffAt ℝ 2 g x :=
    (hg.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).eventually (by norm_num)
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let S := min R (d/2)
  have hS : 0 < S := lt_min hR (half_pos hd)
  have hSR : S ≤ R := min_le_left _ _
  have hC (x : E) (hx : x ∈ closedBall 0 S) : ContDiffAt ℝ 2 g x := by
    apply hball
    have hxS : dist x 0 ≤ S := hx
    have hSd : S ≤ d/2 := min_le_right _ _
    change dist x 0 < d
    linarith
  refine ⟨S,hS,hSR.trans hR1,K,hK,?_⟩
  intro x hx
  by_cases hx0 : x=0
  · subst x
    simp only [secondTaylorPolynomialZero_value,sub_self,abs_zero,norm_zero]
    norm_num
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hnS : ‖x‖ ≤ S := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hsub : closedBall (0 : E) ‖x‖ ⊆ closedBall 0 S := closedBall_subset_closedBall hnS
  have hbound (y : E) (hy : y ∈ closedBall 0 ‖x‖) :
      ‖realHessian g y-realHessian g 0‖ ≤ K*‖x‖ := by
    have hh := hLip y (closedBall_subset_closedBall hSR (hsub hy)) 0 (mem_closedBall_self hR.le)
    rw [sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hy) hK)
  have hh := actual_secondTaylor_error_of_hessian_modulus hn (mul_nonneg hK hn.le)
    (fun y hy => hC y (hsub hy)) hbound x (by simp only [mem_closedBall,dist_zero_right,le_refl])
  calc
    |g x-secondTaylorPolynomialZero g x| ≤ K*‖x‖*‖x‖^2 := hh
    _ = K*‖x‖^3 := by ring

end PowerConvexity
