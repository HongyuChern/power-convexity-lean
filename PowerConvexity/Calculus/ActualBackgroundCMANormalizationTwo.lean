import PowerConvexity.Calculus.ComplexScaledPullbackTwo
import PowerConvexity.Algebra.BackgroundCongruenceTwo

/-! # The actual changed-background CMA equation on the same unit ball.
The normalization is the actual function 256 w(T_G x/16). Its domain,
regularity, positive branch, determinant and value bound are all proved.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem complex_normalizing_contraction_norm_two {G : W}
    (hG : ‖complexMatrixRealMap G‖ ≤ 16) (x : E) :
    ‖(1/16 : ℝ) • complexMatrixRealMap G x‖ ≤ ‖x‖ := by
  have hh := ((complexMatrixRealMap G).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hG (norm_nonneg x))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/16)]
  linarith only [hh]

theorem actual_background_CMA_normalizes_two {C G : W}
    (hG : G.transpose*C*G.map star = 1) (hGd : Complex.normSq G.det = 1)
    (hGn : ‖complexMatrixRealMap G‖ ≤ 16) {w : E → ℝ} {ε : ℝ}
    (hwc : ContinuousOn w (closedBall 0 1)) (hw : ContDiffOn ℝ 2 w (ball 0 1))
    (hp : ∀ x ∈ ball (0 : E) 1, (C+complexHessian realDirections imagDirections w x).PosSemidef)
    (hd : ∀ x ∈ ball (0 : E) 1, (C+complexHessian realDirections imagDirections w x).det = 1)
    (hb : ∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) :
    ContinuousOn (complexScaledPullbackTwo G (1/16) w) (closedBall 0 1) ∧
      ContDiffOn ℝ 2 (complexScaledPullbackTwo G (1/16) w) (ball 0 1) ∧
      (∀ x ∈ ball (0 : E) 1,
        (1+complexHessian realDirections imagDirections (complexScaledPullbackTwo G (1/16) w) x).PosSemidef) ∧
      (∀ x ∈ ball (0 : E) 1,
        (1+complexHessian realDirections imagDirections (complexScaledPullbackTwo G (1/16) w) x).det = 1) ∧
      ∀ x ∈ closedBall (0 : E) 1, |complexScaledPullbackTwo G (1/16) w x| ≤ 256*ε := by
  let T : E →L[ℝ] E := (1/16 : ℝ) • complexMatrixRealMap G
  have hmC : MapsTo T (closedBall (0 : E) 1) (closedBall 0 1) := by
    intro x hx
    have hh := complex_normalizing_contraction_norm_two hGn x
    have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    simpa only [T,ContinuousLinearMap.smul_apply,mem_closedBall,dist_zero_right] using hh.trans hx'
  have hmB : MapsTo T (ball (0 : E) 1) (ball 0 1) := by
    intro x hx
    have hh := complex_normalizing_contraction_norm_two hGn x
    have hx' : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    simpa only [T,ContinuousLinearMap.smul_apply,mem_ball,dist_zero_right] using hh.trans_lt hx'
  have hwAt (x : E) (hx : x ∈ ball 0 1) : ContDiffAt ℝ 2 w (T x) :=
    (hw (T x) (hmB hx)).contDiffAt (isOpen_ball.mem_nhds (hmB hx))
  have hvc : ContinuousOn (complexScaledPullbackTwo G (1/16) w) (closedBall 0 1) := by
    change ContinuousOn (fun x => ((1/16 : ℝ)^2)⁻¹*(w ∘ T) x) (closedBall 0 1)
    exact continuousOn_const.mul (hwc.comp T.continuous.continuousOn hmC)
  have hv2 : ContDiffOn ℝ 2 (complexScaledPullbackTwo G (1/16) w) (ball 0 1) := by
    intro x hx
    exact (contDiffAt_const.mul ((hwAt x hx).comp x T.contDiff.contDiffAt)).contDiffWithinAt
  have he (x : E) (hx : x ∈ ball 0 1) :
      1+complexHessian realDirections imagDirections (complexScaledPullbackTwo G (1/16) w) x =
      G.transpose*(C+complexHessian realDirections imagDirections w (T x))*G.map star := by
    rw [complexScaledPullbackTwo_complexHessian (by norm_num) (hwAt x hx),normalized_background_sum_two hG]
    simp only [T,ContinuousLinearMap.smul_apply]
  refine ⟨hvc,hv2,?_,?_,?_⟩
  · intro x hx
    rw [he x hx]
    exact complex_congruence_posSemidef_two (hp (T x) (hmB hx))
  · intro x hx
    rw [he x hx]
    exact complex_congruence_det_one_two hGd (hd (T x) (hmB hx))
  · intro x hx
    have hh := mul_le_mul_of_nonneg_left (hb (T x) (hmC hx)) (by norm_num : (0:ℝ) ≤ 256)
    simpa only [T,ContinuousLinearMap.smul_apply,complexScaledPullbackTwo,abs_mul,show ((1/16 : ℝ)^2)⁻¹ = 256 by norm_num,
      abs_of_pos (by norm_num : (0:ℝ)<256)] using hh

end PowerConvexity
