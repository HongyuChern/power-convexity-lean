import PowerConvexity.Calculus.ComplexScaledPullbackTwo

/-! # The actual rescaled error after subtracting a quadratic.
The constant background is exactly I plus the actual complex Hessian of
the previous polynomial. No identity-background equation is silently reused.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_complexHessian_sub_two {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) :
    complexHessian realDirections imagDirections (fun y => u y-q y) x =
      complexHessian realDirections imagDirections u x-complexHessian realDirections imagDirections q x := by
  have he : (fun y => u y-q y) = fun y => u y+(-1)*q y := by funext y; ring
  rw [he,complexHessian_add_at hu (contDiffAt_const.mul hq),complexHessian_const_mul_at hq]
  simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_smul,one_smul,sub_eq_add_neg]

def quadraticResidualTwo (w q : E → ℝ) (R : ℝ) : E → ℝ :=
  complexScaledPullbackTwo 1 R (fun x => w x-q x)

theorem quadraticResidualTwo_apply (w q : E → ℝ) (R : ℝ) (x : E) :
    quadraticResidualTwo w q R x = (R^2)⁻¹*(w (R • x)-q (R • x)) := by
  simp only [quadraticResidualTwo,complexScaledPullbackTwo,complexMatrixRealMap_one]

theorem actual_quadratic_residual_properties_two {w q : E → ℝ} {R ε : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hq : IsQuadraticPolynomial q)
    (hwc : ContinuousOn w (closedBall 0 1)) (hw : ContDiffOn ℝ 2 w (ball 0 1))
    (hb : ∀ x ∈ closedBall (0 : E) R, |w x-q x| ≤ ε*R^2) :
    ContinuousOn (quadraticResidualTwo w q R) (closedBall 0 1) ∧
      ContDiffOn ℝ 2 (quadraticResidualTwo w q R) (ball 0 1) ∧
      (∀ x ∈ ball (0 : E) 1,
        (1+complexHessian realDirections imagDirections q 0)+
          complexHessian realDirections imagDirections (quadraticResidualTwo w q R) x =
        1+complexHessian realDirections imagDirections w (R • x)) ∧
      ∀ x ∈ closedBall (0 : E) 1, |quadraticResidualTwo w q R x| ≤ ε := by
  have hI : (1 : W).map star = 1 := by
    change (1 : W).transpose.conjTranspose = 1
    simp only [Matrix.transpose_one,Matrix.conjTranspose_one]
  have hqC := IsQuadraticPolynomial_contDiff hq 2
  let T : E →L[ℝ] E := R • ContinuousLinearMap.id ℝ E
  have hmR : MapsTo T (closedBall (0 : E) 1) (closedBall 0 R) := by
    intro x hx
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    change dist (R • x) 0 ≤ R
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    nlinarith only [mul_le_mul_of_nonneg_left hn hR.le]
  have hmC : MapsTo T (closedBall (0 : E) 1) (closedBall 0 1) :=
    fun _ hx => closedBall_subset_closedBall hR1 (hmR hx)
  have hmB : MapsTo T (ball (0 : E) 1) (ball 0 1) := by
    intro x hx
    have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    change dist (R • x) 0 < 1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    exact (mul_lt_mul_of_pos_left hn hR).trans_le (by simpa using hR1)
  have hwAt (x : E) (hx : x ∈ ball 0 1) : ContDiffAt ℝ 2 w (R • x) :=
    (hw (T x) (hmB hx)).contDiffAt (isOpen_ball.mem_nhds (hmB hx))
  have he : quadraticResidualTwo w q R = fun x => (R^2)⁻¹*(w (T x)-q (T x)) :=
    funext (quadraticResidualTwo_apply w q R)
  refine ⟨?_,?_,?_,?_⟩
  · rw [he]
    exact continuousOn_const.mul ((hwc.comp T.continuous.continuousOn hmC).sub
      ((hqC.continuous.comp T.continuous).continuousOn))
  · rw [he]
    intro x hx
    exact (contDiffAt_const.mul (((hwAt x hx).comp x T.contDiff.contDiffAt).sub
      (hqC.contDiffAt.comp x T.contDiff.contDiffAt))).contDiffWithinAt
  · intro x hx
    change (1+complexHessian realDirections imagDirections q 0)+
      complexHessian realDirections imagDirections (complexScaledPullbackTwo 1 R (fun y => w y-q y)) x = _
    rw [complexScaledPullbackTwo_complexHessian hR
      (by simpa only [complexMatrixRealMap_one] using (hwAt x hx).sub hqC.contDiffAt)]
    simp only [Matrix.transpose_one,hI,Matrix.one_mul,Matrix.mul_one,
      complexMatrixRealMap_one]
    rw [actual_complexHessian_sub_two (hwAt x hx) hqC.contDiffAt,
      quadratic_complexHessian_from_zero_two hq (R • x)]
    abel
  · intro x hx
    rw [quadraticResidualTwo_apply,abs_mul,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hR))]
    exact (mul_le_mul_of_nonneg_left (hb (T x) (hmR hx)) (by positivity)).trans_eq (by field_simp)

end PowerConvexity
