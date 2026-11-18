import PowerConvexity.Analysis.ActualGraphPhysicalDilationFour
import PowerConvexity.Analysis.ActualUniformAffineBoundaryGraphsFour
import CHS.Calculus.EuclideanRescaling

/-! # Exact scale factors and common derivative bounds for the actual graph height

For psi(x)=rho(r x)/r, the derivative has no scale factor and the Hessian has
factor r. The displayed Lipschitz constants are r M and r^2 M respectively.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_physical_graph_fderiv_four {rho : E → ℝ} {r : ℝ} (hr : r ≠ 0)
    {x : E} (hrho : DifferentiableAt ℝ rho (r • x)) :
    fderiv ℝ (actualPhysicalGraphHeightFour rho r) x=fderiv ℝ rho (r • x) := by
  have hd := (hrho.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul r)).const_smul r⁻¹
  rw [show fderiv ℝ (actualPhysicalGraphHeightFour rho r) x=
    r⁻¹ • (fderiv ℝ rho (r • x)).comp (r • ContinuousLinearMap.id ℝ E) from hd.fderiv]
  ext v
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  field_simp

theorem actual_physical_graph_hessian_four {rho : E → ℝ} {r : ℝ} (hr : r ≠ 0)
    {x : E} (hrho : ContDiffAt ℝ 2 rho (r • x)) :
    realHessian (actualPhysicalGraphHeightFour rho r) x=r • realHessian rho (r • x) := by
  let w := euclideanRescalePotential rho 0 r
  have hw : ContDiffAt ℝ 2 w x := by
    apply contDiffAt_const.mul
    have houter : ContDiffAt ℝ 2 rho ((0 : E)+r • x) := by simpa only [zero_add] using hrho
    exact houter.comp x (contDiffAt_const.add (contDiffAt_id.const_smul r))
  have he : actualPhysicalGraphHeightFour rho r=(fun y => r*w y) := by
    funext y
    simp only [actualPhysicalGraphHeightFour,w,euclideanRescalePotential,zero_add]
    field_simp
  rw [he,realHessian_const_mul_at hw]
  have hh := realHessian_euclideanRescalePotential (u := rho) (x₀ := (0 : E)) hr
    (by simpa only [zero_add] using hrho)
  simpa only [w,zero_add] using congrArg (fun H => r • H) hh

theorem actual_physical_graph_uniform_derivative_bounds_four
    {rho : E → ℝ} {S r M : ℝ} (hS : 0 < S) (hr : 0 < r) (hrS : 2*r ≤ S) (hM : 0 ≤ M)
    (hreg : ∀ x ∈ closedBall (0 : E) S, ContDiffAt ℝ 3 rho x)
    (hD0 : fderiv ℝ rho 0=0)
    (hH : ∀ x ∈ closedBall (0 : E) S, ‖realHessian rho x‖ ≤ M)
    (hT : ∀ x ∈ closedBall (0 : E) S, ‖fderiv ℝ (realHessian rho) x‖ ≤ M) :
    let psi := actualPhysicalGraphHeightFour rho r
    (∀ x ∈ closedBall (0 : E) 2,
      ContDiffAt ℝ 3 psi x ∧ ‖fderiv ℝ psi x‖ ≤ 2*r*M ∧ ‖realHessian psi x‖ ≤ r*M) ∧
    (∀ x ∈ closedBall (0 : E) 2, ∀ y ∈ closedBall (0 : E) 2,
      ‖fderiv ℝ psi x-fderiv ℝ psi y‖ ≤ (r*M)*‖x-y‖ ∧
      ‖realHessian psi x-realHessian psi y‖ ≤ (r^2*M)*‖x-y‖) := by
  let psi := actualPhysicalGraphHeightFour rho r
  have hmap (x : E) (hx : x ∈ closedBall (0 : E) 2) : r • x ∈ closedBall (0 : E) S := by
    have hx2 : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hx2 hr.le).trans (by linarith)
  have hD (x y : E) (hx : x ∈ closedBall (0 : E) S) (hy : y ∈ closedBall (0 : E) S) :
      ‖fderiv ℝ rho x-fderiv ℝ rho y‖ ≤ M*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hreg z hz).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
      hH (convex_closedBall (0 : E) S) hy hx
  have hHlip (x y : E) (hx : x ∈ closedBall (0 : E) S) (hy : y ∈ closedBall (0 : E) S) :
      ‖realHessian rho x-realHessian rho y‖ ≤ M*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (((hreg z hz).fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num))
      hT (convex_closedBall (0 : E) S) hy hx
  have hpsiD (x : E) (hx : x ∈ closedBall (0 : E) 2) :
      fderiv ℝ psi x=fderiv ℝ rho (r • x) :=
    actual_physical_graph_fderiv_four hr.ne' ((hreg _ (hmap x hx)).differentiableAt (by norm_num))
  have hpsiH (x : E) (hx : x ∈ closedBall (0 : E) 2) :
      realHessian psi x=r • realHessian rho (r • x) :=
    actual_physical_graph_hessian_four hr.ne' ((hreg _ (hmap x hx)).of_le (by norm_num))
  constructor
  · intro x hx
    refine ⟨contDiffAt_const.mul ((hreg _ (hmap x hx)).comp x (contDiffAt_id.const_smul r)),?_,?_⟩
    · rw [hpsiD x hx]
      have hh := hD (r • x) 0 (hmap x hx) (mem_closedBall_self hS.le)
      rw [hD0,sub_zero,sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh
      have hx2 : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
      exact hh.trans (by nlinarith [mul_nonneg hr.le hM])
    · rw [hpsiH x hx,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left (hH _ (hmap x hx)) hr.le
  · intro x hx y hy
    have hdist : ‖r • x-r • y‖=r*‖x-y‖ := by
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    constructor
    · rw [hpsiD x hx,hpsiD y hy]
      have hh := hD (r • x) (r • y) (hmap x hx) (hmap y hy)
      rw [hdist] at hh
      exact hh.trans_eq (by ring)
    · have he : r • realHessian rho (r • x)-r • realHessian rho (r • y)=
          r • (realHessian rho (r • x)-realHessian rho (r • y)) := by
        ext v w
        simp only [_root_.sub_apply,_root_.smul_apply,smul_eq_mul]
        ring
      rw [hpsiH x hx,hpsiH y hy,he,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      have hh := hHlip (r • x) (r • y) (hmap x hx) (hmap y hy)
      rw [hdist] at hh
      exact (mul_le_mul_of_nonneg_left hh hr.le).trans_eq (by ring)

end PowerConvexity
