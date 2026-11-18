import PowerConvexity.Analysis.ActualUniformGraphHeightDilationFour

/-! # The same actual boundary graph on a common physical unit scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_common_physical_unit_graph_four
    {S r M : ℝ} (hS : 0 < S) (hr : 0 < r) (hrS : 2*r ≤ S) (hM : 0 ≤ M)
    {U : Set E} {c N : E} (G : E ≃L[ℝ] E) {rho : E → ℝ}
    (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x)
    (hreg : ∀ x ∈ closedBall (0 : E) S, ContDiffAt ℝ 3 rho x)
    (hH : ∀ x ∈ closedBall (0 : E) S, ‖realHessian rho x‖ ≤ M)
    (hT : ∀ x ∈ closedBall (0 : E) S, ‖fderiv ℝ (realHessian rho) x‖ ≤ M)
    (hmap : ∀ x ∈ closedBall (0 : E) S,
      c+G (actualGraphShearFour N rho x) ∈ U ↔ 0 < inner ℝ N x)
    (hzero : ∀ u : E → ℝ, (∀ z ∈ frontier U, u z=0) →
      ∀ x ∈ closedBall (0 : E) (S/2), inner ℝ N x=0 →
        u (c+G (actualGraphShearFour N rho x))=0) :
    let psi := actualPhysicalGraphHeightFour rho r
    psi 0=0 ∧ fderiv ℝ psi 0=0 ∧
      (∀ x : E, ∀ t : ℝ, psi (x+t • N)=psi x) ∧
      (∀ x ∈ closedBall (0 : E) 2,
        ContDiffAt ℝ 3 psi x ∧ ‖fderiv ℝ psi x‖ ≤ 2*r*M ∧ ‖realHessian psi x‖ ≤ r*M) ∧
      (∀ x ∈ closedBall (0 : E) 2, ∀ y ∈ closedBall (0 : E) 2,
        ‖fderiv ℝ psi x-fderiv ℝ psi y‖ ≤ (r*M)*‖x-y‖ ∧
        ‖realHessian psi x-realHessian psi y‖ ≤ (r^2*M)*‖x-y‖) ∧
      (∀ x ∈ closedBall (0 : E) 2,
        c+G (r • actualGraphShearFour N psi x) ∈ U ↔ 0 < inner ℝ N x) ∧
      (∀ u : E → ℝ, (∀ z ∈ frontier U, u z=0) →
        ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 →
          u (c+G (r • actualGraphShearFour N psi x))=0) := by
  let psi := actualPhysicalGraphHeightFour rho r
  have hj := actual_physical_graph_regularity_four
    (hreg 0 (mem_closedBall_self hS.le)) hrho0 hD0 (R := r)
  have hb := actual_physical_graph_uniform_derivative_bounds_four hS hr hrS hM hreg hD0 hH hT
  refine ⟨hj.2.1,hj.2.2,actual_physical_graph_normal_invariance_four hinv r,hb.1,hb.2,?_,?_⟩
  · intro x hx
    have hx2 : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hscale : r • x ∈ closedBall (0 : E) S := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hx2 hr.le).trans (by linarith)
    rw [actual_physical_graph_conjugation_four hr.ne']
    exact (hmap _ hscale).trans (by rw [inner_smul_right]; exact mul_pos_iff_of_pos_left hr)
  · intro u hu x hx hNx
    have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hscale : r • x ∈ closedBall (0 : E) (S/2) := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hx1 hr.le).trans (by linarith)
    rw [actual_physical_graph_conjugation_four hr.ne']
    apply hzero u hu _ hscale
    simp only [inner_smul_right,hNx,mul_zero]

end PowerConvexity
