import PowerConvexity.Analysis.ActualNonlinearChartOperatorFour

/-! # Actual graph charts and their invertible differential -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualGraphShearFour (N : E) (rho : E → ℝ) (x : E) : E := x + rho x • N

def actualShearLinearEquivFour (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0) : E ≃L[ℝ] E :=
  { toLinearEquiv :=
      { toFun := fun v => v+l v • N
        invFun := fun v => v-l v • N
        map_add' := by intro v w; simp only [map_add,add_smul]; abel
        map_smul' := by intro a v; simp only [map_smul,smul_add,smul_smul,smul_eq_mul,RingHom.id_apply]
        left_inv := by intro v; simp only [map_add,map_smul,hl,smul_zero,add_zero,add_sub_cancel_right]
        right_inv := by intro v; simp only [map_sub,map_smul,hl,smul_zero,sub_zero,sub_add_cancel] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

theorem actual_shear_linear_apply_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0) (v : E) :
    actualShearLinearEquivFour N l hl v = v+l v • N := rfl

theorem actual_shear_linear_inverse_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0) (v : E) :
    (actualShearLinearEquivFour N l hl).symm v = v-l v • N := rfl

theorem actual_graph_shear_hasFDerivAt_four {N x : E} {rho : E → ℝ}
    (hrho : DifferentiableAt ℝ rho x) :
    HasFDerivAt (actualGraphShearFour N rho)
      (ContinuousLinearMap.id ℝ E+(fderiv ℝ rho x).smulRight N) x := by
  exact (hasFDerivAt_id x).add (hrho.hasFDerivAt.smul_const N)

theorem actual_graph_shear_fderiv_equiv_four {N x : E} {rho : E → ℝ}
    (hrho : DifferentiableAt ℝ rho x) (hN : fderiv ℝ rho x N = 0) :
    fderiv ℝ (actualGraphShearFour N rho) x =
      (actualShearLinearEquivFour N (fderiv ℝ rho x) hN).toContinuousLinearMap := by
  rw [(actual_graph_shear_hasFDerivAt_four hrho).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem actual_graph_shear_contDiffAt_four {N x : E} {rho : E → ℝ} {n : ℕ∞ω}
    (hrho : ContDiffAt ℝ n rho x) : ContDiffAt ℝ n (actualGraphShearFour N rho) x :=
  contDiffAt_id.add (hrho.smul contDiffAt_const)

end PowerConvexity
