import PowerConvexity.Analysis.ActualGraphShearHessianFour
import PowerConvexity.Calculus.ActualLocalCubicTaylorFour

/-! # Actual first and second jets after the inverse graph substitution -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualInverseGraphFour (N : E) (rho : E → ℝ) : E → E :=
  actualGraphShearFour N (fun x => -rho x)

theorem actual_inverse_graph_value_four {N : E} {rho : E → ℝ} (hrho0 : rho 0=0) :
    actualInverseGraphFour N rho 0=0 := by
  simp only [actualInverseGraphFour,actualGraphShearFour,hrho0,neg_zero,zero_smul,add_zero]

theorem actual_inverse_graph_contDiffAt_four {N x : E} {rho : E → ℝ} {n : ℕ∞ω}
    (hrho : ContDiffAt ℝ n rho x) : ContDiffAt ℝ n (actualInverseGraphFour N rho) x :=
  actual_graph_shear_contDiffAt_four hrho.neg

theorem actual_inverse_graph_fderiv_four {N : E} {rho : E → ℝ}
    (hrho : DifferentiableAt ℝ rho 0) (hD0 : fderiv ℝ rho 0=0) :
    fderiv ℝ (actualInverseGraphFour N rho) 0=ContinuousLinearMap.id ℝ E := by
  rw [actualInverseGraphFour,(actual_graph_shear_hasFDerivAt_four (N := N)
    (rho := fun x => -rho x) hrho.neg).fderiv,
    fderiv_fun_neg,hD0]
  simp

theorem actual_inverse_graph_composition_jets_four {N : E} {rho p : E → ℝ}
    (hrho : ContDiffAt ℝ 2 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hp : ContDiffAt ℝ 2 p 0) :
    fderiv ℝ (p ∘ actualInverseGraphFour N rho) 0=fderiv ℝ p 0 ∧
    ∀ v w, realHessian (p ∘ actualInverseGraphFour N rho) 0 v w=
      realHessian p 0 v w-fderiv ℝ p 0 N*realHessian rho 0 v w := by
  have hPsi0 := actual_inverse_graph_value_four (N := N) hrho0
  have hPsi := actual_inverse_graph_contDiffAt_four (N := N) hrho
  have hDPsi := actual_inverse_graph_fderiv_four (N := N)
    (hrho.differentiableAt (by norm_num)) hD0
  have hp' : ContDiffAt ℝ 2 p (actualInverseGraphFour N rho 0) := by simpa only [hPsi0] using hp
  constructor
  · rw [fderiv_comp 0 (hp'.differentiableAt (by norm_num))
      (hPsi.differentiableAt (by norm_num)),hPsi0,hDPsi,ContinuousLinearMap.comp_id]
  · intro v w
    rw [actual_nonlinear_chart_hessian_four hp' hPsi,hPsi0,hDPsi]
    have h2 := actual_graph_shear_second_derivative_four (N := N) hrho.neg v w
    change fderiv ℝ (fderiv ℝ (actualInverseGraphFour N rho)) 0 v w = _ at h2
    rw [h2,realHessian_neg]
    simp only [ContinuousLinearMap.id_apply,ContinuousLinearMap.neg_apply,map_smul,smul_eq_mul]
    ring

theorem actual_inverse_graph_inverse_four {N : E} {rho : E → ℝ}
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) (x : E) :
    actualInverseGraphFour N rho (actualGraphShearFour N rho x)=x ∧
    actualGraphShearFour N rho (actualInverseGraphFour N rho x)=x := by
  constructor
  · change (x+rho x • N)+(-rho (x+rho x • N)) • N=x
    rw [hinv x (rho x),neg_smul]
    abel
  · change (x+(-rho x) • N)+rho (x+(-rho x) • N) • N=x
    rw [hinv x (-rho x),neg_smul]
    abel

end PowerConvexity
