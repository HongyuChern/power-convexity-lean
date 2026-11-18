import PowerConvexity.Analysis.ActualInverseGraphFrozenFour
import PowerConvexity.Calculus.UniformQuadraticRemainder

/-! # Exact inverse-graph Taylor error with explicit dependence on the polynomial jet -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_inverse_graph_taylor_formula_four {N : E} {rho p : E → ℝ}
    (hrho : ContDiffAt ℝ 2 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hp : IsQuadraticPolynomial p) (x : E) :
    secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho) x=
      p x-fderiv ℝ p 0 N*secondTaylorPolynomialZero rho x := by
  have hpC := (IsQuadraticPolynomial_contDiff hp 2).contDiffAt (x := (0 : E))
  have hj := actual_inverse_graph_composition_jets_four (N := N) hrho hrho0 hD0 hpC
  have hpT := quadratic_exact_Taylor hp 0 x
  simp only [sub_zero] at hpT
  rw [secondTaylorPolynomialZero,Function.comp_apply,actual_inverse_graph_value_four hrho0,
    hj.1]
  simp only [_root_.smul_apply,smul_eq_mul,hj.2,secondTaylorPolynomialZero,hrho0,hD0,
    _root_.zero_apply,zero_add]
  rw [hpT]
  ring

theorem actual_inverse_graph_taylor_error_identity_four {N : E} {rho p : E → ℝ}
    (hrho : ContDiffAt ℝ 2 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hp : IsQuadraticPolynomial p) (x : E) :
    p (actualInverseGraphFour N rho x)-secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho) x=
      -(fderiv ℝ p 0 N)*(rho x-secondTaylorPolynomialZero rho x)-
        rho x*realHessian p 0 x N+(rho x)^2/2*realHessian p 0 N N := by
  have ht := quadratic_exact_Taylor hp x (actualInverseGraphFour N rho x)
  have hd : actualInverseGraphFour N rho x-x=(-rho x) • N := by
    simp only [actualInverseGraphFour,actualGraphShearFour,add_sub_cancel_left]
  rw [hd,quadratic_fderiv_from_jet_zero hp x,quadratic_realHessian_from_jet_zero hp x] at ht
  simp only [ContinuousLinearMap.add_apply,map_smul,_root_.smul_apply,smul_eq_mul] at ht
  rw [actual_inverse_graph_taylor_formula_four hrho hrho0 hD0 hp,ht]
  ring

end PowerConvexity
