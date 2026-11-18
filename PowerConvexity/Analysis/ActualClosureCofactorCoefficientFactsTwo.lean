import PowerConvexity.Analysis.ActualClosureCofactorHolderCoefficientTwo

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_closure_cofactor_coefficient_lower_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) :
    (actualClosureCofactorEllipticCoeffTwo hU hu J A hA).lam=A.lam := rfl

theorem actual_closure_cofactor_coefficient_upper_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) :
    (actualClosureCofactorEllipticCoeffTwo hU hu J A hA).Λ=A.Λ := rfl

theorem actual_closure_cofactor_coefficient_interior_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) {x : E} (hx : x ∈ U) :
    (actualClosureCofactorEllipticCoeffTwo hU hu J A hA).a x=c⁻¹ • complexCofactorCoeff u x := by
  rw [actual_closure_cofactor_coefficient_agrees_two hU hu J A hA (subset_closure hx)]
  have he : J.hessian x=realHessian u x := J.hessian_eq hx
  rw [he,actual_cofactor_matrix_form_eq_two (hu.contDiffAt (hU.mem_nhds hx))]

end PowerConvexity
