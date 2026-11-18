import PowerConvexity.Analysis.ActualFlatSourceCorrectionFour

/-! # The exact frozen boundary equation of the reconstructed quadratic -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_quadratic_source_identity_trace_four (q : E → ℝ) (x : E) :
    quadraticScalarSourceTwo (fun _ => (1 : Mat)) q x =
      -(realBlockHessian realDirections imagDirections q x).trace := by
  rw [quadraticScalarSourceTwo]
  simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,if_true]
  change -(∑ i : Fin (2+2), realHessian q x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) = _
  rw [actual_euclidean_trace_eq_block_trace_two]

theorem actual_flat_source_quadratic_trace_four {N : E} (hN : ‖N‖=1) (b : ℝ) (x : E) :
    (realBlockHessian realDirections imagDirections (actualFlatSourceQuadraticFour N b) x).trace = -b := by
  have hh := actualFlatSourceQuadraticFour_source_identity hN b x
  rw [actual_quadratic_source_identity_trace_four] at hh
  linarith

theorem actual_quadratic_update_trace_four {q p : E → ℝ} {R a : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (hR : 0 < R) (x : E) :
    (realBlockHessian realDirections imagDirections (scalarQuadraticUpdateTwo q p R a) x).trace =
      (realBlockHessian realDirections imagDirections q x).trace+
        a*(realBlockHessian realDirections imagDirections p (R⁻¹ • x)).trace := by
  have he : realBlockHessian realDirections imagDirections (scalarQuadraticUpdateTwo q p R a) x =
      realBlockHessian realDirections imagDirections q x+
        a • realBlockHessian realDirections imagDirections p (R⁻¹ • x) := by
    ext i j
    simp only [realBlockHessian,scalarQuadraticUpdateTwo_realHessian hq hp hR,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,Pi.add_apply,
      _root_.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.smul_apply]
  rw [he,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul]

theorem actual_flat_corrected_quadratic_frozen_trace_four {N : E} (hN : ‖N‖=1)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) {R a b : ℝ} (hR : 0 < R)
    (hpt : ∀ x, (realBlockHessian realDirections imagDirections p x).trace=0) (x : E) :
    (realBlockHessian realDirections imagDirections
      (scalarQuadraticUpdateTwo (actualFlatSourceQuadraticFour N b) p R a) x).trace = -b := by
  rw [actual_quadratic_update_trace_four (actualFlatSourceQuadraticFour_quadratic N b) hp hR,
    actual_flat_source_quadratic_trace_four hN,hpt,mul_zero,add_zero]

end PowerConvexity
