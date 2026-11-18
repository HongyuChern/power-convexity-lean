import PowerConvexity.Analysis.ActualNormalPreservingNormalizationFour
import PowerConvexity.Analysis.ActualFlatResidualEquationFour

/-! # The actual classical nondivergence equation in normalized affine coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_linear_matrix_inverse_products_four (G : E ≃L[ℝ] E) :
    actualLinearMatrixTwo G*actualLinearMatrixTwo G.symm=1 ∧
      actualLinearMatrixTwo G.symm*actualLinearMatrixTwo G=1 := by
  constructor
  · apply actual_matMulE_ext_two
    intro v
    rw [actual_matMulE_mul_two,actual_linear_matrix_action_two,actual_linear_matrix_action_two,G.apply_symm_apply]
    ext i
    simp only [matMulE_apply,Matrix.one_mulVec]
  · apply actual_matMulE_ext_two
    intro v
    rw [actual_matMulE_mul_two,actual_linear_matrix_action_two,actual_linear_matrix_action_two,G.symm_apply_apply]
    ext i
    simp only [matMulE_apply,Matrix.one_mulVec]

theorem actual_inverse_congruence_trace_cancellation_four (G : E ≃L[ℝ] E) (A H : Mat) :
    ((actualLinearCongruenceMatrixTwo G A)*
      ((actualLinearMatrixTwo G)ᵀ*H*actualLinearMatrixTwo G)).trace=(A*H).trace := by
  let P := actualLinearMatrixTwo G
  let Q := actualLinearMatrixTwo G.symm
  have hPQ : P*Q=1 := (actual_linear_matrix_inverse_products_four G).1
  have ht : Qᵀ*Pᵀ=1 := by rw [← Matrix.transpose_mul,hPQ,Matrix.transpose_one]
  change ((Q*A*Qᵀ)*(Pᵀ*H*P)).trace=(A*H).trace
  calc
    _ = (Q*(A*(Qᵀ*Pᵀ)*H)*P).trace := by simp only [Matrix.mul_assoc]
    _ = (Q*(A*H)*P).trace := by rw [ht,Matrix.mul_one]
    _ = (P*Q*(A*H)).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hPQ,Matrix.one_mul]

theorem actual_bilinear_matrix_pullback_four (G : E ≃L[ℝ] E) (H : Bilin) :
    Matrix.of (fun i j : Fin (2+2) => H (G (EuclideanSpace.single i 1)) (G (EuclideanSpace.single j 1))) =
      (actualLinearMatrixTwo G)ᵀ*
        Matrix.of (fun i j : Fin (2+2) => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))*actualLinearMatrixTwo G := by
  ext i j
  simp only [Matrix.of_apply]
  rw [actual_bilinear_coordinate_expansion_two]
  simp only [← actual_linear_matrix_entry_two,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem actual_affine_euclidean_hessian_four (G : E ≃L[ℝ] E) (c : E) (r : ℝ)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u (c+G (r • x))) :
    euclideanHessian (fun z => u (c+G (r • z))) x =
      r^2 • ((actualLinearMatrixTwo G)ᵀ*euclideanHessian u (c+G (r • x))*actualLinearMatrixTwo G) := by
  have hm := actual_bilinear_matrix_pullback_four G (realHessian u (c+G (r • x)))
  have hu' : ContDiffAt ℝ 2 u (c+(r • G.toContinuousLinearMap) x) := by
    simpa only [_root_.smul_apply,map_smul,ContinuousLinearEquiv.coe_coe] using hu
  have he : (fun z => u (c+G (r • z)))=(fun z => u (c+(r • G.toContinuousLinearMap) z)) := by
    funext z
    simp only [_root_.smul_apply,map_smul,ContinuousLinearEquiv.coe_coe]
  rw [he]
  ext i j
  change realHessian (fun z => u (c+(r • G.toContinuousLinearMap) z)) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)=_
  rw [realHessian_comp_affine _ _ hu']
  have hpoint : c+(r • G.toContinuousLinearMap) x=c+G (r • x) := by
    simp only [_root_.smul_apply,ContinuousLinearEquiv.coe_coe,map_smul]
  rw [hpoint]
  have hentry := congrArg (fun B : Mat => B i j) hm
  change realHessian u (c+G (r • x)) (G (EuclideanSpace.single i 1)) (G (EuclideanSpace.single j 1)) =
    ((actualLinearMatrixTwo G)ᵀ*euclideanHessian u (c+G (r • x))*actualLinearMatrixTwo G) i j at hentry
  simp only [_root_.smul_apply,map_smul,smul_eq_mul,ContinuousLinearEquiv.coe_coe,Matrix.smul_apply]
  simp only [map_smul] at hentry
  rw [hentry]
  ring

theorem actual_hessian_contraction_trace_four (A : Mat) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, ∑ j, A i j*euclideanHessian u x i j)=(A*euclideanHessian u x).trace := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [euclideanHessian,euclideanHessian,realHessian_symm hu]

theorem actual_affine_classical_equation_transport_four (G : E ≃L[ℝ] E) (c : E) (r : ℝ)
    {A : E → Mat} {f u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u (c+G (r • x)))
    (heq : (∑ i, ∑ j, A (c+G (r • x)) i j*euclideanHessian u (c+G (r • x)) i j) = -f (c+G (r • x))) :
    (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G (A (c+G (r • x))) i j*
      euclideanHessian (fun z => u (c+G (r • z))) x i j) = -(r^2*f (c+G (r • x))) := by
  have hT : ContDiffAt ℝ 2 (fun z : E => c+G (r • z)) x := by fun_prop
  have huT : ContDiffAt ℝ 2 (fun z => u (c+G (r • z))) x := by
    simpa only [Function.comp_def] using hu.comp x hT
  rw [actual_hessian_contraction_trace_four _ huT,actual_affine_euclidean_hessian_four G c r hu,
    Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,actual_inverse_congruence_trace_cancellation_four,
    ← actual_hessian_contraction_trace_four _ hu,heq]
  ring

end PowerConvexity
