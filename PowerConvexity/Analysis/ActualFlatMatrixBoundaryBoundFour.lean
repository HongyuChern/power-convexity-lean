import PowerConvexity.Calculus.ActualFlatQuadraticBarrierFour
import PowerConvexity.Analysis.ActualUniformNormalizationBoundsTwo

/-! # The explicit flat boundary barrier for the actual elliptic matrix
The trace and normal contraction estimates are consequences of the original
ellipticity constants and entry continuity; no boundary gradient is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_matrix_contraction_rankOne_energy_four (C : Mat) (v : E) :
    matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) C (realRankOneForm v) =
      inner ℝ v (matMulE C v) := by
  rw [matrixHessianContraction_rankOne]
  simp [EuclideanSpace.inner_single_right,PiLp.inner_apply,Real.inner_apply,
    matMulE_apply,Matrix.mulVec,dotProduct,mul_comm]

theorem actual_matrix_contraction_trace_four (C : Mat) :
    matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) C
      (realInnerForm : E →L[ℝ] E →L[ℝ] ℝ) = ∑ i, C i i := by
  change (∑ i, ∑ j, C i j*inner ℝ (EuclideanSpace.single j (1 : ℝ))
    (EuclideanSpace.single i (1 : ℝ))) = _
  simp [EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]

theorem actual_elliptic_matrix_contraction_trace_upper_four {U : Set E}
    (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U) :
    ∀ x ∈ U, matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
      (A.a x) (realInnerForm : E →L[ℝ] E →L[ℝ] ℝ) ≤ 4*A.Λ := by
  intro x hx
  rw [actual_matrix_contraction_trace_four]
  have hdiag (i : Fin (2+2)) : A.a x i i ≤ A.Λ := by
    have hh := (actual_elliptic_bounds_pointwise_two hU A ha x hx
      (EuclideanSpace.single i (1 : ℝ))).2
    simpa [EuclideanSpace.inner_single_left,matMulE_apply,Matrix.mulVec,dotProduct,
      EuclideanSpace.single_apply,EuclideanSpace.norm_single] using hh
  calc
    ∑ i, A.a x i i ≤ ∑ _i : Fin (2+2), A.Λ := Finset.sum_le_sum (fun i _ => hdiag i)
    _ = 4*A.Λ := by simp

theorem actual_flat_matrix_elliptic_normal_boundary_bound_four
    {N : E} (hN : ‖N‖=1)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) (actualFlatUpperBallFour N 1))
    (hpos : ∀ x ∈ actualFlatUpperBallFour N 1, (A.a x).PosDef)
    {F : ℝ} (hF : 0 ≤ F) {u : E → ℝ}
    (huC : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (hu2 : ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1))
    (hLu : ∀ x ∈ actualFlatUpperBallFour N 1,
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (A.a x) (realHessian u x)| ≤ F)
    (hu0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0)
    (hub : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ 1) :
    ∀ d ∈ Icc (0 : ℝ) 1, |u (d • N)| ≤ ((4*A.Λ+F+1)/A.lam+2)*d := by
  let L := fun x => matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) (A.a x)
  have hU := actualFlatUpperBallFour_isOpen N 1
  exact actual_flat_elliptic_normal_boundary_bound_four hN A.hlam
    (mul_nonneg (by norm_num) A.Λ_nonneg) hF L
    (fun x hx => matrixHessianContraction_positive _ (hpos x hx).posSemidef)
    (actual_elliptic_matrix_contraction_trace_upper_four hU A ha)
    (by
      intro x hx
      change A.lam ≤ matrixHessianContraction _ (A.a x) (realRankOneForm N)
      rw [actual_matrix_contraction_rankOne_energy_four]
      simpa only [hN,one_pow,mul_one] using
        (actual_elliptic_bounds_pointwise_two hU A ha x hx N).1)
    huC hu2 hLu hu0 hub

end PowerConvexity
