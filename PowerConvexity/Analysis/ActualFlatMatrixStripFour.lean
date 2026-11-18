import PowerConvexity.Analysis.ActualFlatMatrixBoundaryBoundFour
import PowerConvexity.Calculus.ActualFlatBoundaryStripBoundFour

/-! # The explicit flat boundary barrier for the actual elliptic matrix
The same original ellipticity constants control the entire smaller closed
half ball, with no boundary differentiability input.
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

theorem actual_flat_matrix_elliptic_boundary_strip_bound_four
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
    ∀ x ∈ actualFlatClosedUpperBallFour N (1/2),
      |u x| ≤ (2*((4*A.Λ+F/4+1)/A.lam+2))*inner ℝ N x := by
  let L := fun x => matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) (A.a x)
  have hU := actualFlatUpperBallFour_isOpen N 1
  exact actual_flat_elliptic_boundary_strip_bound_four hN A.hlam
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
