import PowerConvexity.Analysis.ActualDistributionalQuadraticSourceTwo

/-! # Actual C2 cofactor matrices supply all weak quadratic sources

On every compact interior ball, the actual scaled cofactor is continuous
and has zero distributional column divergence.  This supplies the exact
polynomial source interface used by the prescribed-exponent iteration;
no third derivative of the potential or first derivative of the matrix is
assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_hasWeakDiv_zero_congr_on_two
    {U : Set E} (hU : IsOpen U) {F G : E → E}
    (hdiv : HasWeakDiv (fun _ => 0) F U) (he : EqOn F G U) :
    HasWeakDiv (fun _ => 0) G U := by
  intro phi hp hc hs
  rw [← hdiv phi hp hc hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  rw [he hx]

theorem actual_hasWeakDiv_zero_const_smul_two
    {U : Set E} {F : E → E} (hdiv : HasWeakDiv (fun _ => 0) F U) (c : ℝ) :
    HasWeakDiv (fun _ => 0) (fun x => c • F x) U := by
  intro phi hp hc hs
  have h := hdiv phi hp hc hs
  change (∫ x in U, ∑ i, c*F x i*fderiv ℝ phi x (EuclideanSpace.single i 1))=
    -∫ x in U, (0 : ℝ)*phi x
  simp only [mul_assoc,← Finset.mul_sum]
  rw [integral_const_mul,h]
  simp

theorem actual_C2_scaled_cofactor_weak_quadratic_sources_two
    {V : Set E} (hV : IsOpen V) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u V)
    {c : E} {r k : ℝ} (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (ha : ∀ x ∈ V, A.a x=k • complexCofactorCoeff u x) :
    ActualWeakQuadraticSourcesTwo A := by
  have hc := actual_C2_cofactor_continuousOn_two hV hu
  have hAc (i j : Fin (2+2)) : ContinuousOn (fun x => A.a x i j) (closedBall c r) := by
    apply (((continuousOn_pi.mp (continuousOn_pi.mp hc i) j).const_mul k).mono hclosed).congr
    intro x hx
    exact congrArg (fun M : Matrix (Fin (2+2)) (Fin (2+2)) ℝ => M i j)
      (ha x (hclosed hx))
  apply actual_weak_quadratic_sources_of_distributional_divergence_two A hAc
  intro j
  have hbase := actual_C2_cofactor_column_hasWeakDiv_zero_two isOpen_ball
    (hu.mono (ball_subset_closedBall.trans hclosed)) j
  apply actual_hasWeakDiv_zero_congr_on_two isOpen_ball
    (actual_hasWeakDiv_zero_const_smul_two hbase k)
  intro x hx
  ext i
  exact (congrArg (fun M : Matrix (Fin (2+2)) (Fin (2+2)) ℝ => M i j)
    (ha x (hclosed (ball_subset_closedBall hx)))).symm

end PowerConvexity
