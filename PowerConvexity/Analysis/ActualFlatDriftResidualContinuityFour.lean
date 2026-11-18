import PowerConvexity.Analysis.ActualFlatDriftResidualGrowthFour
import PowerConvexity.Analysis.ActualClassicalDriftFluxFour

/-! # Actual residual continuity and column divergence under physical dilation -/
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

theorem actual_quadratic_source_continuousOn_four {U : Set E} {A : E → Mat}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) U)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) : ContinuousOn (quadraticScalarSourceTwo A q) U := by
  have he : quadraticScalarSourceTwo A q =
      fun x => -(∑ i, ∑ j, A x i j*euclideanHessian q 0 i j) := by
    funext x
    simp only [quadraticScalarSourceTwo,euclideanHessian,quadratic_realHessian_from_jet_zero hq x]
  rw [he]
  apply ContinuousOn.neg
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (hA i j).mul continuousOn_const

theorem actual_quadratic_first_jet_continuous_four {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    Continuous (fun x => fderiv ℝ q x) := by
  have he : (fun x => fderiv ℝ q x) = fun x => fderiv ℝ q 0+realHessian q 0 x :=
    funext (quadratic_fderiv_from_jet_zero hq)
  rw [he]
  fun_prop

theorem actual_flat_drift_residual_continuous_four {N : E} {R a : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) {A : E → Mat} {b : E → E} {f q : E → ℝ}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) (actualFlatClosedUpperBallFour N 1))
    (hb : ContinuousOn b (actualFlatClosedUpperBallFour N 1))
    (hf : ContinuousOn f (actualFlatClosedUpperBallFour N 1)) (hq : IsQuadraticPolynomial q) :
    ContinuousOn (actualFlatDriftResidualSourceFour A b f q R a) (actualFlatClosedUpperBallFour N 1) := by
  have hd := (actual_quadratic_first_jet_continuous_four hq).continuousOn.clm_apply hb
  exact continuousOn_const.mul (((hf.sub (actual_quadratic_source_continuousOn_four hA hq)).add hd).comp
    (by fun_prop) (actual_flat_closed_unit_dilation_maps_four N hR hR1))

theorem actual_flat_dilation_column_divergence_four {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) (actualFlatUpperBallFour N 1))
    {b : E → E}
    (hdiv : ∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour A.a x=b x) :
    ∀ x ∈ actualFlatUpperBallFour N 1,
      actualCoefficientColumnDivergenceFour (actualFlatDilationCoeffFour hr hr1 A).a x = r • b (r • x) := by
  intro x hx
  have hm := actual_flat_unit_dilation_maps_four N hr hr1 hx
  ext j
  have hd (i : Fin (2+2)) : DifferentiableAt ℝ (fun y => A.a y i j) (r • x) :=
    ((hA i j).contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds hm)).differentiableAt
      (by norm_num)
  change (∑ i, fderiv ℝ (fun y => A.a (r • y) i j) x (EuclideanSpace.single i 1))=r*(b (r • x) j)
  simp_rw [actual_scalar_comp_fderiv_at_four r (hd _)]
  rw [← Finset.mul_sum]
  have hh := congrArg (fun v : E => v j) (hdiv _ hm)
  change (∑ i, fderiv ℝ (fun y => A.a y i j) (r • x) (EuclideanSpace.single i 1))=b (r • x) j at hh
  rw [hh]

end PowerConvexity
