import PowerConvexity.Analysis.ActualScalarClassicalFluxTwo
import PowerConvexity.Calculus.ClosureJetSobolev
import PowerConvexity.Calculus.QuadraticJointJets
import CHS.Analysis.LinearizedFlux

/-! # Actual scalar source of a quadratic for divergence-free coefficients.
The polynomial Sobolev witness, source L2 membership, classical flux and
full H01 identity are all proved. The residual source keeps its exact sign.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def quadraticScalarSourceTwo (a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
    (q : E → ℝ) : E → ℝ :=
  fun x => -(∑ i, ∑ j, a x i j*euclideanHessian q x i j)

theorem actual_quadratic_source_memLp_two
    {c : E} {r : ℝ} {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) (closedBall c r))
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    MemLp (quadraticScalarSourceTwo a q) 2 (volume.restrict (ball c r)) := by
  apply continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall c r) ball_subset_closedBall
  have he : quadraticScalarSourceTwo a q =
      fun x => -(∑ i, ∑ j, a x i j*euclideanHessian q 0 i j) := by
    funext x
    simp only [quadraticScalarSourceTwo,euclideanHessian,
      quadratic_realHessian_from_jet_zero hq x]
  rw [he]
  apply ContinuousOn.neg
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (ha i j).mul continuousOn_const

theorem actual_divergenceFree_quadratic_source_two
    {c : E} {r : ℝ} {V : Set E} (hV : IsOpen V) (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V)
    (hdiv : ∀ x ∈ ball c r, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    ActualScalarWeakEquationTwo A (quadraticScalarSourceTwo A.a q) q := by
  have hqC := IsQuadraticPolynomial_contDiff hq 2
  let F : E → E := fun y => matMulE (A.a y) (smoothGradField q y)
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun y => F y i) (ball c r) := by
    intro x hx
    have hxV := hclosed (ball_subset_closedBall hx)
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ 1
      (fun y => ∑ j, A.a y i j*fderiv ℝ q y (EuclideanSpace.single j 1)) x
    apply ContDiffAt.sum
    intro j _
    exact ((hA i j).contDiffAt (hV.mem_nhds hxV)).mul
      ((hqC.contDiffAt.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  apply actual_scalar_classical_flux_ball_two A (hqC.of_le (by norm_num))
    (actual_quadratic_source_memLp_two
      (fun i j => (hA i j).continuousOn.mono hclosed) hq) hF
  · intro x hx
    rfl
  · intro x hx
    have hxV := hclosed (ball_subset_closedBall hx)
    rw [show F = fun y => matMulE (A.a y) (smoothGradField q y) by rfl,
      classicalDivergence_matMulE_gradient
        (fun i j => ((hA i j).contDiffAt (hV.mem_nhds hxV)).differentiableAt (by norm_num))
        hqC.contDiffAt (hdiv x hx)]
    rfl

theorem actual_divergenceFree_quadratic_residual_two
    {c : E} {r : ℝ} {V : Set E} (hV : IsOpen V) (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V)
    (hdiv : ∀ x ∈ ball c r, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {u f q : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball c r)))
    (hu : ActualScalarWeakEquationTwo A f u) (hq : IsQuadraticPolynomial q) :
    ActualScalarWeakEquationTwo A
      (fun x => f x+∑ i, ∑ j, A.a x i j*euclideanHessian q x i j)
      (fun x => u x-q x) := by
  have hqweak := actual_divergenceFree_quadratic_source_two hV hclosed A hA hdiv hq
  have hqf := actual_quadratic_source_memLp_two
    (fun i j => (hA i j).continuousOn.mono hclosed) hq
  have hr := actual_scalar_weak_sub_two isOpen_ball hf hqf hu hqweak
  simpa only [quadraticScalarSourceTwo,sub_neg_eq_add] using hr

end PowerConvexity
