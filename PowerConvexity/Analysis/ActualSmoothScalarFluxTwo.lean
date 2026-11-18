import PowerConvexity.Analysis.ActualBoundaryVanishingH01Two
import PowerConvexity.Analysis.ActualQuadraticScalarSourceTwo

/-! # The actual scalar source and weak flux of a smooth boundary barrier -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_elliptic_coefficient_memLp_top_two {U : Set E}
    (A : EllipticCoeff (2+2) U) (i j : Fin (2+2)) :
    MemLp (fun x => A.a x i j) ∞ (volume.restrict U) := by
  apply memLp_top_of_bound (A.measurable_apply i j).aestronglyMeasurable A.Λ
  filter_upwards [A.mixed_bound] with x hx
  have hh := hx (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  simpa [EuclideanSpace.inner_single_left,matMulE_apply,Matrix.mulVec,
    dotProduct,EuclideanSpace.single,PiLp.single_apply,Real.norm_eq_abs] using hh

theorem actual_smooth_scalar_source_memLp_two
    {U : Set E} (hK : IsCompact (closure U)) (A : EllipticCoeff (2+2) U)
    {p : E → ℝ} (hp : ContDiff ℝ 2 p) :
    MemLp (quadraticScalarSourceTwo A.a p) 2 (volume.restrict U) := by
  have hH (i j : Fin (2+2)) : Continuous (fun x => euclideanHessian p x i j) := by
    have hh : Continuous (realHessian p) := continuous_iff_continuousAt.mpr (fun x =>
      ((hp.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt)
    exact (hh.clm_apply continuous_const).clm_apply continuous_const
  have hm (i j : Fin (2+2)) : MemLp (fun x => A.a x i j*euclideanHessian p x i j)
      2 (volume.restrict U) := by
    exact (continuous_memLp_two_of_subset_compact hK subset_closure (hH i j)).mul'
      (actual_elliptic_coefficient_memLp_top_two A i j)
  exact (memLp_finsetSum _ (fun i _ => memLp_finsetSum _ (fun j _ => hm i j))).neg

theorem actual_smooth_divergenceFree_scalar_weak_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {p : E → ℝ} (hp : ContDiff ℝ 2 p) :
    ActualScalarWeakEquationTwo A (quadraticScalarSourceTwo A.a p) p := by
  let F : E → E := fun y => matMulE (A.a y) (smoothGradField p y)
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun y => F y i) U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ 1
      (fun y => ∑ j, A.a y i j*fderiv ℝ p y (EuclideanSpace.single j 1)) x
    apply ContDiffAt.sum
    intro j _
    exact ((hA i j).contDiffAt (hU.mem_nhds hx)).mul
      ((hp.contDiffAt.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  apply actual_scalar_weak_of_classical_flux_two hU
    (hK.isBounded.subset subset_closure) A
    (actualClassicalBoundedWitnessTwo hU hK (hp.of_le (by norm_num)))
    (Filter.Eventually.of_forall (fun _ => rfl))
    (actual_smooth_scalar_source_memLp_two hK A hp) hF
  · intro x hx
    rfl
  · intro x hx
    rw [show F = fun y => matMulE (A.a y) (smoothGradField p y) by rfl,
      classicalDivergence_matMulE_gradient
        (fun i j => ((hA i j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
        hp.contDiffAt (hdiv x hx)]
    rfl

end PowerConvexity
