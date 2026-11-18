import PowerConvexity.Calculus.CofactorLinearizedDirichletTwo
import CHS.Analysis.LocalDirectionalSupersolutions

/-! # Actual local cofactor supersolutions for a variable determinant.
No constant-density hypothesis is used. The conclusion is the vendored
all-H01-test definition, obtained from the actual classical flux.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped BigOperators ComplexOrder ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem scaled_cofactor_local_supersolution_on_ball_two
    {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hv : ContDiffOn ℝ 2 v U)
    (hA : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (2+2) U)
    (hB : ∀ x ∈ U, B.1.a x = c⁻¹ • complexCofactorCoeff u x)
    (hlin : ∀ x ∈ U, linearizedCMAOperatorTwo realDirections imagDirections u v x ≤ 0)
    {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U) :
    IsSupersolution (B.restrict
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed)).1 v := by
  let F (y : E) := c⁻¹ • matMulE (complexCofactorCoeff u y) (smoothGradField v y)
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun y => F y i) U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ 1 (fun y => c⁻¹ *
      ∑ j, complexCofactorCoeff u y i j * fderiv ℝ v y (EuclideanSpace.single j 1)) x
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro j _
    exact ((complexCofactorCoeff_contDiffAt (hu.contDiffAt (hU.mem_nhds hx)) i j).of_le
      (by norm_num)).mul
      (((hv.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have hsub : ball x₀ r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed
  apply supersolution_of_local_classical_flux hU hr hrR hclosed _ (hv.of_le (by norm_num)) hF
  · intro x hx
    change matMulE (B.1.a x) (smoothGradField v x) = _
    rw [hB x (hsub hx),matMulE_smul_matrix]
  · intro x hx
    have hxU := hsub hx
    rw [show F = fun y => c⁻¹ • matMulE (complexCofactorCoeff u y)
      (smoothGradField v y) by rfl,classicalDivergence_const_smul,
      classical_cofactor_flux_eq_density_linearized_two
        (hu.contDiffAt (hU.mem_nhds hxU)) (hv.contDiffAt (hU.mem_nhds hxU)) (hA x hxU)]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le)
      (mul_nonpos_of_nonneg_of_nonpos (Complex.pos_iff.mp (hA x hxU).det_pos).1.le (hlin x hxU))

end PowerConvexity
