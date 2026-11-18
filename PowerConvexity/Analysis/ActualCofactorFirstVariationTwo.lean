import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo
import PowerConvexity.Analysis.ActualCofactorQuadraticResidualTwo
import PowerConvexity.Calculus.NormalizedCofactorLinearizedTwo
import PowerConvexity.Calculus.VariableDensityDirectionalGradientTwo

/-! # Actual first derivatives solve the same cofactor weak equation

The scalar load is exactly -c^{-1} D_v rho. No quotient by the density
survives after passing from the inverse Hessian to the cofactor equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_scaled_cofactor_first_variation_equation_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x) :
    ∀ v : E, ∀ x ∈ U,
      (∑ i, ∑ j, A.a x i j*euclideanHessian (fun y => fderiv ℝ u y v) x i j) =
        c⁻¹*fderiv ℝ rho x v := by
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  have hne (x : E) (hx : x ∈ U) : rho x ≠ 0 := by
    have hh := (Complex.pos_iff.mp (hpos x hx).det_pos).1
    rw [hdet x hx,Complex.ofReal_re] at hh
    exact hh.ne'
  intro v x hx
  let p : E → ℝ := fun y => fderiv ℝ u y v
  have hp : ContDiffOn ℝ 2 p U :=
    ((hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).clm_apply contDiffOn_const).of_le (by norm_num)
  have hflux := normalized_cofactor_flux_eq_density_linearized_two hU hu hp A hA hx (hpos x hx)
  rw [classicalDivergence_matMulE_gradient
    (fun i j => ((hreg i j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
      (hp.contDiffAt (hU.mem_nhds hx)) (hdiv x hx),hdet x hx,Complex.ofReal_re] at hflux
  have hL : linearizedCMAOperatorTwo realDirections imagDirections u p x =
      fderiv ℝ rho x v/rho x :=
    directionalDerivative_variable_density_two hU (hu.of_le (by norm_num)) hrho
      realDirections imagDirections hdet hne hx v
  change (∑ i, ∑ j, A.a x i j*euclideanHessian p x i j) =
    c⁻¹*rho x*linearizedCMAOperatorTwo realDirections imagDirections u p x at hflux
  rw [hL] at hflux
  exact hflux.trans (by field_simp [hne x hx])

theorem actual_scaled_cofactor_first_variation_weak_ball_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 2 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x)
    {x₀ : E} {r : ℝ} (hclosed : closedBall x₀ r ⊆ U) (v : E) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
      (fun x => -(c⁻¹*fderiv ℝ rho x v)) (fun x => fderiv ℝ u x v) := by
  have hsub : ball x₀ r ⊆ U := ball_subset_closedBall.trans hclosed
  have hp : ContDiffOn ℝ 2 (fun x => fderiv ℝ u x v) U :=
    ((hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).clm_apply contDiffOn_const).of_le (by norm_num)
  have hfC : ContDiffOn ℝ 1 (fun x => -(c⁻¹*fderiv ℝ rho x v)) U :=
    (contDiffOn_const.mul
      ((hrho.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)).neg
  have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall x₀ r) ball_subset_closedBall (hfC.continuousOn.mono hclosed)
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  apply actual_local_classical_scalar_weak_two hU hp hclosed
    (A.restrict hsub) (fun i j => (hreg i j).mono hsub)
    (fun x hx j => hdiv x (hsub hx) j) hf
  intro x hx
  simpa only [EllipticCoeff.restrict_a,neg_neg] using actual_scaled_cofactor_first_variation_equation_two hU hu
    (hrho.of_le (by norm_num)) hpos hdet A hA v x (hsub hx)

end PowerConvexity
