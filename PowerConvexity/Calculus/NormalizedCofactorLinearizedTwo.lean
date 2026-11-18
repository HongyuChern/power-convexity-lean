import PowerConvexity.Calculus.CofactorLinearizedDirichletTwo
import CHS.Analysis.DirectionalSupersolutions

/-! # Exact normalization and sign of the actual scalar linearized problem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Matrix
open scoped BigOperators ComplexOrder ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem normalized_cofactor_flux_eq_density_linearized_two
    {U : Set E} (hU : IsOpen U) {u h : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hh : ContDiffOn ℝ 2 h U)
    {c : ℝ} (B : EllipticCoeff (2+2) U)
    (hB : ∀ y ∈ U, B.a y = c⁻¹ • complexCofactorCoeff u y)
    {x : E} (hx : x ∈ U)
    (hA : (complexHessian realDirections imagDirections u x).PosDef) :
    classicalDivergence (fun y => matMulE (B.a y) (smoothGradField h y)) x =
      c⁻¹ * (complexHessian realDirections imagDirections u x).det.re *
        linearizedCMAOperatorTwo realDirections imagDirections u h x := by
  have heq : (fun y => matMulE (B.a y) (smoothGradField h y)) =ᶠ[𝓝 x]
      (fun y => c⁻¹ • matMulE (complexCofactorCoeff u y) (smoothGradField h y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hB y hy,matMulE_smul_matrix]
  have hdiv : classicalDivergence (fun y => matMulE (B.a y) (smoothGradField h y)) x =
      classicalDivergence
        (fun y => c⁻¹ • matMulE (complexCofactorCoeff u y) (smoothGradField h y)) x := by
    unfold classicalDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hi : (fun y => matMulE (B.a y) (smoothGradField h y) i) =ᶠ[𝓝 x]
        (fun y => (c⁻¹ • matMulE (complexCofactorCoeff u y) (smoothGradField h y)) i) :=
      heq.mono (fun y hy => congrArg (fun v : E => v i) hy)
    rw [hi.fderiv_eq]
  rw [hdiv,classicalDivergence_const_smul,
    classical_cofactor_flux_eq_density_linearized_two
      (hu.contDiffAt (hU.mem_nhds hx)) (hh.contDiffAt (hU.mem_nhds hx)) hA]
  ring

theorem normalized_cofactor_scalar_equation_iff_linearized_two
    {U : Set E} (hU : IsOpen U) {u h : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hh : ContDiffOn ℝ 2 h U)
    {c : ℝ} (hc : 0 < c) (B : EllipticCoeff (2+2) U)
    (hB : ∀ y ∈ U, B.a y = c⁻¹ • complexCofactorCoeff u y)
    {x : E} (hx : x ∈ U)
    (hA : (complexHessian realDirections imagDirections u x).PosDef)
    (g : E → ℝ) :
    (-classicalDivergence (fun y => matMulE (B.a y) (smoothGradField h y)) x =
      -(c⁻¹ * (complexHessian realDirections imagDirections u x).det.re * g x)) ↔
      linearizedCMAOperatorTwo realDirections imagDirections u h x = g x := by
  rw [normalized_cofactor_flux_eq_density_linearized_two hU hu hh B hB hx hA,
    neg_inj]
  exact ⟨mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hc.ne')
    (Complex.pos_iff.mp hA.det_pos).1.ne'),fun he => congrArg _ he⟩

end PowerConvexity
