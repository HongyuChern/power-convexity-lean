import PowerConvexity.Calculus.VariableDensityCofactor
import PowerConvexity.Calculus.LinearizedDirichletC0Two
import CHS.Analysis.LinearizedFlux

/-! # Exact link from actual cofactor flux to the intended linearized CMA operator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Matrix
open scoped BigOperators ComplexOrder ContDiff
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem complexCofactor_contraction_eq_density_linearized_two
    {u : E → ℝ} {x : E}
    (hA : (complexHessian realDirections imagDirections u x).PosDef) (h : E → ℝ) :
    (∑ i, ∑ j, complexCofactorCoeff u x i j * euclideanHessian h x i j) =
      (complexHessian realDirections imagDirections u x).det.re *
        linearizedCMAOperatorTwo realDirections imagDirections u h x := by
  have hinv : (∑ i, ∑ j, complexLinearizedCoeff u x i j * euclideanHessian h x i j) =
      linearizedCMAOperatorTwo realDirections imagDirections u h x := by
    rw [← Equiv.sum_comp finSumFinEquiv]
    simp_rw [← Equiv.sum_comp finSumFinEquiv]
    simp only [complexLinearizedCoeff,Matrix.reindex_apply,Matrix.submatrix_apply,
      Equiv.symm_apply_apply,euclideanHessian,← blockDirection_eq_single,
      linearizedCMAOperatorTwo,complexHessianContraction,matrixHessianContraction,
      LinearMap.coe_mk,AddHom.coe_mk]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : realLinearizationMatrix (complexHessian realDirections imagDirections u x)⁻¹ j i =
        realLinearizationMatrix (complexHessian realDirections imagDirections u x)⁻¹ i j := by
      simpa only [star_trivial] using (realLinearizationMatrix_posDef hA.inv).isHermitian.apply i j
    rw [hs]
  rw [complexCofactorCoeff_eq_det_smul_inverse hA]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  rw [hinv]

theorem classical_cofactor_flux_eq_density_linearized_two
    {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hh : ContDiffAt ℝ 2 h x)
    (hA : (complexHessian realDirections imagDirections u x).PosDef) :
    classicalDivergence (fun y => matMulE (complexCofactorCoeff u y) (smoothGradField h y)) x =
      (complexHessian realDirections imagDirections u x).det.re *
        linearizedCMAOperatorTwo realDirections imagDirections u h x := by
  rw [classicalDivergence_matMulE_gradient
    (fun i j => (complexCofactorCoeff_contDiffAt hu i j).differentiableAt (by norm_num)) hh
    (complexCofactorCoeff_divergence (hu.of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit))]
  exact complexCofactor_contraction_eq_density_linearized_two hA h

end PowerConvexity
