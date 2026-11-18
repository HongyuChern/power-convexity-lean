import PowerConvexity.Calculus.VariableDensityCofactor
import CHS.Calculus.PotentialNegation

/-! # In dimension two the actual cofactor divergence needs no determinant hypothesis

The adjugate is linear, so the identity is exactly commutation of the third
derivatives.  In particular it applies to arbitrary smooth test functions,
whose complex Hessians need not be positive or invertible.  This is used to
transfer the identity to C2 potentials by distributional integration by parts.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Matrix
open scoped ContDiff BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi

theorem complexHessian_adjugate_divergence_unconditional_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} {x : F} (hu : ContDiffAt ℝ 3 u x)
    (a b : Fin 2 → F) (j : Fin 2) :
    (∑ i : Fin 2, dz (a i) (b i) (fun y => (complexHessian a b u y).adjugate j i) x)=0 := by
  fin_cases j
  · simp only [Fin.sum_univ_two,Matrix.adjugate_fin_two]
    change dz (a 0) (b 0) (fun y => complexHessian a b u y 1 1) x+
      dz (a 1) (b 1) (fun y => -complexHessian a b u y 0 1) x=0
    rw [dz_neg_fun,complexHessian_row_comm hu a b 0 1 1]
    ring
  · simp only [Fin.sum_univ_two,Matrix.adjugate_fin_two]
    change dz (a 0) (b 0) (fun y => -complexHessian a b u y 1 0) x+
      dz (a 1) (b 1) (fun y => complexHessian a b u y 0 0) x=0
    rw [dz_neg_fun,complexHessian_row_comm hu a b 1 0 0]
    ring

theorem complexHessian_realCofactor_divergence_unconditional_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} {x : F} (hu : ContDiffAt ℝ 3 u x)
    (a b : Fin 2 → F) (j : Fin 2 ⊕ Fin 2) :
    (∑ i, fderiv ℝ (fun y => realLinearizationMatrix
      (complexHessian a b u y).adjugate i j) x (Sum.elim a b i))=0 :=
  realLinearizationMatrix_divergence
    (field_adjugate_differentiableAt (complexHessian_differentiableAt hu a b))
    a b (complexHessian_adjugate_divergence_unconditional_two hu a b) j

theorem complexCofactorCoeff_divergence_unconditional_two
    {u : AmbientSpace (2+2) → ℝ} {x : AmbientSpace (2+2)}
    (hu : ContDiffAt ℝ 3 u x) (j : Fin (2+2)) :
    (∑ i, fderiv ℝ (fun y => complexCofactorCoeff u y i j) x
      (EuclideanSpace.single i 1))=0 := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexCofactorCoeff,realLinearizedWeight,Matrix.reindex_apply,
    Matrix.submatrix_apply,Equiv.symm_apply_apply,← blockDirection_eq_single]
  exact complexHessian_realCofactor_divergence_unconditional_two hu
    realDirections imagDirections (finSumFinEquiv.symm j)

end PowerConvexity
