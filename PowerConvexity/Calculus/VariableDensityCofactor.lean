import PowerConvexity.Analysis.VariableDensityEllipticityFamily

/-! # Actual cofactor coefficients for a nonconstant complex Monge-Ampere density.
The divergence identity uses commuting third derivatives and an invertible
complex Hessian. No determinant-one hypothesis is inserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Matrix
open scoped BigOperators ComplexOrder ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis

theorem positive_complex_adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) : A.adjugate.PosDef := by
  have hadj : A.adjugate = A.det • A⁻¹ := by
    rw [Matrix.inv_def,smul_smul,Ring.mul_inverse_cancel _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),one_smul]
  rw [hadj]
  exact hA.inv.smul hA.det_pos

theorem complexHessian_cofactor_divergence
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : F → ℝ} {x : F} (hu : ContDiffAt ℝ 3 u x) (a b : ι → F)
    (hdet : IsUnit (complexHessian a b u x).det) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (complexHessian a b u y).adjugate j i) x) = 0 :=
  cofactor_divergence_of_commuting_rows a b (complexHessian_differentiableAt hu a b)
    (complexHessian_row_comm hu a b) hdet j

theorem complexHessian_realCofactor_divergence
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : F → ℝ} {x : F} (hu : ContDiffAt ℝ 3 u x) (a b : ι → F)
    (hdet : IsUnit (complexHessian a b u x).det) (j : ι ⊕ ι) :
    (∑ i, fderiv ℝ (fun y => realLinearizationMatrix
      (complexHessian a b u y).adjugate i j) x (Sum.elim a b i)) = 0 :=
  realLinearizationMatrix_divergence
    (field_adjugate_differentiableAt (complexHessian_differentiableAt hu a b))
    a b (complexHessian_cofactor_divergence hu a b hdet) j

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n+n)
local notation "W" => Matrix (Fin n) (Fin n) ℂ

def complexCofactorCoeff (u : E → ℝ) (x : E) : Matrix (Fin (n+n)) (Fin (n+n)) ℝ :=
  realLinearizedWeight (complexHessian realDirections imagDirections u x).adjugate

theorem complexCofactorCoeff_posDef {u : E → ℝ} {x : E}
    (hA : (complexHessian realDirections imagDirections u x).PosDef) :
    (complexCofactorCoeff u x).PosDef :=
  realLinearizedWeight_posDef (positive_complex_adjugate hA)

theorem complexCofactorCoeff_contDiffAt {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (i j : Fin (n+n)) :
    ContDiffAt ℝ 2 (fun y => complexCofactorCoeff u y i j) x :=
  realLinearizationMatrix_contDiffAt
    (field_adjugate_contDiffAt (complexHessian_contDiffAt_two hu realDirections imagDirections))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem complexCofactorCoeff_divergence {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x)
    (hdet : IsUnit (complexHessian realDirections imagDirections u x).det)
    (j : Fin (n+n)) :
    (∑ i, fderiv ℝ (fun y => complexCofactorCoeff u y i j) x
      (EuclideanSpace.single i 1)) = 0 := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexCofactorCoeff,realLinearizedWeight,Matrix.reindex_apply,
    Matrix.submatrix_apply,Equiv.symm_apply_apply,← blockDirection_eq_single]
  exact complexHessian_realCofactor_divergence hu realDirections imagDirections hdet
    (finSumFinEquiv.symm j)

theorem realLinearizedWeight_real_smul (r : ℝ) (A : W) :
    realLinearizedWeight (r • A) = r • realLinearizedWeight A := by
  have h : realLinearizationMatrix (r • A) = r • realLinearizationMatrix A := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [realLinearizationMatrix,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,
        Complex.mul_im,mul_assoc,mul_left_comm,mul_comm]
  ext i j
  simpa only [realLinearizedWeight,Matrix.reindex_apply,Matrix.submatrix_apply,
    Matrix.smul_apply] using congrArg (fun B => B (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) h

theorem complexCofactorCoeff_eq_det_smul_inverse {u : E → ℝ} {x : E}
    (hA : (complexHessian realDirections imagDirections u x).PosDef) :
    complexCofactorCoeff u x =
      (complexHessian realDirections imagDirections u x).det.re • complexLinearizedCoeff u x := by
  let A := complexHessian realDirections imagDirections u x
  have he : A.det = (A.det.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using (Complex.pos_iff.mp hA.det_pos).2.symm
  have hadj : A.adjugate = A.det.re • A⁻¹ := by
    have hh : A.adjugate = A.det • A⁻¹ := by
      rw [Matrix.inv_def,smul_smul,Ring.mul_inverse_cancel _
        ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),one_smul]
    rw [hh,he]
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_re]
  change realLinearizedWeight A.adjugate = A.det.re • realLinearizedWeight A⁻¹
  rw [hadj,realLinearizedWeight_real_smul]

end PowerConvexity
