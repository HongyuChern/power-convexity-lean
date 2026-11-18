import PowerConvexity.DependencyProbe

/-!
# The actual matrix equations in frozen manuscript §2.1

All matrix entries and all derivatives below are those of the same function `u`.
The inverse-Hessian contraction is `W q p`, with row index first.  In particular,
entrywise conjugation `map star` is not silently replaced by an adjoint.

The PDE identities use the fixed CHS commit.  Positivity is needed for the
inequality, but not for the differentiated determinant-one equalities.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder ContDiff Topology

namespace PowerConvexity

open CHS.Calculus CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's `u^{q̄p} ∂_{p q̄}`, applied entrywise. -/
noncomputable def matrixL (a b : ι → E) (u : E → ℝ)
    (G : E → Matrix ι ι ℂ) (x : E) : Matrix ι ι ℂ :=
  contract (complexHessian a b u x)⁻¹ (fun p q =>
    matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x)

theorem matrixL_entry (a b : ι → E) (u : E → ℝ)
    (G : E → Matrix ι ι ℂ) (x : E) (i j : ι) :
    matrixL a b u G x i j =
      ∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
        dz (a q) (-b q) (dz (a p) (b p) (fun y => G y i j)) x := by
  simp only [matrixL, contract, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, matrixDZ]

/-- TeX `Eq_1st_Derivative_2.1`, in any constant Wirtinger direction. -/
theorem cma_first_derivative {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (v w : E) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz v w (fun y => complexHessian a b u y p q) x) = 0 := by
  apply complexHessian_det_one_first (hu.contDiffAt (hU.mem_nhds hx)) a b
  exact Filter.Eventually.mono (hU.mem_nhds hx) hdet

/-- The first differentiated equation also holds at constant density.  This
form is needed after a general constant complex linear normalization. -/
theorem complexHessian_det_const_first {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (v w : E) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz v w (fun y => complexHessian a b u y p q) x) = 0 := by
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [← dz_det_field (complexHessian_differentiableAt hu a b) v w,
    dz_congr_nhds hdet v w, dz_const, mul_zero]

/-- The scalar linearization has the CHS real coefficient matrix, including
the factor 1/4 for the identity complex Hessian. -/
theorem real_linearization_pairing {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (a b : ι → E) (u : E → ℝ) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      complexHessian a b φ x p q).re =
      ∑ i, ∑ j, realLinearizationMatrix ((complexHessian a b u x)⁻¹) i j *
        realBlockHessian a b φ x i j :=
  realLinearizationMatrix_pairing hφ a b _

theorem real_linearization_posDef (a b : ι → E) (u : E → ℝ) (x : E)
    (hA : (complexHessian a b u x).PosDef) :
    (realLinearizationMatrix ((complexHessian a b u x)⁻¹)).PosDef :=
  realLinearizationMatrix_posDef hA.inv

/-- TeX `Matrix_A_Equation_AA`. -/
theorem matrix_A_equation_AA {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    matrixL a b u (complexHessian a b u) x =
      contract (complexHessian a b u x)⁻¹ (fun p q =>
        matrixDZ (a p) (b p) (complexHessian a b u) x *
          (complexHessian a b u x)⁻¹ *
            matrixDZ (a q) (-b q) (complexHessian a b u) x) := by
  exact (matrix_differential_identities hU hu a b hdet hx).1

/-- TeX `Matrix_A_Equation_BB`. -/
theorem matrix_A_equation_BB {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    matrixL a b u (complexHessian a b u) x =
      contract (complexHessian a b u x)⁻¹ (fun p q =>
        matrixDZ (a q) (-b q) (pureHessian a b u) x *
          ((complexHessian a b u x).map star)⁻¹ *
            matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x) := by
  exact (matrix_differential_identities hU hu a b hdet hx).2.1

/-- TeX `Matrix_B_Equation_AB`. -/
theorem matrix_B_equation_AB {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    matrixL a b u (pureHessian a b u) x =
      contract (complexHessian a b u x)⁻¹ (fun p q =>
        matrixDZ (a p) (b p) (complexHessian a b u) x *
          (complexHessian a b u x)⁻¹ *
            matrixDZ (a q) (-b q) (pureHessian a b u) x) := by
  exact (matrix_differential_identities hU hu a b hdet hx).2.2.1

/-- TeX `Matrix_B_Equation_BA`. -/
theorem matrix_B_equation_BA {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    matrixL a b u (pureHessian a b u) x =
      contract (complexHessian a b u x)⁻¹ (fun p q =>
        matrixDZ (a q) (-b q) (pureHessian a b u) x *
          ((complexHessian a b u x).map star)⁻¹ *
            matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x) := by
  exact (matrix_differential_identities hU hu a b hdet hx).2.2.2.1

/-- TeX `Eq_AbarBbarpq`: the inverse-return divergence. -/
theorem inverse_return_divergence {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    contract (complexHessian a b u x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q)
        (inverseDerivativeField a b (fun y => (complexHessian a b u y).map star)
          (fun y => (pureHessian a b u y).map star) p) x) = 0 := by
  exact (matrix_differential_identities hU hu a b hdet hx).2.2.2.2

/-- TeX `2_1_8`, fixing the placement of the conjugate inverse. -/
theorem compensatedHessian_eq (a b : ι → E) (u : E → ℝ) (p : ι) (x : E) :
    compensatedHessian a b u p x =
      matrixDZ (a p) (b p) (pureHessian a b u) x -
        pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
          matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x := rfl

/-- The equality in TeX `M_leq_0`. -/
theorem schur_linearization_eq {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    matrixL a b u (schurHessian a b u) x =
      -contract (complexHessian a b u x)⁻¹ (fun p q =>
        compensatedHessian a b u p x * ((complexHessian a b u x).map star)⁻¹ *
          (compensatedHessian a b u q x).conjTranspose) :=
  schurHessian_LM hU hu a b hdet hx

/-- The inequality in TeX `M_leq_0`, on the positive complex-Hessian branch. -/
theorem schur_linearization_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) :
    (-matrixL a b u (schurHessian a b u) x).PosSemidef :=
  schurHessian_LM_nonpos hU hu a b hdet hx hA

end PowerConvexity
