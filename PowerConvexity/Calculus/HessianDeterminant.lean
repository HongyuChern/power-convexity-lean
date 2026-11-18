import CHS.Calculus.BasisHessian
import PowerConvexity.Algebra.Congruence

/-! # Appendix A: the actual Hessian determinant identity in every dimension

The only additional condition needed to make the displayed inverse formula
meaningful is invertibility of the actual mixed complex Hessian. Positivity
is not assumed. The determinant factor is 4^(card i), including card i = 0.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hessianTransform_det_product :
    (hessianTransform (ι := ι)).det * (hessianTransform (ι := ι)).conjTranspose.det =
      (4 : ℂ)^Fintype.card ι := by
  have h := congrArg Matrix.det (hessianTransform_adjoint_mul (ι := ι))
  simp only [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_sum] at h
  rw [mul_comm] at h
  rw [h, pow_add, ← mul_pow]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_complexBlockHessian_det {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (4 : ℂ)^Fintype.card ι * (complexBlockHessian a b u x).det =
      ((realBlockHessian a b u x).det : ℂ) := by
  have h := congrArg Matrix.det (actual_block_congruence hu a b)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul] at h
  have hm : ((realBlockHessian a b u x).map Complex.ofReal).det =
      ((realBlockHessian a b u x).det : ℂ) :=
    (Complex.ofRealHom.map_det (realBlockHessian a b u x)).symm
  rw [hm, Fintype.card_sum, pow_add, inv_pow] at h
  rw [h]
  calc
    _ = ((4 : ℂ)^Fintype.card ι * ((4 : ℂ)^Fintype.card ι)⁻¹) *
        (((4 : ℂ)^Fintype.card ι)⁻¹ *
          ((hessianTransform (ι := ι)).det * (hessianTransform (ι := ι)).conjTranspose.det)) *
        ((realBlockHessian a b u x).det : ℂ) := by ring
    _ = _ := by rw [hessianTransform_det_product]; simp

/-- Frozen `lem:determinant_lemma` / `A1-1`, with the necessary invertibility
condition and actual derivatives. C2 at one point suffices; a quadratic
polynomial is a special case. -/
theorem actual_hessian_determinant_identity {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : IsUnit (complexHessian a b u x).det) :
    (1 - pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
      (pureHessian a b u x).map star * (complexHessian a b u x)⁻¹).det =
      ((realBlockHessian a b u x).det : ℂ) /
        ((4 : ℂ)^Fintype.card ι * (complexHessian a b u x).det^2) := by
  let A := complexHessian a b u x
  let B := pureHessian a b u x
  let S := A - B * (A.map star)⁻¹ * B.map star
  let K := 1 - B * (A.map star)⁻¹ * B.map star * A⁻¹
  have hbar : A.map star = A.transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  have hbarunit : IsUnit (A.map star).det := by
    rw [hbar, Matrix.det_transpose]
    exact hA
  let : Invertible (A.map star) := Matrix.invertibleOfIsUnitDet _ hbarunit
  have hblock : (complexBlockHessian a b u x).det = A.det * S.det := by
    change (Matrix.fromBlocks A B (B.map star) (A.map star)).det = A.det * S.det
    rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
    rw [hbar, Matrix.det_transpose]
    simp only [S, hbar]
  have hKA : K * A = S := by
    dsimp only [K,S]
    rw [sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA,
      Matrix.mul_one]
  have hd := congrArg Matrix.det hKA
  rw [Matrix.det_mul] at hd
  have h := actual_complexBlockHessian_det hu a b
  rw [hblock, ← hd] at h
  change K.det = _
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ (by norm_num : (4:ℂ) ≠ 0))
    (pow_ne_zero _ (isUnit_iff_ne_zero.mp hA)))).mpr
  change K.det * ((4:ℂ)^Fintype.card ι * A.det^2) = _
  calc
    _ = (4:ℂ)^Fintype.card ι * (A.det * (K.det * A.det)) := by ring
    _ = _ := h

/-- The determinant does not depend on grouping real coordinates as all x's
followed by all y's, or on any other simultaneous ordering of rows and columns. -/
theorem actual_hessian_determinant_identity_reindex
    {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι ⊕ ι)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : IsUnit (complexHessian a b u x).det) :
    (1 - pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
      (pureHessian a b u x).map star * (complexHessian a b u x)⁻¹).det =
      ((Matrix.of (fun i j : κ => realHessian u x
        (Sum.elim a b (e i)) (Sum.elim a b (e j)))).det : ℂ) /
        ((4 : ℂ)^Fintype.card ι * (complexHessian a b u x).det^2) := by
  have hd := Matrix.det_submatrix_equiv_self e (realBlockHessian a b u x)
  change (1 - pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
      (pureHessian a b u x).map star * (complexHessian a b u x)⁻¹).det =
    (((realBlockHessian a b u x).submatrix e e).det : ℂ) / _
  rw [hd]
  exact actual_hessian_determinant_identity hu a b hA

/-- Coordinate pair `(i,0)` is x_i and `(i,1)` is y_i. This is the
interleaved ordering D_(2i-1,2j-1), etc., in frozen Appendix A. -/
def interleavedCoordinateEquiv : (ι × Fin 2) ≃ ι ⊕ ι where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
  left_inv := by rintro ⟨i,j⟩; fin_cases j <;> simp
  right_inv := by rintro (i|i) <;> simp

theorem actual_hessian_determinant_identity_interleaved
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : IsUnit (complexHessian a b u x).det) :
    (1 - pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
      (pureHessian a b u x).map star * (complexHessian a b u x)⁻¹).det =
      ((Matrix.of (fun i j : ι × Fin 2 => realHessian u x
        (if i.2 = 0 then a i.1 else b i.1)
        (if j.2 = 0 then a j.1 else b j.1))).det : ℂ) /
        ((4 : ℂ)^Fintype.card ι * (complexHessian a b u x).det^2) := by
  convert actual_hessian_determinant_identity_reindex interleavedCoordinateEquiv hu a b hA using 1
  congr 3
  ext i j
  by_cases hi : i.2 = 0 <;> by_cases hj : j.2 = 0 <;>
    simp [interleavedCoordinateEquiv, hi, hj]

end PowerConvexity
