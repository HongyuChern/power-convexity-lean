import PowerConvexity.Algebra.SchurSpectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Ordered real characteristic roots in dimension two

The definitions use the actual trace and determinant.  The characteristic
factorization of the Hermitian representative proves that these formulas
are the ordered real eigenvalues of the Schur quotient.
-/

set_option autoImplicit false
open scoped ComplexOrder

namespace PowerConvexity

noncomputable def eigenDiscriminantTwo (K : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  K.trace.re ^ 2 - 4 * K.det.re

noncomputable def lowerEigenvalueTwo (K : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (K.trace.re - Real.sqrt (eigenDiscriminantTwo K)) / 2

noncomputable def upperEigenvalueTwo (K : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (K.trace.re + Real.sqrt (eigenDiscriminantTwo K)) / 2

theorem trace_det_of_charpoly_real_pair (K : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℝ)
    (h : K.charpoly = (Polynomial.X - Polynomial.C (r : ℂ)) *
      (Polynomial.X - Polynomial.C (s : ℂ))) :
    K.trace = ((r + s : ℝ) : ℂ) ∧ K.det = ((r * s : ℝ) : ℂ) := by
  rw [Matrix.charpoly_fin_two] at h
  have he : (Polynomial.X - Polynomial.C (r : ℂ)) *
      (Polynomial.X - Polynomial.C (s : ℂ)) =
      Polynomial.X ^ 2 - Polynomial.C ((r + s : ℝ) : ℂ) * Polynomial.X +
        Polynomial.C ((r * s : ℝ) : ℂ) := by
    push_cast
    simp only [map_add, map_mul]
    ring
  rw [he] at h
  have h0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
  have h1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
  simp at h0 h1
  constructor
  · push_cast
    linear_combination -h1
  · simpa only [Complex.ofReal_mul] using h0

theorem eigenDiscriminantTwo_of_real_pair (K : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℝ)
    (h : K.charpoly = (Polynomial.X - Polynomial.C (r : ℂ)) *
      (Polynomial.X - Polynomial.C (s : ℂ))) :
    eigenDiscriminantTwo K = (r - s)^2 := by
  obtain ⟨ht, hd⟩ := trace_det_of_charpoly_real_pair K r s h
  simp only [eigenDiscriminantTwo, ht, hd, Complex.ofReal_re]
  ring

theorem lowerEigenvalueTwo_of_real_pair (K : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℝ)
    (h : K.charpoly = (Polynomial.X - Polynomial.C (r : ℂ)) *
      (Polynomial.X - Polynomial.C (s : ℂ))) :
    lowerEigenvalueTwo K = min r s := by
  obtain ⟨ht, _⟩ := trace_det_of_charpoly_real_pair K r s h
  rw [lowerEigenvalueTwo, eigenDiscriminantTwo_of_real_pair K r s h,
    Real.sqrt_sq_eq_abs, ht, Complex.ofReal_re]
  rcases le_total r s with hrs | hsr
  · rw [min_eq_left hrs, abs_of_nonpos (sub_nonpos.mpr hrs)]
    ring
  · rw [min_eq_right hsr, abs_of_nonneg (sub_nonneg.mpr hsr)]
    ring

theorem upperEigenvalueTwo_of_real_pair (K : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℝ)
    (h : K.charpoly = (Polynomial.X - Polynomial.C (r : ℂ)) *
      (Polynomial.X - Polynomial.C (s : ℂ))) :
    upperEigenvalueTwo K = max r s := by
  obtain ⟨ht, _⟩ := trace_det_of_charpoly_real_pair K r s h
  rw [upperEigenvalueTwo, eigenDiscriminantTwo_of_real_pair K r s h,
    Real.sqrt_sq_eq_abs, ht, Complex.ofReal_re]
  rcases le_total r s with hrs | hsr
  · rw [max_eq_right hrs, abs_of_nonpos (sub_nonpos.mpr hrs)]
    ring
  · rw [max_eq_left hsr, abs_of_nonneg (sub_nonneg.mpr hsr)]
    ring

theorem eigenvalueTwo_gap (K : Matrix (Fin 2) (Fin 2) ℂ) :
    upperEigenvalueTwo K - lowerEigenvalueTwo K =
      Real.sqrt (eigenDiscriminantTwo K) := by
  unfold upperEigenvalueTwo lowerEigenvalueTwo
  ring

theorem eigenvalueTwo_strict_gap_iff (K : Matrix (Fin 2) (Fin 2) ℂ) :
    lowerEigenvalueTwo K < upperEigenvalueTwo K ↔ 0 < eigenDiscriminantTwo K := by
  rw [← sub_pos, eigenvalueTwo_gap, Real.sqrt_pos]

theorem lowerEigenvalueTwo_is_min_root (K : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℝ)
    (h : K.charpoly = (Polynomial.X - Polynomial.C (r : ℂ)) *
      (Polynomial.X - Polynomial.C (s : ℂ))) :
    K.charpoly.IsRoot (lowerEigenvalueTwo K : ℂ) ∧
      ∀ t : ℝ, K.charpoly.IsRoot (t : ℂ) → lowerEigenvalueTwo K ≤ t := by
  rw [lowerEigenvalueTwo_of_real_pair K r s h]
  constructor
  · rcases le_total r s with hrs | hsr
    · simp [min_eq_left hrs, h, Polynomial.IsRoot]
    · simp [min_eq_right hsr, h, Polynomial.IsRoot]
  · intro t ht
    have he : ((t : ℂ) - (r : ℂ)) * ((t : ℂ) - (s : ℂ)) = 0 := by
      simpa only [h, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] using ht
    rcases mul_eq_zero.mp he with hr | hs
    · have heq : t = r := Complex.ofReal_injective (sub_eq_zero.mp hr)
      rw [heq]
      exact min_le_left _ _
    · have heq : t = s := Complex.ofReal_injective (sub_eq_zero.mp hs)
      rw [heq]
      exact min_le_right _ _

theorem schur_quotient_real_pair {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    let hH := schurHermitianRepresentative_isHermitian hA.isHermitian hB
    (matrixSchur A B * A⁻¹).charpoly =
      (Polynomial.X - Polynomial.C (hH.eigenvalues 0 : ℂ)) *
      (Polynomial.X - Polynomial.C (hH.eigenvalues 1 : ℂ)) := by
  simpa only [Fin.prod_univ_two] using schur_quotient_charpoly_real_factors hA hB

theorem schur_quotient_discriminant_nonneg {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    0 ≤ eigenDiscriminantTwo (matrixSchur A B * A⁻¹) := by
  rw [eigenDiscriminantTwo_of_real_pair _ _ _ (schur_quotient_real_pair hA hB)]
  exact sq_nonneg _

theorem schur_quotient_lower_is_min_root {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B * A⁻¹).charpoly.IsRoot
        (lowerEigenvalueTwo (matrixSchur A B * A⁻¹) : ℂ) ∧
      ∀ t : ℝ, (matrixSchur A B * A⁻¹).charpoly.IsRoot (t : ℂ) →
        lowerEigenvalueTwo (matrixSchur A B * A⁻¹) ≤ t :=
  lowerEigenvalueTwo_is_min_root _ _ _ (schur_quotient_real_pair hA hB)

theorem schur_posSemidef_iff_lower_nonneg {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B).PosSemidef ↔ 0 ≤ lowerEigenvalueTwo (matrixSchur A B * A⁻¹) := by
  let H := schurHermitianRepresentative A B
  have hH : H.IsHermitian := schurHermitianRepresentative_isHermitian hA.isHermitian hB
  have hQ : IsUnit (whiteningMatrix A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (whiteningMatrix_normalizes hA).1
  have hc : H.PosSemidef ↔ (matrixSchur A B).PosSemidef :=
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff (x := matrixSchur A B) hQ
  rw [← hc, hH.posSemidef_iff_eigenvalues_nonneg,
    lowerEigenvalueTwo_of_real_pair _ _ _ (schur_quotient_real_pair hA hB), le_min_iff]
  change (∀ i : Fin 2, 0 ≤ hH.eigenvalues i) ↔
    0 ≤ hH.eigenvalues 0 ∧ 0 ≤ hH.eigenvalues 1
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem schur_posDef_iff_lower_pos {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B).PosDef ↔ 0 < lowerEigenvalueTwo (matrixSchur A B * A⁻¹) := by
  let H := schurHermitianRepresentative A B
  have hH : H.IsHermitian := schurHermitianRepresentative_isHermitian hA.isHermitian hB
  have hQ : IsUnit (whiteningMatrix A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (whiteningMatrix_normalizes hA).1
  have hc : H.PosDef ↔ (matrixSchur A B).PosDef :=
    Matrix.IsUnit.posDef_star_right_conjugate_iff (x := matrixSchur A B) hQ
  rw [← hc, hH.posDef_iff_eigenvalues_pos,
    lowerEigenvalueTwo_of_real_pair _ _ _ (schur_quotient_real_pair hA hB), lt_min_iff]
  change (∀ i : Fin 2, 0 < hH.eigenvalues i) ↔
    0 < hH.eigenvalues 0 ∧ 0 < hH.eigenvalues 1
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem matrixSchur_one_real_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) :
    matrixSchur 1 (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => ((1 - d i ^ 2 : ℝ) : ℂ)) := by
  have hI : (1 : Matrix ι ι ℂ).map star = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hD : (Matrix.diagonal (fun i => (d i : ℂ))).map star =
      Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  unfold matrixSchur
  rw [hI, inv_one, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.one_apply, pow_two]
  · simp [Matrix.one_apply, Matrix.diagonal_apply, h]

theorem real_diagonal_charpoly_pair (d : Fin 2 → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).charpoly =
      (Polynomial.X - Polynomial.C (d 0 : ℂ)) *
        (Polynomial.X - Polynomial.C (d 1 : ℂ)) := by
  rw [Matrix.charpoly_diagonal, Fin.prod_univ_two]

theorem lowerEigenvalueTwo_real_diagonal (d : Fin 2 → ℝ) :
    lowerEigenvalueTwo (Matrix.diagonal (fun i => (d i : ℂ))) = min (d 0) (d 1) :=
  lowerEigenvalueTwo_of_real_pair _ _ _ (real_diagonal_charpoly_pair d)

theorem eigenDiscriminantTwo_real_diagonal (d : Fin 2 → ℝ) :
    eigenDiscriminantTwo (Matrix.diagonal (fun i => (d i : ℂ))) = (d 0 - d 1)^2 :=
  eigenDiscriminantTwo_of_real_pair _ _ _ (real_diagonal_charpoly_pair d)

end PowerConvexity
