import PowerConvexity.Algebra.DimensionTwo
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The inverse weight in normalized coordinates

When the modified mixed Hessian is the identity, the original mixed Hessian
is `I - h g g*`.  Positivity supplies the strictly positive denominator in
the Sherman--Morrison formula.  The resulting inverse really is `I + r r*`.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace PowerConvexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def vectorNormSq (g : ι → ℂ) : ℝ := ∑ i, Complex.normSq (g i)

theorem star_dot_self_eq_vectorNormSq (g : ι → ℂ) :
    star g ⬝ᵥ g = (vectorNormSq g : ℂ) := by
  simp only [dotProduct, vectorNormSq, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self, Pi.star_apply]
  rfl

theorem outer_self_square (g : ι → ℂ) :
    Matrix.vecMulVec g (star g) * Matrix.vecMulVec g (star g) =
      (vectorNormSq g : ℂ) • Matrix.vecMulVec g (star g) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, star_dot_self_eq_vectorNormSq,
    Matrix.vecMulVec_smul]

theorem det_one_sub_outer (h : ℝ) (g : ι → ℂ) :
    (1 - (h : ℂ) • Matrix.vecMulVec g (star g)).det =
      ((1 - h * vectorNormSq g : ℝ) : ℂ) := by
  have hd := Matrix.det_one_add_replicateCol_mul_replicateRow
    (ι := Unit) ((-h : ℂ) • g) (star g)
  have he : Matrix.replicateCol Unit ((-h : ℂ) • g) *
      Matrix.replicateRow Unit (star g) = (-h : ℂ) • Matrix.vecMulVec g (star g) := by
    rw [← Matrix.smul_vecMulVec]
    exact (Matrix.vecMulVec_eq Unit _ _).symm
  rw [he, dotProduct_smul, star_dot_self_eq_vectorNormSq] at hd
  simpa only [neg_smul, sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_mul, neg_mul, smul_eq_mul] using hd

theorem rankOne_denominator_pos (h : ℝ) (g : ι → ℂ)
    (hA : (1 - (h : ℂ) • Matrix.vecMulVec g (star g)).PosDef) :
    0 < 1 - h * vectorNormSq g := by
  have hd := hA.det_pos
  rw [det_one_sub_outer] at hd
  exact_mod_cast hd

theorem inverse_one_sub_outer (h : ℝ) (g : ι → ℂ)
    (hk : 1 - h * vectorNormSq g ≠ 0) :
    (1 - (h : ℂ) • Matrix.vecMulVec g (star g))⁻¹ =
      1 + ((h / (1 - h * vectorNormSq g) : ℝ) : ℂ) •
        Matrix.vecMulVec g (star g) := by
  have hkc : ((1 - h * vectorNormSq g : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hk
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, outer_self_square]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]
  push_cast at hkc
  field_simp
  <;> ring

noncomputable def normalizedRankOneVector (h : ℝ) (g : ι → ℂ) : ι → ℂ :=
  (Real.sqrt (h / (1 - h * vectorNormSq g)) : ℂ) • g

theorem inverse_one_sub_outer_eq_rankOne (h : ℝ) (hh : 0 ≤ h) (g : ι → ℂ)
    (hA : (1 - (h : ℂ) • Matrix.vecMulVec g (star g)).PosDef) :
    (1 - (h : ℂ) • Matrix.vecMulVec g (star g))⁻¹ =
      1 + Matrix.vecMulVec (normalizedRankOneVector h g)
        (star (normalizedRankOneVector h g)) := by
  have hk := rankOne_denominator_pos h g hA
  rw [inverse_one_sub_outer h g (ne_of_gt hk)]
  congr 1
  ext i j
  simp only [normalizedRankOneVector, Matrix.vecMulVec_apply, Pi.smul_apply,
    Pi.star_apply, smul_eq_mul, star_mul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_apply]
  have hs : (Real.sqrt (h / (1 - h * vectorNormSq g)) : ℂ) ^ 2 =
      ((h / (1 - h * vectorNormSq g) : ℝ) : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (div_nonneg hh hk.le)
  linear_combination -(g i * (starRingEnd ℂ) (g j)) * hs

end PowerConvexity
