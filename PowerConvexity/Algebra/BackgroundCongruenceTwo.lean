import PowerConvexity.Algebra.QuantitativeComplexNormalizationTwo

/-! # Exact forward and inverse background congruence.
These identities retain the fixed transpose/conjugation convention, positive
branch and determinant. They are used for the actual scaled functions later.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix
open scoped ComplexOrder
namespace PowerConvexity
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem normalized_background_sum_two {C G : W}
    (hG : G.transpose*C*G.map star = 1) (A : W) :
    1+G.transpose*A*G.map star = G.transpose*(C+A)*G.map star := by
  rw [Matrix.mul_add,Matrix.add_mul,hG]

theorem inverse_normalized_background_two {C G : W}
    (hGu : IsUnit G.det) (hG : G.transpose*C*G.map star = 1) :
    G⁻¹.transpose*(1 : W)*G⁻¹.map star = C := by
  have hl : G⁻¹.transpose*G.transpose = 1 := by
    rw [← Matrix.transpose_mul,Matrix.mul_nonsing_inv _ hGu,Matrix.transpose_one]
  have hr : G.map star*G⁻¹.map star = 1 := by
    change G.transpose.conjTranspose*G⁻¹.transpose.conjTranspose = 1
    rw [← Matrix.conjTranspose_mul,hl,Matrix.conjTranspose_one]
  calc
    _ = G⁻¹.transpose*(G.transpose*C*G.map star)*G⁻¹.map star := by rw [hG]
    _ = (G⁻¹.transpose*G.transpose)*C*(G.map star*G⁻¹.map star) := by noncomm_ring
    _ = C := by rw [hl,hr,Matrix.one_mul,Matrix.mul_one]

theorem inverse_normalized_background_sum_two {C G : W}
    (hGu : IsUnit G.det) (hG : G.transpose*C*G.map star = 1) (A : W) :
    C+G⁻¹.transpose*A*G⁻¹.map star = G⁻¹.transpose*(1+A)*G⁻¹.map star := by
  rw [Matrix.mul_add,Matrix.add_mul,inverse_normalized_background_two hGu hG]

theorem complex_congruence_det_one_two {G A : W}
    (hG : Complex.normSq G.det = 1) (hA : A.det = 1) :
    (G.transpose*A*G.map star).det = 1 := by
  change (G.transpose*A*G.transpose.conjTranspose).det = 1
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_conjTranspose,Matrix.det_transpose,
    hA,mul_one,Complex.star_def,Complex.mul_conj,hG,Complex.ofReal_one]

theorem complex_inverse_det_normSq_one_two {G : W}
    (hG : Complex.normSq G.det = 1) : Complex.normSq G⁻¹.det = 1 := by
  have hn := determinant_norm_eq_one_of_normSq_two hG
  rw [Complex.normSq_eq_norm_sq,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,norm_inv,hn,inv_one,one_pow]

theorem complex_congruence_posSemidef_two {G A : W} (hA : A.PosSemidef) :
    (G.transpose*A*G.map star).PosSemidef :=
  hA.mul_mul_conjTranspose_same G.transpose

theorem complex_congruence_posDef_two {G A : W} (hGu : IsUnit G.det) (hA : A.PosDef) :
    (G.transpose*A*G.map star).PosDef := by
  apply hA.mul_mul_conjTranspose_same
  rw [Matrix.vecMul_injective_iff_isUnit,Matrix.isUnit_iff_isUnit_det,Matrix.det_transpose]
  exact hGu

end PowerConvexity
