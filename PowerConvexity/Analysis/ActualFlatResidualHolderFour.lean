import PowerConvexity.Analysis.ActualFlatResidualEquationFour

/-! # Quantitative source bounds for the same actual boundary residual -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_matrix_entry_le_operator_norm_four (C : Mat) (i j : Fin (2+2)) :
    |C i j| ≤ ‖actualMatrixOperatorTwo C‖ := by
  have hh := (PiLp.norm_apply_le (actualMatrixOperatorTwo C (EuclideanSpace.single j 1)) i).trans
    ((actualMatrixOperatorTwo C).le_opNorm (EuclideanSpace.single j 1))
  simpa [actual_matrix_operator_apply_two,matMulE_apply,Matrix.mulVec,dotProduct,
    EuclideanSpace.single_apply,EuclideanSpace.norm_single] using hh

theorem actual_matrix_difference_entry_bound_four (C D : Mat) (i j : Fin (2+2)) :
    |C i j-D i j| ≤ ‖actualMatrixOperatorTwo C-actualMatrixOperatorTwo D‖ := by
  simpa only [Matrix.sub_apply,map_sub] using actual_matrix_entry_le_operator_norm_four (C-D) i j

theorem actual_quadratic_source_difference_bound_four {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) {M : ℝ} (hM : 0 ≤ M)
    (hH : ‖realHessian q 0‖ ≤ M) (C D : Mat) (x y : E) :
    |quadraticScalarSourceTwo (fun _ => C) q x-
      quadraticScalarSourceTwo (fun _ => D) q y| ≤
      16*‖actualMatrixOperatorTwo C-actualMatrixOperatorTwo D‖*M := by
  have he : quadraticScalarSourceTwo (fun _ => C) q x-
      quadraticScalarSourceTwo (fun _ => D) q y =
      -(∑ i, ∑ j, (C i j-D i j)*euclideanHessian q 0 i j) := by
    simp only [quadraticScalarSourceTwo,euclideanHessian,
      quadratic_realHessian_from_jet_zero hq,sub_mul,Finset.sum_sub_distrib]
    ring
  have hentry (i j : Fin (2+2)) : |euclideanHessian q 0 i j| ≤ M := by
    have hh := (realHessian q 0).le_opNorm₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    have hh' : |euclideanHessian q 0 i j| ≤ ‖realHessian q 0‖ := by
      simpa only [euclideanHessian,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using hh
    exact hh'.trans hH
  rw [he,abs_neg]
  calc
    _ ≤ ∑ i, |∑ j, (C i j-D i j)*euclideanHessian q 0 i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (2+2), ∑ _j : Fin (2+2),
        ‖actualMatrixOperatorTwo C-actualMatrixOperatorTwo D‖*M := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (actual_matrix_difference_entry_bound_four C D i j) (hentry i j)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem actual_quadratic_source_holder_four {U : Set E} {A : E → Mat} {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) {K M alpha : ℝ} (hM : 0 ≤ M)
    (hH : ‖realHessian q 0‖ ≤ M)
    (hA : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ U, ∀ y ∈ U,
      |quadraticScalarSourceTwo A q x-quadraticScalarSourceTwo A q y| ≤
      (16*K*M)*‖x-y‖^alpha := by
  intro x hx y hy
  exact (actual_quadratic_source_difference_bound_four hq hM hH (A x) (A y) x y).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA x hx y hy)
      (by norm_num : (0 : ℝ) ≤ 16)) hM).trans_eq (by ring))

theorem actual_flat_residual_source_holder_four {N : E} {A : E → Mat} {f q : E → ℝ}
    (hq : IsQuadraticPolynomial q) {R b Ka Kf M alpha : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hb : 0 < b) (hM : 0 ≤ M)
    (hH : ‖realHessian q 0‖ ≤ M)
    (hA : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ Ka*‖x-y‖^alpha)
    (hf : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      |f x-f y| ≤ Kf*‖x-y‖^alpha) :
    ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      |actualFlatResidualSourceFour A f q R b x-actualFlatResidualSourceFour A f q R b y| ≤
      (b⁻¹*R^alpha*(Kf+16*Ka*M))*‖x-y‖^alpha := by
  intro x hx y hy
  have hmx := actual_flat_unit_dilation_maps_four N hR hR1 hx
  have hmy := actual_flat_unit_dilation_maps_four N hR hR1 hy
  have hqf := actual_quadratic_source_holder_four hq hM hH hA _ hmx _ hmy
  have hh : |(f (R • x)-quadraticScalarSourceTwo A q (R • x))-
      (f (R • y)-quadraticScalarSourceTwo A q (R • y))| ≤
      (Kf+16*Ka*M)*‖R • x-R • y‖^alpha := by
    rw [show (f (R • x)-quadraticScalarSourceTwo A q (R • x))-
        (f (R • y)-quadraticScalarSourceTwo A q (R • y)) =
        (f (R • x)-f (R • y))-
        (quadraticScalarSourceTwo A q (R • x)-quadraticScalarSourceTwo A q (R • y)) by ring]
    exact (abs_sub _ _).trans ((add_le_add (hf _ hmx _ hmy) hqf).trans_eq (by ring))
  simp only [actualFlatResidualSourceFour,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hb)]
  apply (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hb).le).trans_eq
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hR,
    Real.mul_rpow hR.le (norm_nonneg _)]
  ring

theorem actual_operator_identity_action_bound_four {C : Mat} {d : ℝ}
    (hC : ‖actualMatrixOperatorTwo C-actualMatrixOperatorTwo (1 : Mat)‖ ≤ d) (v : E) :
    ‖v-matMulE C v‖ ≤ d*‖v‖ := by
  have hh := ((actualMatrixOperatorTwo C-actualMatrixOperatorTwo (1 : Mat)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg v))
  rw [actual_matrix_operator_one_two] at hh
  change ‖matMulE C v-v‖ ≤ d*‖v‖ at hh
  simpa only [norm_sub_rev] using hh

theorem actual_flat_residual_source_growth_four {N : E} {A : E → Mat} {f q : E → ℝ}
    (hq : IsQuadraticPolynomial q) {R b Ka Kf M alpha : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hb : 0 < b) (hKa : 0 ≤ Ka) (hM : 0 ≤ M)
    (hH : ‖realHessian q 0‖ ≤ M)
    (hqt : ∀ x, (realBlockHessian realDirections imagDirections q x).trace=0)
    (hA : ∀ x ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ Ka*‖x‖^alpha)
    (hf : ∀ x ∈ actualFlatUpperBallFour N 1, |f x| ≤ Kf*‖x‖^alpha) :
    ∀ x ∈ actualFlatUpperBallFour N 1,
      |actualFlatResidualSourceFour A f q R b x| ≤
      (b⁻¹*R^alpha*(Kf+16*Ka*M))*‖x‖^alpha := by
  intro x hx
  have hm := actual_flat_unit_dilation_maps_four N hR hR1 hx
  have hqf := actual_harmonic_quadratic_source_bound_two
    (mul_nonneg hKa (Real.rpow_nonneg (norm_nonneg _) alpha)) hM
    (actual_operator_identity_action_bound_four (hA _ hm))
    (by simpa only [quadratic_realHessian_from_jet_zero hq] using hH) (hqt (R • x))
  have hh : |f (R • x)-quadraticScalarSourceTwo A q (R • x)| ≤
      (Kf+16*Ka*M)*‖R • x‖^alpha :=
    (abs_sub _ _).trans ((add_le_add (hf _ hm) hqf).trans_eq (by ring))
  simp only [actualFlatResidualSourceFour,abs_mul,abs_of_pos (inv_pos.mpr hb)]
  apply (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hb).le).trans_eq
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg _)]
  ring

theorem actual_flat_dilation_operator_holder_four {N : E} {A : E → Mat} {R K alpha : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hA : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (A (R • x))-actualMatrixOperatorTwo (A (R • y))‖ ≤
      (K*R^alpha)*‖x-y‖^alpha := by
  intro x hx y hy
  have hh := hA _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
    _ (actual_flat_unit_dilation_maps_four N hR hR1 hy)
  exact hh.trans_eq (by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hR,
      Real.mul_rpow hR.le (norm_nonneg _)]
    ring)

end PowerConvexity
