import PowerConvexity.Analysis.ActualCofactorMatrixDerivativeTwo

/-! # The quadratic third-derivative correction in the actual second variation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "T3" => E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualCofactorThirdBilinearTwo (T S : T3) (v w : E) : ℝ :=
  ∑ i, ∑ j, actualCofactorMatrixFormTwo (T w) i j *
    S (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) v

def actualCofactorThirdCorrectionTwo (T : T3) (v w : E) : ℝ :=
  actualCofactorThirdBilinearTwo T T v w

theorem actual_trilinear_unit_entry_bound_two
    (T : T3) {M : ℝ} (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (v : E) (hv : ‖v‖ ≤ 1) (i j : Fin (2+2)) :
    |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) v| ≤ M := by
  have hh := (T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).le_opNorm v
  rw [Real.norm_eq_abs] at hh
  have he : ‖T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤ M := by
    exact (T.le_opNorm₂ _ _).trans (by simpa only [EuclideanSpace.norm_single,norm_one,mul_one] using hT)
  exact hh.trans ((mul_le_mul he hv (norm_nonneg _) hM).trans_eq (mul_one _))

theorem actual_cofactor_third_bilinear_bound_two
    (T S : T3) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hT : ‖T‖ ≤ M) (hS : ‖S‖ ≤ N)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |actualCofactorThirdBilinearTwo T S v w| ≤
      16*‖actualCofactorMatrixFormTwo‖*M*N := by
  have hTw : ‖T w‖ ≤ M :=
    (T.le_opNorm w).trans ((mul_le_mul hT hw (norm_nonneg _) hM).trans_eq (mul_one _))
  have he (i j : Fin (2+2)) :
      |actualCofactorMatrixFormTwo (T w) i j *
        S (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) v| ≤
        ‖actualCofactorMatrixFormTwo‖*M*N := by
    rw [abs_mul]
    exact mul_le_mul
      ((actual_cofactor_matrix_entry_norm_bound_two _ i j).trans
        (mul_le_mul_of_nonneg_left hTw (norm_nonneg _)))
      (actual_trilinear_unit_entry_bound_two S hN hS v hv i j)
      (abs_nonneg _) (mul_nonneg (norm_nonneg _) hM)
  calc
    _ ≤ ∑ i, |∑ j, actualCofactorMatrixFormTwo (T w) i j *
        S (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |actualCofactorMatrixFormTwo (T w) i j *
        S (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) v| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (2+2), ∑ _j : Fin (2+2), ‖actualCofactorMatrixFormTwo‖*M*N := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact he i j
    _ = _ := by simp; ring

theorem actual_cofactor_third_correction_bound_two
    (T : T3) {M : ℝ} (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |actualCofactorThirdCorrectionTwo T v w| ≤
      16*‖actualCofactorMatrixFormTwo‖*M^2 := by
  simpa only [actualCofactorThirdCorrectionTwo,pow_two,mul_assoc] using
    actual_cofactor_third_bilinear_bound_two T T hM hM hT hT v w hv hw

theorem actual_cofactor_third_correction_difference_two
    (T S : T3) {M : ℝ} (hM : 0 ≤ M) (hT : ‖T‖ ≤ M) (hS : ‖S‖ ≤ M)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |actualCofactorThirdCorrectionTwo T v w-actualCofactorThirdCorrectionTwo S v w| ≤
      32*‖actualCofactorMatrixFormTwo‖*M*‖T-S‖ := by
  have he : actualCofactorThirdCorrectionTwo T v w-actualCofactorThirdCorrectionTwo S v w =
      actualCofactorThirdBilinearTwo (T-S) T v w+actualCofactorThirdBilinearTwo S (T-S) v w := by
    unfold actualCofactorThirdCorrectionTwo actualCofactorThirdBilinearTwo
    rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [_root_.sub_apply,map_sub,Matrix.sub_apply]
    ring
  rw [he]
  calc
    _ ≤ |actualCofactorThirdBilinearTwo (T-S) T v w|+
      |actualCofactorThirdBilinearTwo S (T-S) v w| := abs_add_le _ _
    _ ≤ 16*‖actualCofactorMatrixFormTwo‖*‖T-S‖*M+
        16*‖actualCofactorMatrixFormTwo‖*M*‖T-S‖ := add_le_add
      (actual_cofactor_third_bilinear_bound_two (T-S) T (norm_nonneg _) hM le_rfl hT v w hv hw)
      (actual_cofactor_third_bilinear_bound_two S (T-S) hM (norm_nonneg _) hS le_rfl v w hv hw)
    _ = _ := by ring

end PowerConvexity
