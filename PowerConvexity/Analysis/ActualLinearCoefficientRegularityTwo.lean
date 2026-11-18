import PowerConvexity.Analysis.ActualLinearEllipticPullbackTwo

/-! # Regularity and column divergence in the actual normalized coordinates

All statements use exactly `actualLinearPullbackCoeffTwo`: there is no second
coefficient field and no change in the chosen linear equivalence.  The column
divergence formula is proved before specializing to divergence-free fields.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_linear_congruence_contDiffOn_two
    {U : Set E} (G : E ≃L[ℝ] E) {a : E → Mat} {n : ℕ∞ω}
    (ha : ∀ i j, ContDiffOn ℝ n (fun x => a x i j) U) (i j : Fin (2+2)) :
    ContDiffOn ℝ n (fun z => actualLinearCongruenceMatrixTwo G (a (G z)) i j)
      (G ⁻¹' U) := by
  simp only [actualLinearCongruenceMatrixTwo, Matrix.mul_apply]
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.mul _ contDiffOn_const
  apply ContDiffOn.sum
  intro l _
  exact contDiffOn_const.mul ((ha l k).comp G.contDiff.contDiffOn (fun _ hz => hz))

theorem actual_linear_pullback_coeff_contDiffOn_two
    {U : Set E} (G : E ≃L[ℝ] E) (A : EllipticCoeff (2+2) U) {n : ℕ∞ω}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A.a x i j) U) (i j : Fin (2+2)) :
    ContDiffOn ℝ n (fun z => (actualLinearPullbackCoeffTwo G A).a z i j)
      (G ⁻¹' U) :=
  actual_linear_congruence_contDiffOn_two G hA i j

theorem actual_linear_inverse_column_recovery_two
    (G : E ≃L[ℝ] E) (l : Fin (2+2)) :
    (∑ i, actualLinearMatrixTwo G.symm i l • G (EuclideanSpace.single i 1)) =
      EuclideanSpace.single l 1 := by
  calc
    _ = G (∑ i, actualLinearMatrixTwo G.symm i l • EuclideanSpace.single i 1) := by
      simp only [map_sum, map_smul]
    _ = G (G.symm (EuclideanSpace.single l 1)) := by
      congr 1
      ext i
      simp [actual_linear_matrix_entry_two, Pi.single_apply]
    _ = _ := G.apply_symm_apply _

theorem actual_linear_congruence_fderiv_apply_two
    (G : E ≃L[ℝ] E) {a : E → Mat} {z : E}
    (ha : ∀ i j, DifferentiableAt ℝ (fun x => a x i j) (G z))
    (i j : Fin (2+2)) (v : E) :
    fderiv ℝ (fun y => actualLinearCongruenceMatrixTwo G (a (G y)) i j) z v =
      ∑ k, actualLinearMatrixTwo G.symm j k *
        ∑ l, actualLinearMatrixTwo G.symm i l *
          fderiv ℝ (fun y => a y l k) (G z) (G v) := by
  have hd : HasFDerivAt
      (fun y => actualLinearCongruenceMatrixTwo G (a (G y)) i j)
      (∑ k, actualLinearMatrixTwo G.symm j k •
        ∑ l, actualLinearMatrixTwo G.symm i l •
          (fderiv ℝ (fun y => a y l k) (G z)).comp G.toContinuousLinearMap) z := by
    simp only [actualLinearCongruenceMatrixTwo, Matrix.mul_apply, Matrix.transpose_apply]
    apply HasFDerivAt.fun_sum
    intro k _
    apply HasFDerivAt.mul_const
    apply HasFDerivAt.fun_sum
    intro l _
    exact ((ha l k).hasFDerivAt.comp z G.hasFDerivAt).const_mul _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe]

theorem actual_linear_congruence_column_divergence_two
    (G : E ≃L[ℝ] E) {a : E → Mat} {z : E}
    (ha : ∀ i j, DifferentiableAt ℝ (fun x => a x i j) (G z))
    (j : Fin (2+2)) :
    (∑ i, fderiv ℝ (fun y => actualLinearCongruenceMatrixTwo G (a (G y)) i j) z
      (EuclideanSpace.single i 1)) =
      ∑ k, actualLinearMatrixTwo G.symm j k *
        ∑ l, fderiv ℝ (fun y => a y l k) (G z) (EuclideanSpace.single l 1) := by
  simp_rw [actual_linear_congruence_fderiv_apply_two G ha]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  calc
    (∑ i, actualLinearMatrixTwo G.symm i l *
        fderiv ℝ (fun y => a y l k) (G z) (G (EuclideanSpace.single i 1))) =
      fderiv ℝ (fun y => a y l k) (G z)
        (∑ i, actualLinearMatrixTwo G.symm i l • G (EuclideanSpace.single i 1)) := by
          simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by rw [actual_linear_inverse_column_recovery_two]

theorem actual_linear_pullback_coeff_divergence_free_two
    {U : Set E} (hU : IsOpen U) (G : E ≃L[ℝ] E) (A : EllipticCoeff (2+2) U)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) :
    ∀ z ∈ G ⁻¹' U, ∀ j,
      (∑ i, fderiv ℝ (fun y => (actualLinearPullbackCoeffTwo G A).a y i j) z
        (EuclideanSpace.single i 1)) = 0 := by
  intro z hz j
  have hd (i k : Fin (2+2)) : DifferentiableAt ℝ (fun y => A.a y i k) (G z) :=
    ((hA i k).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  change (∑ i, fderiv ℝ (fun y => actualLinearCongruenceMatrixTwo G (A.a (G y)) i j) z
    (EuclideanSpace.single i 1)) = 0
  rw [actual_linear_congruence_column_divergence_two G hd]
  simp only [hdiv (G z) hz, mul_zero, Finset.sum_const_zero]

end PowerConvexity
