import PowerConvexity.Analysis.ActualNormalPreservingNormalizationFour

/-! # Exact operator Holder control for the actual inverse congruence -/
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

theorem actual_linear_congruence_operator_difference_four (G : E ≃L[ℝ] E) (A B : Mat) :
    actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G A)-
      actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G B) =
      G.symm.toContinuousLinearMap.comp
        ((actualMatrixOperatorTwo A-actualMatrixOperatorTwo B).comp
          G.symm.toContinuousLinearMap.adjoint) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    actual_matrix_operator_apply_two,actual_linear_congruence_action_two]
  exact (map_sub G.symm _ _).symm

theorem actual_linear_congruence_operator_norm_four (G : E ≃L[ℝ] E) (A B : Mat) :
    ‖actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G A)-
      actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G B)‖ ≤
      ‖G.symm.toContinuousLinearMap‖^2*‖actualMatrixOperatorTwo A-actualMatrixOperatorTwo B‖ := by
  rw [actual_linear_congruence_operator_difference_four]
  calc
    _ ≤ ‖G.symm.toContinuousLinearMap‖*
        ‖(actualMatrixOperatorTwo A-actualMatrixOperatorTwo B).comp G.symm.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖G.symm.toContinuousLinearMap‖*
        (‖actualMatrixOperatorTwo A-actualMatrixOperatorTwo B‖*‖G.symm.toContinuousLinearMap.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem actual_linear_scaled_congruence_holder_four (G : E ≃L[ℝ] E)
    {A : E → Mat} {U V : Set E} {c : E} {r alpha K M L : ℝ}
    (hr : 0 ≤ r) (halpha : 0 ≤ alpha) (hK : 0 ≤ K) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ L)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hA : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ V, ∀ y ∈ V,
      ‖actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G (A (c+G (r • x))))-
        actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G (A (c+G (r • y))))‖ ≤
        (L^2*K*(r*M)^alpha)*‖x-y‖^alpha := by
  intro x hx y hy
  have hn : ‖(c+G (r • x))-(c+G (r • y))‖ ≤ (r*M)*‖x-y‖ := by
    have he : (c+G (r • x))-(c+G (r • y))=G (r • (x-y)) := by
      simp only [smul_sub,map_sub]
      abel
    rw [he]
    have hh := (G.toContinuousLinearMap.le_opNorm (r • (x-y))).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg (r • (x-y))))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hh
    exact hh.trans_eq (by ring)
  have hsq : ‖G.symm.toContinuousLinearMap‖^2 ≤ L^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hInv 2
  calc
    _ ≤ ‖G.symm.toContinuousLinearMap‖^2*
        ‖actualMatrixOperatorTwo (A (c+G (r • x)))-actualMatrixOperatorTwo (A (c+G (r • y)))‖ :=
      actual_linear_congruence_operator_norm_four G _ _
    _ ≤ L^2*(K*‖(c+G (r • x))-(c+G (r • y))‖^alpha) :=
      mul_le_mul hsq (hA _ (hmap hx) _ (hmap hy)) (norm_nonneg _) (sq_nonneg L)
    _ ≤ L^2*(K*((r*M)*‖x-y‖)^alpha) := by
      gcongr
    _ = _ := by rw [Real.mul_rpow (mul_nonneg hr hM) (norm_nonneg _)]; ring

end PowerConvexity
