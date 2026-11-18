import PowerConvexity.Analysis.ActualLinearCoefficientCongruenceTwo

/-! # Quantitative ellipticity of the actual inverse congruence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_ae_linear_pullback_two {U : Set E} {P : E → Prop}
    (G : E ≃L[ℝ] E) (hP : ∀ᵐ x ∂volume.restrict U, P x) :
    ∀ᵐ z ∂volume.restrict (G ⁻¹' U), P (G z) := by
  have hG : MeasurableEmbedding G := G.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← hG.ae_map_iff,← hG.restrict_map,actual_linear_map_volume_two,Measure.restrict_smul]
  exact Measure.ae_smul_measure hP _

theorem actual_linear_adjoint_recovery_bound_two (G : E ≃L[ℝ] E)
    {k : ℝ} (hG : ‖G.toContinuousLinearMap‖ ≤ k) (v : E) :
    ‖v‖ ≤ k*‖G.symm.toContinuousLinearMap.adjoint v‖ := by
  have he : G.toContinuousLinearMap.adjoint (G.symm.toContinuousLinearMap.adjoint v) = v := by
    simpa only [G.symm_symm] using actual_linear_adjoint_inverse_apply_two G.symm v
  calc
    ‖v‖ = ‖G.toContinuousLinearMap.adjoint (G.symm.toContinuousLinearMap.adjoint v)‖ := by rw [he]
    _ ≤ ‖G.toContinuousLinearMap.adjoint‖*‖G.symm.toContinuousLinearMap.adjoint v‖ :=
      G.toContinuousLinearMap.adjoint.le_opNorm _
    _ ≤ k*‖G.symm.toContinuousLinearMap.adjoint v‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_right hG (norm_nonneg _)

theorem actual_linear_congruence_coercive_two (G : E ≃L[ℝ] E) (A : Mat)
    {lam k : ℝ} (hlam : 0 ≤ lam) (hk : 0 < k) (hG : ‖G.toContinuousLinearMap‖ ≤ k)
    (hA : ∀ v : E, lam*‖v‖^2 ≤ ⟪v,matMulE A v⟫_ℝ) (v : E) :
    (lam/k^2)*‖v‖^2 ≤ ⟪v,matMulE (actualLinearCongruenceMatrixTwo G A) v⟫_ℝ := by
  let y := G.symm.toContinuousLinearMap.adjoint v
  have hn : ‖v‖ ≤ k*‖y‖ := actual_linear_adjoint_recovery_bound_two G hG v
  have hs : ‖v‖^2 ≤ k^2*‖y‖^2 := by
    nlinarith [norm_nonneg v,norm_nonneg y]
  have hm : (lam/k^2)*‖v‖^2 ≤ lam*‖y‖^2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hk)]
    nlinarith [mul_le_mul_of_nonneg_left hs hlam]
  rw [actual_linear_congruence_action_two]
  change (lam/k^2)*‖v‖^2 ≤ ⟪v,G.symm.toContinuousLinearMap (matMulE A y)⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hm.trans (hA y)

theorem actual_linear_congruence_inverse_coercive_two (G : E ≃L[ℝ] E) (A : Mat)
    {Lambda l : ℝ} (hLambda : 0 < Lambda) (hl : 0 < l)
    (hG : ‖G.symm.toContinuousLinearMap‖ ≤ l)
    (hA : ∀ v : E, Lambda⁻¹*‖v‖^2 ≤ ⟪v,matMulE A⁻¹ v⟫_ℝ) (v : E) :
    (Lambda*l^2)⁻¹*‖v‖^2 ≤
      ⟪v,matMulE (actualLinearCongruenceMatrixTwo G A)⁻¹ v⟫_ℝ := by
  have hn : ‖v‖ ≤ l*‖G v‖ := by
    calc
      ‖v‖ = ‖G.symm (G v)‖ := by rw [G.symm_apply_apply]
      _ ≤ ‖G.symm.toContinuousLinearMap‖*‖G v‖ := G.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ l*‖G v‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  have hs : ‖v‖^2 ≤ l^2*‖G v‖^2 := by
    nlinarith [norm_nonneg v,norm_nonneg (G v)]
  have hm : (Lambda*l^2)⁻¹*‖v‖^2 ≤ Lambda⁻¹*‖G v‖^2 := by
    rw [inv_mul_eq_div,div_le_iff₀ (mul_pos hLambda (sq_pos_of_pos hl))]
    have he : (Lambda⁻¹*‖G v‖^2)*(Lambda*l^2) = l^2*‖G v‖^2 := by
      field_simp
    rw [he]
    exact hs
  rw [actual_linear_congruence_inverse_action_two,ContinuousLinearMap.adjoint_inner_right]
  exact hm.trans (hA (G v))

end PowerConvexity
