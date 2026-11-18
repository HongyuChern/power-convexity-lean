import PowerConvexity.Analysis.ActualUniformNormalizationBoundsTwo
import PowerConvexity.Calculus.ActualFlatReflectionGeometryFour

/-! # Frozen normalization preserving the actual boundary half-space
An actual orthogonal adjustment of the positive matrix factor keeps the
chosen unit normal fixed up to a positive scalar. No continuous eigenbasis
or uniformity over a varying normal is assumed.
-/
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

theorem actual_linear_matrix_trans_four (F G : E ≃L[ℝ] E) :
    actualLinearMatrixTwo (F.trans G) = actualLinearMatrixTwo G*actualLinearMatrixTwo F := by
  apply actual_matMulE_ext_two
  intro v
  rw [actual_linear_matrix_action_two,actual_matMulE_mul_two,
    actual_linear_matrix_action_two,actual_linear_matrix_action_two]
  rfl

theorem actual_linear_congruence_trans_four (F G : E ≃L[ℝ] E) (A : Mat) :
    actualLinearCongruenceMatrixTwo (F.trans G) A =
      actualLinearCongruenceMatrixTwo F (actualLinearCongruenceMatrixTwo G A) := by
  have hi : actualLinearMatrixTwo (F.trans G).symm =
      actualLinearMatrixTwo F.symm*actualLinearMatrixTwo G.symm :=
    actual_linear_matrix_trans_four G.symm F.symm
  simp only [actualLinearCongruenceMatrixTwo,hi,Matrix.transpose_mul,Matrix.mul_assoc]

theorem actual_linear_isometry_congruence_identity_four (O : E ≃ₗᵢ[ℝ] E) :
    actualLinearCongruenceMatrixTwo O.toContinuousLinearEquiv (1 : Mat)=1 := by
  apply actual_matMulE_ext_two
  intro v
  rw [actual_linear_congruence_action_two]
  change O.symm (matMulE (1 : Mat) ((O.symm : E →L[ℝ] E).adjoint v)) = matMulE (1 : Mat) v
  rw [O.symm.adjoint_eq_symm]
  have hId (w : E) : matMulE (1 : Mat) w=w := by ext i; simp only [matMulE_apply,Matrix.one_mulVec]
  rw [hId,hId]
  exact O.symm_apply_apply v

theorem actual_normal_alignment_four {N V : E} (hN : ‖N‖=1) (hV : V ≠ 0) :
    ∃ O : E ≃ₗᵢ[ℝ] E, ∀ x : E, inner ℝ V (O x)=‖V‖*inner ℝ N x := by
  have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
  let W := ‖V‖⁻¹ • V
  have hW : ‖W‖=1 := by
    dsimp only [W]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  let O := (ℝ ∙ (N-W))ᗮ.reflection
  have hON : O N=W := Submodule.reflection_sub (hN.trans hW.symm)
  have hrecover : ‖V‖ • O N=V := by
    rw [hON]
    dsimp only [W]
    rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  refine ⟨O,?_⟩
  intro x
  calc
    inner ℝ V (O x) = inner ℝ (‖V‖ • O N) (O x) := by rw [hrecover]
    _ = ‖V‖*inner ℝ N x := by simp only [inner_smul_left,O.inner_map_map]; simp

theorem actual_normal_preserving_frozen_normalization_four {A : Mat} (hA : A.PosDef)
    {N : E} (hN : ‖N‖=1) :
    ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G A=1 ∧
      ∃ k > 0, ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v := by
  obtain ⟨G,hG⟩ := actual_positive_frozen_normalization_two hA
  let V := G.toContinuousLinearMap.adjoint N
  have hV : V ≠ 0 := by
    intro hz
    have hh := actual_linear_adjoint_inverse_apply_two G N
    change G.symm.toContinuousLinearMap.adjoint V=N at hh
    rw [hz,map_zero] at hh
    have hn := hN
    rw [← hh,norm_zero] at hn
    norm_num at hn
  obtain ⟨O,hO⟩ := actual_normal_alignment_four hN hV
  let H := O.toContinuousLinearEquiv.trans G
  refine ⟨H,?_,‖V‖,norm_pos_iff.mpr hV,?_⟩
  · dsimp only [H]
    rw [actual_linear_congruence_trans_four,hG,actual_linear_isometry_congruence_identity_four]
  · intro v
    change inner ℝ N (G (O v))=‖V‖*inner ℝ N v
    exact (G.toContinuousLinearMap.adjoint_inner_left (O v) N).symm.trans (hO v)

theorem actual_normal_preserving_frozen_bounds_four {A : Mat} (hA : A.PosDef)
    {N : E} (hN : ‖N‖=1) {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hlo : ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE A v))
    (hhi : ∀ v : E, inner ℝ v (matMulE A v) ≤ Lambda*‖v‖^2) :
    ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G A=1 ∧
      ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
      ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
      ∃ k > 0, ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v := by
  obtain ⟨G,hG,k,hk,hn⟩ := actual_normal_preserving_frozen_normalization_four hA hN
  obtain ⟨hGn,hInv⟩ := actual_frozen_normalization_operator_bounds_two G hG hlam hLambda hlo hhi
  exact ⟨G,hG,hGn,hInv,k,hk,hn⟩

end PowerConvexity
