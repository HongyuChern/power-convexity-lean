import PowerConvexity.Analysis.ActualUniformDefiningNormalization
import PowerConvexity.Analysis.ActualNormalPreservingNormalizationFour

/-! # Genuine frozen normalization with one fixed inward unit normal

The orthogonal adjustment preserves the normalized coefficient. The common
forward, inverse and defining-scalar bounds precede the boundary point and
the actual positive matrix. No continuous choice of matrix factors is used.
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

theorem actual_compact_fixed_normal_frozen_normalization_four
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hDf : ∀ c ∈ K, fderiv ℝ f c ≠ 0) {N : E} (hN : ‖N‖=1)
    {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda) :
    ∃ Z > 0, ∀ c ∈ K, ∀ A : Mat, A.PosDef →
      (∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE A v)) →
      (∀ v : E, inner ℝ v (matMulE A v) ≤ Lambda*‖v‖^2) →
      ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G A=1 ∧
        ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
        ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
        ∃ zeta : ℝ, zeta < 0 ∧ |zeta| ≤ Z ∧
          ∀ v : E, zeta*fderiv ℝ f c (G v)=inner ℝ N v := by
  obtain ⟨Z,hZ,hnormal⟩ := actual_compact_inward_differential_normalization
    hK hf hDf (inv_nonneg.mpr (Real.sqrt_nonneg lam))
  refine ⟨Z,hZ,?_⟩
  intro c hc A hA hlo hhi
  obtain ⟨G0,hG0⟩ := actual_positive_frozen_normalization_two hA
  have hG0bound := actual_frozen_normalization_operator_bounds_two G0 hG0 hlam hLambda hlo hhi
  obtain ⟨W,hW,zeta,hz,hzZ,hD⟩ := hnormal c hc G0 hG0bound.2
  have hW0 : W ≠ 0 := by
    intro hz0
    rw [hz0,norm_zero] at hW
    norm_num at hW
  obtain ⟨O,hO⟩ := actual_normal_alignment_four hN hW0
  let G := O.toContinuousLinearEquiv.trans G0
  have hG : actualLinearCongruenceMatrixTwo G A=1 := by
    dsimp only [G]
    rw [actual_linear_congruence_trans_four,hG0,actual_linear_isometry_congruence_identity_four]
  have hb := actual_frozen_normalization_operator_bounds_two G hG hlam hLambda hlo hhi
  refine ⟨G,hG,hb.1,hb.2,zeta,hz,hzZ,?_⟩
  intro v
  change zeta*fderiv ℝ f c (G0 (O v))=inner ℝ N v
  rw [hD,hO,hW,one_mul]

end PowerConvexity
