import PowerConvexity.Analysis.ActualUniformNormalizationBoundsTwo

/-! # Actual pointwise norm and inverse ellipticity on the original open set

The statements are derived from the true almost-everywhere EllipticCoeff
bounds and interior continuity. They introduce no boundary coefficient data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_elliptic_operator_norm_pointwise_four {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U) :
    ∀ x ∈ U, ‖actualMatrixOperatorTwo (A.a x)‖ ≤ A.Λ := by
  have hm (v w : E) : ∀ x ∈ U,
      |inner ℝ w (matMulE (A.a x) v)| ≤ A.Λ*‖w‖*‖v‖ := by
    apply actual_continuousOn_le_of_ae_two hU
      (continuousOn_const.inner (actual_continuous_matrix_action_two ha v)).abs continuousOn_const
    exact A.mixed_bound.mono (fun x hx => hx v w)
  intro x hx
  apply ContinuousLinearMap.opNorm_le_bound _ A.Λ_nonneg
  intro v
  have hh := hm v (matMulE (A.a x) v) x hx
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hh
  change ‖matMulE (A.a x) v‖ ≤ A.Λ*‖v‖
  nlinarith [norm_nonneg (matMulE (A.a x) v),mul_nonneg A.Λ_nonneg (norm_nonneg v)]

theorem actual_elliptic_inverse_coercivity_pointwise_four {U : Set E} (hU : IsOpen U)
    (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContinuousOn (fun x => A.a x i j) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef) :
    ∀ x ∈ U, ∀ v : E,
      A.Λ⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (A.a x)⁻¹ v) := by
  have hmat : ContinuousOn A.a U := continuousOn_pi.mpr
    (fun i => continuousOn_pi.mpr (fun j => ha i j))
  have hi : ∀ i j, ContinuousOn (fun x => (A.a x)⁻¹ i j) U := by
    intro i j x hx
    have hinv : ContinuousAt Inv.inv (A.a x) := by
      apply continuousAt_matrix_inv
      rw [Ring.inverse_eq_inv']
      exact continuousAt_id.inv₀ (ne_of_gt (hpos x hx).det_pos)
    exact (continuous_apply j).continuousAt.comp_continuousWithinAt
      ((continuous_apply i).continuousAt.comp_continuousWithinAt
        (hinv.comp_continuousWithinAt (hmat x hx)))
  intro x hx v
  exact actual_continuousOn_le_of_ae_two hU continuousOn_const
    (continuousOn_const.inner (actual_continuous_matrix_action_two hi v))
    (A.coercive_inv.mono (fun y hy => hy v)) x hx

end PowerConvexity
