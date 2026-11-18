import PowerConvexity.Analysis.ActualLinearEllipticityBoundsTwo

/-! # Constructed actual elliptic coefficient and full weak pullback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualLinearPullbackCoeffTwo {U : Set E} (G : E ≃L[ℝ] E)
    (A : EllipticCoeff (2+2) U) : EllipticCoeff (2+2) (G ⁻¹' U) where
  a := fun z => actualLinearCongruenceMatrixTwo G (A.a (G z))
  lam := A.lam/(max 1 ‖G.toContinuousLinearMap‖)^2
  Λ := A.Λ*(max 1 ‖G.symm.toContinuousLinearMap‖)^2
  measurable_comp := actual_linear_congruence_measurable_two G A.measurable_comp
  hlam := div_pos A.hlam (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  hΛ := by
    have hk : 1 ≤ (max 1 ‖G.toContinuousLinearMap‖)^2 := by
      nlinarith [le_max_left (1 : ℝ) ‖G.toContinuousLinearMap‖]
    have hl : 1 ≤ (max 1 ‖G.symm.toContinuousLinearMap‖)^2 := by
      nlinarith [le_max_left (1 : ℝ) ‖G.symm.toContinuousLinearMap‖]
    exact (div_le_self A.lam_nonneg hk).trans
      (A.hΛ.trans (le_mul_of_one_le_right A.Λ_nonneg hl))
  coercive := by
    filter_upwards [actual_ae_linear_pullback_two G A.coercive] with z hz
    intro v
    exact actual_linear_congruence_coercive_two G (A.a (G z)) A.lam_nonneg
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (le_max_right _ _) hz v
  coercive_inv := by
    filter_upwards [actual_ae_linear_pullback_two G A.coercive_inv] with z hz
    intro v
    exact actual_linear_congruence_inverse_coercive_two G (A.a (G z)) A.Λ_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (le_max_right _ _) hz v

theorem actual_linear_pullback_coeff_action_two {U : Set E} (G : E ≃L[ℝ] E)
    (A : EllipticCoeff (2+2) U) (z v : E) :
    matMulE ((actualLinearPullbackCoeffTwo G A).a z) v =
      G.symm (matMulE (A.a (G z)) (G.symm.toContinuousLinearMap.adjoint v)) :=
  actual_linear_congruence_action_two G (A.a (G z)) v

theorem actual_scalar_weak_constructed_linear_pullback_two {U : Set E}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (G : E ≃L[ℝ] E)
    (A : EllipticCoeff (2+2) U) {f u : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo (actualLinearPullbackCoeffTwo G A)
      (fun z => f (G z)) (fun z => u (G z)) := by
  exact actual_scalar_weak_linear_pullback_two hU hUb G A (actualLinearPullbackCoeffTwo G A)
    (fun z hz v => actual_linear_pullback_coeff_action_two G A z v) hf hu

end PowerConvexity
