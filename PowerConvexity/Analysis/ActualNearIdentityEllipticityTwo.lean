import PowerConvexity.Analysis.ActualScalarLinearPullbackTwo

/-! # Actual half-ellipticity from a small coefficient deviation.
Only the ellipticity bookkeeping changes; the actual coefficient and
the full weak equation are preserved exactly.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_near_identity_coercivity_two
    (A : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
    (hA : ∀ v : E, ‖v-matMulE A v‖ ≤ (1/2 : ℝ)*‖v‖) (v : E) :
    (1/2 : ℝ)*‖v‖^2 ≤ ⟪v,matMulE A v⟫_ℝ := by
  have hb := (abs_real_inner_le_norm v (v-matMulE A v)).trans
    (mul_le_mul_of_nonneg_left (hA v) (norm_nonneg v))
  rw [inner_sub_right,real_inner_self_eq_norm_sq] at hb
  nlinarith [le_abs_self (‖v‖^2-⟪v,matMulE A v⟫_ℝ)]

def actualHalfEllipticRepackTwo {U : Set E} (A : EllipticCoeff (2+2) U)
    (hA : ∀ᵐ x ∂volume.restrict U, ∀ v : E, ‖v-matMulE (A.a x) v‖ ≤ (1/2 : ℝ)*‖v‖) :
    EllipticCoeff (2+2) U where
  a := A.a
  lam := 1/2
  Λ := max (1/2) A.Λ
  measurable_comp := A.measurable_comp
  hlam := by norm_num
  hΛ := le_max_left _ _
  coercive := by
    filter_upwards [hA] with x hx
    exact actual_near_identity_coercivity_two (A.a x) hx
  coercive_inv := by
    filter_upwards [A.coercive_inv] with x hx
    intro v
    have hi : (max (1/2 : ℝ) A.Λ)⁻¹ ≤ A.Λ⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le A.Λ_pos (le_max_right _ _)) A.Λ_pos).mpr
        (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_right hi (sq_nonneg ‖v‖)).trans (hx v)

theorem actual_scalar_weak_half_repack_two {U : Set E} (A : EllipticCoeff (2+2) U)
    (hA : ∀ᵐ x ∂volume.restrict U, ∀ v : E, ‖v-matMulE (A.a x) v‖ ≤ (1/2 : ℝ)*‖v‖)
    {f u : E → ℝ} (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo (actualHalfEllipticRepackTwo A hA) f u := by
  refine ⟨hu.1,?_⟩
  intro uw phi hp pw
  exact hu.2 uw phi hp pw

end PowerConvexity
