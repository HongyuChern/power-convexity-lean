import PowerConvexity.Analysis.ActualUniformPullbackL2Two

/-! # Pullback L2 amplitudes chosen before the actual function -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_family_affine_linear_pullback_L2_two
    {r N₀ : ℝ} (hr : 0 < r) (hN₀ : 0 ≤ N₀) (B : ℝ) :
    ∃ N ≥ 0, ∀ U : Set E, ∀ u : E → ℝ,
      ∀ hu : MemLp u 2 (volume.restrict U), ‖hu.toLp u‖ ≤ N₀ →
      ∀ (G : E ≃L[ℝ] E) (c : E),
      ‖G.symm.toContinuousLinearMap‖ ≤ B → ball c r ⊆ G ⁻¹' U →
      ∀ hv : MemLp (fun z => u (G (c+r • z))) 2 (volume.restrict (ball (0 : E) 1)),
        ‖hv.toLp (fun z => u (G (c+r • z)))‖ ≤ N := by
  obtain ⟨J,hJ,hbound⟩ := actual_linear_jacobians_uniform_of_inverse_bound_two B
  refine ⟨Real.sqrt ((r^4)⁻¹*J*N₀^2),Real.sqrt_nonneg _,?_⟩
  intro U u hu hun G c hG hsub hv
  apply Real.le_sqrt_of_sq_le
  have hh := actual_affine_linear_pullback_L2_squared_bound_two G c hr hsub
    (hbound G hG) hu hv
  exact hh.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) hN₀).mpr hun) (by positivity))

end PowerConvexity
