import PowerConvexity.Calculus.CompactAffineTangencyTwo
import PowerConvexity.Calculus.VariableDensityBoundaryNormalTwo
import PowerConvexity.Calculus.TangentialBilinearSubsolutionEstimateTwo

/-! # One quadratic affine-jet bound on the entire actual boundary

The constants are chosen before the boundary center, unit tangent direction,
and unknown solution. The defining function and fixed C1 estimate determine
them. No unknown second derivative bound is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance vdbjqRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance vdbjqRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem exists_uniform_boundary_affine_jet_quadratic_bound_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {C0 : ℝ} (hC0 : 0 ≤ C0) :
    ∃ B ≥ 0, ∃ M ≥ 0,
      ∀ x ∈ frontier U, ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
        ∃ (K : E →L[ℂ] E) (c : E),
          (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ M ∧
          ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
            (∀ y ∈ frontier U, u y = 0) →
            (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
            (∀ y ∈ U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) u y).det.re) →
            (∀ y ∈ frontier U, ‖J.derivative y‖ ≤ C0) →
            ∀ y ∈ frontier U, |J.derivative y (c+K y)| ≤ B*‖y-x‖^2 := by
  have hS : IsCompact (frontier U) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨eta,heta,C,hC,M,hM,hD,hquad⟩ := exists_compact_uniform_affine_complex_tangency_two
    e hS hf (fun x hx => (hfb x hx).1) (fun x hx => (hfb x hx).2)
  let B : ℝ := (C0/eta)*C
  refine ⟨B,by dsimp [B]; positivity,M,hM,?_⟩
  intro x hx tau htau htangent
  obtain ⟨K,c,htrace,hcx,hKn,hq⟩ := hquad x hx tau htau htangent
  refine ⟨K,c,htrace,hcx,hKn,?_⟩
  intro u J hu hub hup hud hgrad y hy
  obtain ⟨mu,hmu,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_of_det_lower_two
    hU hconv hK hu J hub e (fun j => Complex.I • e j) hab hup hud hy
    (hf.of_le (by norm_num)).contDiffAt (hfb y hy).1 (hfb y hy).2 (hdef y hy)
  have hm1 := positive_multiple_coefficient_le_norm_bound (fderiv ℝ f y) (J.derivative y)
    (hfb y hy).2 hmu hJ (hgrad y hy)
  have hm : mu ≤ C0/eta := hm1.trans (div_le_div₀ hC0 le_rfl heta (hD y hy))
  rw [hJ,ContinuousLinearMap.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hmu]
  calc
    mu*|fderiv ℝ f y (c+K y)| ≤ mu*(C*‖y-x‖^2) :=
      mul_le_mul_of_nonneg_left (hq y hy) hmu.le
    _ ≤ (C0/eta)*(C*‖y-x‖^2) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = B*‖y-x‖^2 := by dsimp [B]; ring

end
end PowerConvexity
