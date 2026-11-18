import PowerConvexity.Analysis.ActualUniformCofactorBarrierEstimateTwo

/-! # Actual boundary distance bounds supplied by a smooth barrier -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem actual_smooth_barrier_boundary_point_bound_two
    {U : Set X} (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {w : X → ℝ} (hw : ContDiff ℝ 1 w) (hwb : ∀ z ∈ frontier U, w z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closure U, ∀ z ∈ frontier U,
      |w x| ≤ C*‖x-z‖ := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (hw.continuous_fderiv one_ne_zero).continuousOn
  let C : ℝ := max B 0+1
  have hC : 0 < C := by dsimp only [C]; linarith [le_max_right B 0]
  have hBC : B ≤ C := by dsimp only [C]; linarith [le_max_left B 0]
  refine ⟨C,hC,?_⟩
  intro x hx z hz
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ closure U) => hw.differentiable one_ne_zero y)
    (fun y hy => (hB y hy).trans hBC) hconv.closure (frontier_subset_closure hz) hx
  simpa only [hwb z hz,sub_zero,Real.norm_eq_abs] using hh

local notation "E" => AmbientSpace (2+2)

theorem actual_uniform_cofactor_boundary_point_estimate_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ v : E → ℝ,
      ContDiffOn ℝ 4 v U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections v x).PosDef) →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections v x).det.re) →
      ∀ A : EllipticCoeff (2+2) U,
      (∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff v x) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict U) →
      ActualScalarWeakEquationTwo A f u → MemH01 u U → ContinuousOn u U →
      ∀ F : ℝ, 0 ≤ F → (∀ x ∈ U, |f x| ≤ F) →
      ∀ x ∈ U, ∀ z ∈ frontier U, |u x| ≤ c*F*C*‖x-z‖ := by
  obtain ⟨eps,heps,hest⟩ := actual_uniform_cofactor_zeroTrace_barrier_estimate_two hU hK hw hwp hwb
  obtain ⟨D,hD,hwbnd⟩ := actual_smooth_barrier_boundary_point_bound_two hconv hK
    (hw.of_le (by norm_num)) hwb
  refine ⟨D/(2*eps),div_pos hD (by positivity),?_⟩
  intro c hc v hv hvp hvd A hA f u hf hu hu0 huC F hF hfb x hx z hz
  have hk : 0 ≤ c*F/(2*eps) := div_nonneg (mul_nonneg hc.le hF) (by positivity)
  calc
    |u x| ≤ (c*F/(2*eps))*(-w x) := hest c hc v hv hvp hvd A hA f u hf hu hu0 huC F hF hfb x hx
    _ ≤ (c*F/(2*eps))*|w x| := mul_le_mul_of_nonneg_left (neg_le_abs _) hk
    _ ≤ (c*F/(2*eps))*(D*‖x-z‖) :=
      mul_le_mul_of_nonneg_left (hwbnd x (subset_closure hx) z hz) hk
    _ = c*F*(D/(2*eps))*‖x-z‖ := by ring

end PowerConvexity
