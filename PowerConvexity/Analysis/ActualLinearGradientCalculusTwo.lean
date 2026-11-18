import PowerConvexity.Analysis.ActualWeakLinearPullbackTwo
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Actual adjoint gradient and smooth-test change of coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_fderiv_coordinate_expansion_two (f : E → ℝ) (x v : E) :
    fderiv ℝ f x v = ∑ i, v i*fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hv : (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  nth_rw 1 [← hv]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem actual_linear_weak_gradient_adjoint_two (G : E ≃L[ℝ] E)
    (W : E → E) (z : E) :
    actualLinearWeakGradientTwo G W z = G.toContinuousLinearMap.adjoint (W (G z)) := by
  ext i
  change (∑ j, (G (EuclideanSpace.single i 1)) j*W (G z) j) = _
  calc
    _ = ⟪W (G z),G (EuclideanSpace.single i 1)⟫_ℝ := by
      simp only [PiLp.inner_apply,Real.inner_apply,mul_comm]
    _ = ⟪G.toContinuousLinearMap.adjoint (W (G z)),EuclideanSpace.single i 1⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left G.toContinuousLinearMap _ _).symm
    _ = _ := by simp [EuclideanSpace.inner_single_right]

theorem actual_smooth_gradient_linear_pullback_two (G : E ≃L[ℝ] E)
    {f : E → ℝ} (hf : Differentiable ℝ f) (z : E) :
    smoothGradField (fun x => f (G x)) z =
      G.toContinuousLinearMap.adjoint (smoothGradField f (G z)) := by
  rw [← actual_linear_weak_gradient_adjoint_two]
  ext i
  change fderiv ℝ (fun x => f (G x)) z (EuclideanSpace.single i 1) =
    ∑ j, (G (EuclideanSpace.single i 1)) j*fderiv ℝ f (G z) (EuclideanSpace.single j 1)
  have hh := (hf (G z)).hasFDerivAt.comp z G.hasFDerivAt
  change fderiv ℝ (f ∘ G) z (EuclideanSpace.single i 1) = _
  rw [hh.fderiv]
  exact actual_fderiv_coordinate_expansion_two f (G z) (G (EuclideanSpace.single i 1))

theorem actual_smooth_test_linear_pushforward_two {U : Set E}
    (G : E ≃L[ℝ] E) {phi : E → ℝ} (hp : IsSmoothTestOn (G ⁻¹' U) phi) :
    IsSmoothTestOn U (fun x => phi (G.symm x)) := by
  refine ⟨hp.1.comp G.symm.contDiff,hp.2.1.comp_homeomorph G.symm.toHomeomorph,?_⟩
  intro x hx
  have hx' := hp.2.2 ((tsupport_comp_subset_preimage phi G.symm.continuous) hx)
  simpa only [mem_preimage,G.apply_symm_apply] using hx'

theorem actual_smooth_gradient_inverse_pullback_two (G : E ≃L[ℝ] E)
    {phi : E → ℝ} (hp : Differentiable ℝ phi) (z : E) :
    G.toContinuousLinearMap.adjoint
      (smoothGradField (fun x => phi (G.symm x)) (G z)) = smoothGradField phi z := by
  have hh := actual_smooth_gradient_linear_pullback_two G
    (f := fun x => phi (G.symm x)) (hp.comp G.symm.differentiable) z
  simpa only [G.symm_apply_apply] using hh.symm

end PowerConvexity
