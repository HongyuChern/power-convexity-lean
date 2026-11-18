import PowerConvexity.Calculus.PoissonIntegralFour
import PowerConvexity.Analysis.UnitSphereMeasureFour
import PowerConvexity.Calculus.ViscosityHarmonicBallUniquenessTwo

/-! # Actual mass-one normalization of the four-dimensional Poisson kernel.
The proof combines actual sphere invariance, actual harmonicity of the
integral, and the proved classical radial uniqueness theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

theorem poissonKernelFour_rotation (T : E ≃ₗᵢ[ℝ] E) (ξ x : E) :
    poissonKernelFour (T ξ) (T x) = poissonKernelFour ξ x := by
  simp only [poissonKernelFour,← T.map_sub,T.norm_map]

theorem poissonKernelFour_integral_rotation (T : E ≃ₗᵢ[ℝ] E) (x : E) :
    (∫ ξ : S, poissonKernelFour ξ (T x) ∂unitSphereProbabilityFour) =
      ∫ ξ : S, poissonKernelFour ξ x ∂unitSphereProbabilityFour := by
  rw [← unitSphereProbabilityFour_integral_rotation T (fun ξ : S => poissonKernelFour ξ (T x))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => poissonKernelFour_rotation T ξ x)

theorem poissonKernelFour_integral_eq_one {x : E} (hx : x ∈ ball 0 1) :
    (∫ ξ : S, poissonKernelFour ξ x ∂unitSphereProbabilityFour) = 1 := by
  let g : E → ℝ := poissonIntegralFour unitSphereProbabilityFour (fun _ => 1)
  have hg : InnerProductSpace.HarmonicOnNhd g (ball 0 1) :=
    poissonIntegralFour_harmonic_on_unit_ball unitSphereProbabilityFour continuous_const
  have he (y : E) : g y = ∫ ξ : S, poissonKernelFour ξ y ∂unitSphereProbabilityFour := by
    simp only [g,poissonIntegralFour,one_mul]
  have hradial : ∀ y ∈ ball (0 : E) 1, ∀ z ∈ ball (0 : E) 1,
      dist y 0 = dist z 0 → g y = g z := by
    intro y hy z hz heq
    obtain ⟨T,hT⟩ := exists_linearIsometryEquiv_map_of_norm_eq_four
      (by simpa only [dist_zero_right] using heq)
    rw [he y,he z,← hT]
    exact (poissonKernelFour_integral_rotation T y).symm
  have hzero : g 0 = 1 := by
    rw [he]
    have hK (ξ : S) : poissonKernelFour ξ 0 = 1 :=
      poissonKernelFour_at_zero (by simpa only [mem_sphere,dist_zero_right] using ξ.property)
    simp_rw [hK]
    simp
  exact (he x).symm.trans ((actual_radial_classical_harmonic_constant_two hg hradial x hx).trans hzero)

theorem poissonKernelFour_continuous_on_sphere {x : E} (hx : x ∈ ball 0 1) :
    Continuous (fun ξ : S => poissonKernelFour ξ x) := by
  apply continuous_iff_continuousAt.mpr
  intro ξ
  have h := (poissonKernelFour_joint_contDiffAt (z := (x,(ξ : E))) (unitBall_point_ne_unitSphere_four hx ξ) 0).continuousAt
  exact h.comp (f := fun η : S => (x,(η : E)))
    (continuous_const.prodMk continuous_subtype_val).continuousAt

theorem poissonIntegralFour_abs_le {f : S → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ ξ, |f ξ| ≤ M) {x : E} (hx : x ∈ ball 0 1) :
    |poissonIntegralFour unitSphereProbabilityFour f x| ≤ M := by
  have hk := poissonKernelFour_continuous_on_sphere hx
  have hi : Integrable (fun ξ : S => f ξ*poissonKernelFour ξ x) unitSphereProbabilityFour :=
    (hf.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : Integrable (fun ξ : S => M*poissonKernelFour ξ x) unitSphereProbabilityFour :=
    (continuous_const.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (ξ : S) := poissonKernelFour_nonneg_on_unit_ball (ξ := (ξ:E)) (ball_subset_closedBall hx)
  calc
    |poissonIntegralFour unitSphereProbabilityFour f x| ≤
        ∫ ξ : S, ‖f ξ*poissonKernelFour ξ x‖ ∂unitSphereProbabilityFour :=
      by
        simpa only [poissonIntegralFour,Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := unitSphereProbabilityFour)
            (fun ξ : S => f ξ*poissonKernelFour ξ x))
    _ ≤ ∫ ξ : S, M*poissonKernelFour ξ x ∂unitSphereProbabilityFour := by
      apply integral_mono hi.norm hb
      intro ξ
      change ‖f ξ*poissonKernelFour ξ x‖ ≤ M*poissonKernelFour ξ x
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn ξ)]
      exact mul_le_mul_of_nonneg_right (hM ξ) (hn ξ)
    _ = M := by rw [integral_const_mul,poissonKernelFour_integral_eq_one hx,mul_one]

end PowerConvexity
