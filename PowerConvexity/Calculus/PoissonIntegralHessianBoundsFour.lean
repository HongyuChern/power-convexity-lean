import PowerConvexity.Calculus.PoissonKernelCompactBoundsFour
import PowerConvexity.Calculus.HarmonicPoissonRepresentationFour

/-! # Uniform actual real Hessian bounds and modulus for bounded Poisson data.
The constants are chosen before the continuous boundary datum. All Hessians
are actual Frechet second derivatives of the actual integral or harmonic function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE
local instance pihNormSMul : NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  @NormedSpace.toNormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) inferInstance inferInstance cat6

theorem poissonKernelFour_hessian_continuous_on_sphere {x : E}
    (hx : x ∈ closedBall (0 : E) (1/2 : ℝ)) :
    Continuous (fun ξ : S => realHessian (poissonKernelFour ξ) x) := by
  apply continuous_iff_continuousAt.mpr
  intro ξ
  have hxB : x ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by norm_num))
  have hm : ContinuousAt (fun ζ : S => (x,(ζ : E))) ξ :=
    (continuous_const.prodMk continuous_subtype_val).continuousAt
  exact (poissonKernelFour_hessian_joint_contDiffAt (z := (x,(ξ : E)))
    (unitBall_point_ne_unitSphere_four hxB ξ) 0).continuousAt.comp
      (f := fun ζ : S => (x,(ζ : E))) hm

theorem poissonIntegralFour_hessian_universal_bound :
    ∃ M > 0, ∀ f : S → ℝ, Continuous f → (∀ ξ, |f ξ| ≤ 1) →
      ∀ x ∈ closedBall (0 : E) (1/2 : ℝ),
        ‖realHessian (poissonIntegralFour unitSphereProbabilityFour f) x‖ ≤ M := by
  obtain ⟨M,hM,hKM⟩ := poissonKernelFour_hessian_universal_bound
  refine ⟨M,hM,?_⟩
  intro f hf hfb x hx
  have hxB : x ∈ ball (0 : E) 1 :=
    mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by norm_num))
  rw [(poissonIntegralFour_C2_and_hessian unitSphereProbabilityFour hf).2 x hxB]
  have hb (ξ : S) : ‖f ξ • realHessian (poissonKernelFour ξ) x‖ ≤ M := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      |f ξ| *‖realHessian (poissonKernelFour ξ) x‖ ≤
          1*‖realHessian (poissonKernelFour ξ) x‖ :=
        mul_le_mul_of_nonneg_right (hfb ξ) (norm_nonneg (realHessian (poissonKernelFour ξ) x))
      _ ≤ M := by simpa only [one_mul] using hKM x hx ξ
  simpa using norm_integral_le_of_norm_le_const
    (μ := unitSphereProbabilityFour) (Filter.Eventually.of_forall hb)

theorem poissonIntegralFour_hessian_universal_modulus {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1/2 : ℝ) ∧
      ∀ f : S → ℝ, Continuous f → (∀ ξ, |f ξ| ≤ 1) →
        ∀ x ∈ closedBall (0 : E) (1/2 : ℝ), ∀ y ∈ closedBall (0 : E) (1/2 : ℝ),
          dist x y < δ →
            ‖realHessian (poissonIntegralFour unitSphereProbabilityFour f) x-
              realHessian (poissonIntegralFour unitSphereProbabilityFour f) y‖ ≤ η := by
  obtain ⟨δ,hδ,hδh,hKδ⟩ := poissonKernelFour_hessian_universal_modulus hη
  refine ⟨δ,hδ,hδh,?_⟩
  intro f hf hfb x hx y hy hxy
  have hxB : x ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by norm_num))
  have hyB : y ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by norm_num))
  have hix : Integrable (fun ξ : S => f ξ • realHessian (poissonKernelFour ξ) x)
      unitSphereProbabilityFour :=
    (hf.smul (poissonKernelFour_hessian_continuous_on_sphere hx)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiy : Integrable (fun ξ : S => f ξ • realHessian (poissonKernelFour ξ) y)
      unitSphereProbabilityFour :=
    (hf.smul (poissonKernelFour_hessian_continuous_on_sphere hy)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [(poissonIntegralFour_C2_and_hessian unitSphereProbabilityFour hf).2 x hxB,
    (poissonIntegralFour_C2_and_hessian unitSphereProbabilityFour hf).2 y hyB,← integral_sub hix hiy]
  have hb (ξ : S) : ‖f ξ • realHessian (poissonKernelFour ξ) x-
      f ξ • realHessian (poissonKernelFour ξ) y‖ ≤ η := by
    have he : f ξ • realHessian (poissonKernelFour ξ) x-
        f ξ • realHessian (poissonKernelFour ξ) y =
        f ξ • (realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y) := by
      ext v w
      simp only [_root_.smul_apply,ContinuousLinearMap.sub_apply,smul_eq_mul,mul_sub]
    rw [he,norm_smul,Real.norm_eq_abs]
    calc
      |f ξ| *‖realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y‖ ≤
          1*‖realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y‖ :=
        mul_le_mul_of_nonneg_right (hfb ξ) (norm_nonneg (realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y))
      _ ≤ η := by simpa only [one_mul] using hKδ x hx y hy hxy ξ
  simpa using norm_integral_le_of_norm_le_const
    (μ := unitSphereProbabilityFour) (Filter.Eventually.of_forall hb)

theorem classical_harmonic_unitBall_hessian_eq_poisson_four {g : E → ℝ}
    (hgc : ContinuousOn g (closedBall 0 1))
    (hg : InnerProductSpace.HarmonicOnNhd g (ball 0 1)) {x : E} (hx : x ∈ ball 0 1) :
    realHessian g x = realHessian
      (poissonIntegralFour unitSphereProbabilityFour (fun ξ : S => g ξ)) x := by
  have heq : g =ᶠ[𝓝 x] poissonIntegralFour unitSphereProbabilityFour (fun ξ : S => g ξ) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact classical_harmonic_unitBall_actual_poisson_representation_four hgc hg hy
  exact (heq.fderiv (𝕜 := ℝ)).fderiv_eq

theorem classical_harmonic_unitBall_hessian_universal_bound_four :
    ∃ M > 0, ∀ g : E → ℝ, ContinuousOn g (closedBall 0 1) →
      InnerProductSpace.HarmonicOnNhd g (ball 0 1) →
      (∀ x ∈ closedBall (0 : E) 1, |g x| ≤ 1) →
      ∀ x ∈ closedBall (0 : E) (1/2 : ℝ), ‖realHessian g x‖ ≤ M := by
  obtain ⟨M,hM,hPM⟩ := poissonIntegralFour_hessian_universal_bound
  refine ⟨M,hM,?_⟩
  intro g hgc hg hgb x hx
  have hxB : x ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by norm_num))
  rw [classical_harmonic_unitBall_hessian_eq_poisson_four hgc hg hxB]
  exact hPM (fun ξ : S => g ξ)
    (continuousOn_iff_continuous_domRestrict.mp (hgc.mono sphere_subset_closedBall))
    (fun ξ => hgb ξ (sphere_subset_closedBall ξ.property)) x hx

theorem classical_harmonic_unitBall_hessian_universal_modulus_four {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1/2 : ℝ) ∧
      ∀ g : E → ℝ, ContinuousOn g (closedBall 0 1) →
        InnerProductSpace.HarmonicOnNhd g (ball 0 1) →
        (∀ x ∈ closedBall (0 : E) 1, |g x| ≤ 1) →
        ∀ x ∈ closedBall (0 : E) (1/2 : ℝ), ∀ y ∈ closedBall (0 : E) (1/2 : ℝ),
          dist x y < δ → ‖realHessian g x-realHessian g y‖ ≤ η := by
  obtain ⟨δ,hδ,hδh,hPδ⟩ := poissonIntegralFour_hessian_universal_modulus hη
  refine ⟨δ,hδ,hδh,?_⟩
  intro g hgc hg hgb x hx y hy hxy
  have hxB : x ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by norm_num))
  have hyB : y ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by norm_num))
  rw [classical_harmonic_unitBall_hessian_eq_poisson_four hgc hg hxB,
    classical_harmonic_unitBall_hessian_eq_poisson_four hgc hg hyB]
  exact hPδ (fun ξ : S => g ξ)
    (continuousOn_iff_continuous_domRestrict.mp (hgc.mono sphere_subset_closedBall))
    (fun ξ => hgb ξ (sphere_subset_closedBall ξ.property)) x hx y hy hxy

end PowerConvexity
