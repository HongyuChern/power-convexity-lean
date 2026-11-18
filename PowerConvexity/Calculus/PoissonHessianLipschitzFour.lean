import PowerConvexity.Calculus.PoissonIntegralHessianBoundsFour
import Mathlib.Analysis.Calculus.MeanValue

/-! # A common Lipschitz constant for actual harmonic Hessians

Compactness is applied to the derivative of the actual Poisson-kernel
Hessian, before choosing the boundary datum. This supplies a quantitative
cubic Taylor remainder and does not use a merely qualitative common modulus.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem poissonKernelFour_hessian_universal_lipschitz :
    ∃ L > 0, ∀ x ∈ closedBall (0 : E) (1/2 : ℝ),
      ∀ y ∈ closedBall (0 : E) (1/2 : ℝ), ∀ ξ : S,
        ‖realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y‖ ≤
          L*‖x-y‖ := by
  let F : E × E → (E →L[ℝ] E →L[ℝ] ℝ) :=
    fun z => realHessian (poissonKernelFour z.2) z.1
  have hDC : ContinuousOn (fun p : E × S => fderiv ℝ F (p.1,(p.2 : E)))
      (closedBall (0 : E) (1/2 : ℝ) ×ˢ univ) := by
    intro p hp
    have hx : p.1 ∈ ball (0 : E) 1 :=
      mem_ball.mpr ((mem_closedBall.mp hp.1).trans_lt (by norm_num))
    have hd : ContinuousAt (fderiv ℝ F) (p.1,(p.2 : E)) :=
      ((poissonKernelFour_hessian_joint_contDiffAt
        (unitBall_point_ne_unitSphere_four hx p.2) 1).fderiv_right
          (m := 0) (by norm_num)).continuousAt
    exact (hd.comp (f := fun q : E × S => (q.1,(q.2 : E)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt).continuousWithinAt
  have hcompact := (isCompact_closedBall (0 : E) (1/2 : ℝ)).prod
    (isCompact_univ : IsCompact (univ : Set S))
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hDC
  let L := max C 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨L,hL,?_⟩
  intro x hx y hy ξ
  have hd : ∀ z ∈ closedBall (0 : E) (1/2 : ℝ) ×ˢ {(ξ : E)},
      DifferentiableAt ℝ F z := by
    intro z hz
    have hz2 : z.2=(ξ : E) := hz.2
    have hzB : z.1 ∈ ball (0 : E) 1 :=
      mem_ball.mpr ((mem_closedBall.mp hz.1).trans_lt (by norm_num))
    apply (poissonKernelFour_hessian_joint_contDiffAt (n := 1) ?_).differentiableAt (by norm_num)
    rw [hz2]
    exact unitBall_point_ne_unitSphere_four hzB ξ
  have hb : ∀ z ∈ closedBall (0 : E) (1/2 : ℝ) ×ˢ {(ξ : E)},
      ‖fderiv ℝ F z‖ ≤ L := by
    intro z hz
    have hz2 : z.2=(ξ : E) := hz.2
    have he : z=(z.1,(ξ : E)) := by ext <;> simp [hz2]
    rw [he]
    exact (hC (z.1,ξ) ⟨hz.1,mem_univ _⟩).trans (le_max_left _ _)
  have hcv : Convex ℝ (closedBall (0 : E) (1/2 : ℝ) ×ˢ {(ξ : E)}) :=
    (convex_closedBall (0 : E) (1/2)).prod (convex_singleton (ξ : E))
  have hh := hcv.norm_image_sub_le_of_norm_fderiv_le hd hb
    (x := (y,(ξ : E))) (y := (x,(ξ : E))) ⟨hy,rfl⟩ ⟨hx,rfl⟩
  simpa only [F,Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,
    max_eq_left (norm_nonneg _)] using hh

theorem poissonIntegralFour_hessian_universal_lipschitz :
    ∃ L > 0, ∀ f : S → ℝ, Continuous f → (∀ ξ, |f ξ| ≤ 1) →
      ∀ x ∈ closedBall (0 : E) (1/2 : ℝ),
      ∀ y ∈ closedBall (0 : E) (1/2 : ℝ),
        ‖realHessian (poissonIntegralFour unitSphereProbabilityFour f) x-
          realHessian (poissonIntegralFour unitSphereProbabilityFour f) y‖ ≤ L*‖x-y‖ := by
  obtain ⟨L,hL,hK⟩ := poissonKernelFour_hessian_universal_lipschitz
  refine ⟨L,hL,?_⟩
  intro f hf hfb x hx y hy
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
      f ξ • realHessian (poissonKernelFour ξ) y‖ ≤ L*‖x-y‖ := by
    have he : f ξ • realHessian (poissonKernelFour ξ) x-
        f ξ • realHessian (poissonKernelFour ξ) y =
        f ξ • (realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y) := by
      ext v w
      simp only [_root_.smul_apply,ContinuousLinearMap.sub_apply,smul_eq_mul,mul_sub]
    rw [he,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ 1*‖realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y‖ :=
        mul_le_mul_of_nonneg_right (hfb ξ)
          (norm_nonneg (realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y))
      _ ≤ L*‖x-y‖ := by simpa only [one_mul] using hK x hx y hy ξ
  simpa using norm_integral_le_of_norm_le_const
    (μ := unitSphereProbabilityFour) (Filter.Eventually.of_forall hb)

theorem classical_harmonic_unitBall_hessian_universal_lipschitz_four :
    ∃ L > 0, ∀ g : E → ℝ, ContinuousOn g (closedBall 0 1) →
      InnerProductSpace.HarmonicOnNhd g (ball 0 1) →
      (∀ x ∈ closedBall (0 : E) 1, |g x| ≤ 1) →
      ∀ x ∈ closedBall (0 : E) (1/2 : ℝ),
      ∀ y ∈ closedBall (0 : E) (1/2 : ℝ),
        ‖realHessian g x-realHessian g y‖ ≤ L*‖x-y‖ := by
  obtain ⟨L,hL,hP⟩ := poissonIntegralFour_hessian_universal_lipschitz
  refine ⟨L,hL,?_⟩
  intro g hgc hg hgb x hx y hy
  have hxB : x ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by norm_num))
  have hyB : y ∈ ball (0 : E) 1 := mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by norm_num))
  rw [classical_harmonic_unitBall_hessian_eq_poisson_four hgc hg hxB,
    classical_harmonic_unitBall_hessian_eq_poisson_four hgc hg hyB]
  exact hP (fun ξ : S => g ξ)
    (continuousOn_iff_continuous_domRestrict.mp (hgc.mono sphere_subset_closedBall))
    (fun ξ => hgb ξ (sphere_subset_closedBall ξ.property)) x hx y hy

end PowerConvexity
