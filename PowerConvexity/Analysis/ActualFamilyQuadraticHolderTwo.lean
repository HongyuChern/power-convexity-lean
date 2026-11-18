import PowerConvexity.Analysis.ActualFamilyQuadraticJetScaleTwo
import PowerConvexity.Analysis.ActualUniformQuadraticJetCompatibilityTwo
import PowerConvexity.Analysis.ActualQuadraticAverageIdentificationTwo
import CHS.Calculus.HessianLocality

/-! # Quantitative Holder Hessian control from the actual L2 expansions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_family_quadratic_Hessian_holder_two
    {R theta C : ℝ} (hR : 0 < R) (htheta : 0 < theta)
    (htheta1 : theta < 1) (hC : 0 ≤ C) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ H ≥ 0,
      ∀ (U V : Set E) (u : E → ℝ), MemLp u 2 (volume.restrict U) →
      ∀ P : E → E → ℝ, (∀ x ∈ V, IsQuadraticPolynomial (P x)) →
      (∀ x ∈ V, ball x R ⊆ U) →
      (∀ x ∈ V, ∀ n : ℕ,
        (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
          C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) →
      ∀ x ∈ V, ∀ y ∈ V, dist x y < R/2 →
        ‖realHessian (P x) x-realHessian (P y) y‖ ≤ H*‖x-y‖^beta := by
  obtain ⟨J,hJ,hscale⟩ := actual_family_quadratic_two_center_at_scale_two
  obtain ⟨beta,hbeta,hbeta1,hdecay⟩ := actual_half_decay_exponent_two htheta htheta1
  let H := J*Real.sqrt C*(2/(R*theta))^beta
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨beta,hbeta,hbeta1,H,hH,?_⟩
  intro U V u hu P hP hballs herr x hx y hy hnear
  by_cases hxy : x = y
  · subst y
    have he : realHessian (P x) x-realHessian (P x) x = 0 := by
      ext v w
      change realHessian (P x) x v w-realHessian (P x) x v w = 0
      ring
    rw [he,ContinuousLinearMap.opNorm_zero]
    exact mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨n,hn,hpow⟩ := actual_geometric_half_radius_holder_select_two hR htheta htheta1
    hbeta.le hdecay hd (by simpa only [dist_eq_norm] using hnear)
  have hh := (hscale U V u hu P hP R theta C hR htheta htheta1.le hC hballs herr
    x hx y hy n (by simpa only [dist_eq_norm] using hn)).2.2
  exact hh.trans ((mul_le_mul_of_nonneg_left hpow
    (mul_nonneg hJ.le (Real.sqrt_nonneg C))).trans_eq (by dsimp [H]; ring))

theorem actual_continuous_polynomial_field_jets_identify_two
    {U V : Set E} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVU : V ⊆ U)
    {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U)) (huC : ContinuousOn u V)
    (P : E → E → ℝ) (hP : ∀ x ∈ V, IsQuadraticPolynomial (P x))
    {R theta C : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) (hC : 0 ≤ C)
    (hballs : ∀ x ∈ V, ball x R ⊆ U)
    (herr : ∀ x ∈ V, ∀ n : ℕ,
      (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) :
    ContDiffOn ℝ 2 u V ∧ ∀ x ∈ V,
      u x = P x x ∧ fderiv ℝ u x = fderiv ℝ (P x) x ∧
        realHessian u x = realHessian (P x) x := by
  have hfield := actual_polynomial_field_C2_of_uniform_L2_expansion_two hV hu P hP
    hR htheta htheta1 hC hballs herr
  have hae := actual_polynomial_field_ae_eq_of_uniform_L2_two hV hVb hVU hu P hP
    hR htheta htheta1 hC hballs herr
  have heq := Measure.eqOn_open_of_ae_eq hae hV hfield.1.continuousOn huC
  have hloc (x : E) (hx : x ∈ V) : u =ᶠ[𝓝 x] (fun y => P y y) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (heq hy).symm
  refine ⟨?_,?_⟩
  · intro x hx
    exact ((hfield.1.contDiffAt (hV.mem_nhds hx)).congr_of_eventuallyEq
      (hloc x hx)).contDiffWithinAt
  · intro x hx
    exact ⟨(heq hx).symm,(hloc x hx).fderiv_eq.trans (hfield.2.1 x hx),
      (realHessian_eq_of_eventuallyEq (hloc x hx)).trans (hfield.2.2 x hx)⟩

end PowerConvexity
