import PowerConvexity.Analysis.ActualCofactorFirstVariationTwo
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Uniform actual Holder loads for the first cofactor variation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_distance_le_holder_power_two
    {d D alpha : ℝ} (hd : 0 ≤ d) (hD : d ≤ D) (halpha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    d ≤ max 1 D*d^alpha := by
  have hp : 0 ≤ d^alpha := Real.rpow_nonneg hd _
  by_cases hd1 : d ≤ 1
  · exact (Real.self_le_rpow_of_le_one hd hd1 ha1).trans
      (le_mul_of_one_le_left hp (le_max_left _ _))
  · have hp1 : 1 ≤ d^alpha := Real.one_le_rpow (le_of_lt (lt_of_not_ge hd1)) halpha
    exact hD.trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right (by positivity) hp1))

theorem actual_unit_directional_density_source_bounds_two
    {U : Set E} (hU : IsOpen U) {rho : E → ℝ} (hrho : ContDiffOn ℝ 2 rho U)
    {x₀ : E} {r c D₁ D₂ alpha : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hsub : ball x₀ (2*r) ⊆ U)
    (hfirst : ∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ D₁)
    (hsecond : ∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂)
    (v : E) (hv : ‖v‖ ≤ 1) :
    ContDiffOn ℝ 1 (fun x => -(c⁻¹*fderiv ℝ rho x v)) U ∧
      (∀ x ∈ U, |-(c⁻¹*fderiv ℝ rho x v)| ≤ c⁻¹*D₁) ∧
      ∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
        |-(c⁻¹*fderiv ℝ rho x v)-(-(c⁻¹*fderiv ℝ rho y v))| ≤
          (c⁻¹*D₂*max 1 (4*r))*‖x-y‖^alpha := by
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ rho) U :=
    hrho.fderiv_of_isOpen hU (m := 1) (by norm_num)
  refine ⟨(contDiffOn_const.mul (hDf.clm_apply contDiffOn_const)).neg,?_,?_⟩
  · intro x hx
    rw [abs_neg,abs_mul,abs_of_pos (inv_pos.mpr hc)]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hc).le
    have hh := (fderiv ℝ rho x).le_opNorm v
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((mul_le_mul (hfirst x hx) hv (norm_nonneg _) hD₁).trans_eq (mul_one _))
  · intro x hx y hy
    have hLip : ‖fderiv ℝ rho x-fderiv ℝ rho y‖ ≤ D₂*‖x-y‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => (hDf.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num))
        (fun z hz => hsecond z (hsub hz)) (convex_ball x₀ (2*r)) hy hx
    have hval : |fderiv ℝ rho x v-fderiv ℝ rho y v| ≤ D₂*‖x-y‖ := by
      have hh := (fderiv ℝ rho x-fderiv ℝ rho y).le_opNorm v
      change ‖fderiv ℝ rho x v-fderiv ℝ rho y v‖ ≤ _ at hh
      rw [Real.norm_eq_abs] at hh
      exact hh.trans ((mul_le_of_le_one_right (norm_nonneg _) hv).trans hLip)
    have hdist : ‖x-y‖ ≤ 4*r := by
      have ht := dist_triangle x x₀ y
      have hx0 : dist x x₀ < 2*r := hx
      have hy0 : dist y x₀ < 2*r := hy
      rw [dist_comm x₀ y,dist_eq_norm x y] at ht
      linarith
    have hpow := actual_distance_le_holder_power_two (norm_nonneg (x-y)) hdist halpha.le ha1
    have he : -(c⁻¹*fderiv ℝ rho x v)-(-(c⁻¹*fderiv ℝ rho y v)) =
        -(c⁻¹*(fderiv ℝ rho x v-fderiv ℝ rho y v)) := by ring
    rw [he,abs_neg,abs_mul,abs_of_pos (inv_pos.mpr hc)]
    exact (mul_le_mul_of_nonneg_left
      (hval.trans (mul_le_mul_of_nonneg_left hpow hD₂)) (inv_pos.mpr hc).le).trans_eq (by ring)

end PowerConvexity
