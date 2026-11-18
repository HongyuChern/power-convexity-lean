import PowerConvexity.Analysis.ActualCofactorSecondVariationTwo
import PowerConvexity.Analysis.ActualDirectionalSourceBoundsTwo

/-! # Uniform size and Holder bounds for the actual second-variation source -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_bilinear_unit_value_bound_two
    (H : E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (hH : ‖H‖ ≤ M)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : |H v w| ≤ M := by
  have hh := H.le_opNorm₂ v w
  rw [Real.norm_eq_abs] at hh
  exact hh.trans ((mul_le_mul
    (mul_le_mul hH hv (norm_nonneg _) hM) hw (norm_nonneg _)
      (mul_nonneg hM zero_le_one)).trans_eq (by ring))

theorem actual_Hessian_holder_from_third_bound_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    {x₀ : E} {r M alpha : ℝ} (hM : 0 ≤ M) (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hsub : ball x₀ (2*r) ⊆ U)
    (hthird : ∀ x ∈ U, ‖fderiv ℝ (realHessian u) x‖ ≤ M) :
    ∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
      ‖realHessian u x-realHessian u y‖ ≤ (M*max 1 (4*r))*‖x-y‖^alpha := by
  have hH : ContDiffOn ℝ 1 (realHessian u) U :=
    (hu.fderiv_of_isOpen hU (m := 2) (by norm_num)).fderiv_of_isOpen hU (m := 1) (by norm_num)
  intro x hx y hy
  have hlip : ‖realHessian u x-realHessian u y‖ ≤ M*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hH.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num))
      (fun z hz => hthird z (hsub hz)) (convex_ball x₀ (2*r)) hy hx
  have hdist : ‖x-y‖ ≤ 4*r := by
    have ht := dist_triangle x x₀ y
    have hx0 : dist x x₀ < 2*r := hx
    have hy0 : dist y x₀ < 2*r := hy
    rw [dist_comm x₀ y,dist_eq_norm x y] at ht
    linarith
  exact (hlip.trans (mul_le_mul_of_nonneg_left
    (actual_distance_le_holder_power_two (norm_nonneg _) hdist halpha.le ha1) hM)).trans_eq (by ring)

theorem actual_unit_second_variation_source_bounds_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 3 rho U)
    {x₀ : E} {r c M K D₂ D₃ alpha : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hK : 0 ≤ K) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hsub : ball x₀ (2*r) ⊆ U)
    (hthird : ∀ x ∈ U, ‖fderiv ℝ (realHessian u) x‖ ≤ M)
    (hhold : ∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
      ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ K*‖x-y‖^alpha)
    (hsecond : ∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂)
    (hthirdrho : ∀ x ∈ U, ‖fderiv ℝ (realHessian rho) x‖ ≤ D₃)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ContDiffOn ℝ 1 (actualCofactorSecondSourceTwo u rho c v w) U ∧
      (∀ x ∈ U, |actualCofactorSecondSourceTwo u rho c v w x| ≤
        c⁻¹*D₂+c⁻¹*(16*‖actualCofactorMatrixFormTwo‖*M^2)) ∧
      ∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
        |actualCofactorSecondSourceTwo u rho c v w x-
          actualCofactorSecondSourceTwo u rho c v w y| ≤
          (c⁻¹*D₃*max 1 (4*r)+c⁻¹*(32*‖actualCofactorMatrixFormTwo‖*M*K))*‖x-y‖^alpha := by
  refine ⟨actual_cofactor_second_source_C1_two hU hu hrho c v w,?_,?_⟩
  · intro x hx
    unfold actualCofactorSecondSourceTwo
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg,abs_mul,abs_of_pos (inv_pos.mpr hc)]
      exact mul_le_mul_of_nonneg_left
        (actual_bilinear_unit_value_bound_two _ hD₂ (hsecond x hx) w v hw hv) (inv_pos.mpr hc).le
    · rw [abs_mul,abs_of_pos (inv_pos.mpr hc)]
      exact mul_le_mul_of_nonneg_left
        (actual_cofactor_third_correction_bound_two _ hM (hthird x hx) v w hv hw) (inv_pos.mpr hc).le
  · intro x hx y hy
    have hrhold := actual_Hessian_holder_from_third_bound_two hU hrho hD₃ halpha ha1 hsub hthirdrho x hx y hy
    have hR : |realHessian rho x w v-realHessian rho y w v| ≤
        (D₃*max 1 (4*r))*‖x-y‖^alpha := by
      exact actual_bilinear_unit_value_bound_two (realHessian rho x-realHessian rho y)
        (by positivity) hrhold w v hw hv
    have hC := (actual_cofactor_third_correction_difference_two
      (fderiv ℝ (realHessian u) x) (fderiv ℝ (realHessian u) y) hM
      (hthird x (hsub hx)) (hthird y (hsub hy)) v w hv hw).trans
        (mul_le_mul_of_nonneg_left (hhold x hx y hy) (by positivity))
    have he : actualCofactorSecondSourceTwo u rho c v w x-
        actualCofactorSecondSourceTwo u rho c v w y =
      -(c⁻¹*(realHessian rho x w v-realHessian rho y w v))+
        c⁻¹*(actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w-
          actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) y) v w) := by
      unfold actualCofactorSecondSourceTwo
      ring
    rw [he]
    calc
      _ ≤ |-(c⁻¹*(realHessian rho x w v-realHessian rho y w v))|+
        |c⁻¹*(actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w-
          actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) y) v w)| := abs_add_le _ _
      _ = c⁻¹*|realHessian rho x w v-realHessian rho y w v|+
        c⁻¹*|actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w-
          actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) y) v w| := by
        rw [abs_neg,abs_mul,abs_mul,abs_of_pos (inv_pos.mpr hc)]
      _ ≤ c⁻¹*((D₃*max 1 (4*r))*‖x-y‖^alpha)+
        c⁻¹*(32*‖actualCofactorMatrixFormTwo‖*M*(K*‖x-y‖^alpha)) :=
        add_le_add (mul_le_mul_of_nonneg_left hR (inv_pos.mpr hc).le)
          (mul_le_mul_of_nonneg_left hC (inv_pos.mpr hc).le)
      _ = _ := by ring

end PowerConvexity
