import PowerConvexity.Analysis.ActualUniformQuadraticJetScaleTwo
import PowerConvexity.Analysis.ActualPolynomialFieldC2EpsilonTwo

/-! # Actual uniform L2 errors imply two-centre jet compatibility

The distance selects a geometric scale after an arbitrarily late iteration
index. This removes the approximation error relative to the distance itself,
including for the first derivative; fixed-scale continuity alone is not used.
-/
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

theorem actual_bilinear_opNorm_sub_reverse_two (A B : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖A-B‖ = ‖B-A‖ := by
  have he : A-B = -(B-A) := by
    ext v w
    change A v w-B v w = -(B v w-A v w)
    ring
  rw [he,ContinuousLinearMap.opNorm_neg]

theorem actual_uniform_quadratic_two_center_compatibility_two
    {U V : Set E} {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (P : E → E → ℝ) (hP : ∀ x ∈ V, IsQuadraticPolynomial (P x))
    {R theta C : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) (hC : 0 ≤ C)
    (hballs : ∀ x ∈ V, ball x R ⊆ U)
    (herr : ∀ x ∈ V, ∀ n : ℕ,
      (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ x ∈ V, ∀ y ∈ V, dist y x < delta →
      |P y y-P x y| ≤ epsilon*‖y-x‖^2 ∧
      ‖fderiv ℝ (P y) y-fderiv ℝ (P x) y‖ ≤ epsilon*‖y-x‖ ∧
      ‖realHessian (P y) y-realHessian (P x) x‖ ≤ epsilon := by
  obtain ⟨J,hJ,hscale⟩ := actual_uniform_quadratic_two_center_at_scale_two hu P hP
    hR htheta htheta1.le hC hballs herr
  let D : ℝ := 1/theta
  have hD : 0 < D := div_pos zero_lt_one htheta
  have hD1 : 1 ≤ D := by
    apply (le_div_iff₀ htheta).mpr
    simpa only [one_mul] using htheta1.le
  have hDD : D ≤ D^2 := by nlinarith
  have hD2 : 1 ≤ D^2 := hD1.trans hDD
  let L : ℝ := J*Real.sqrt C*D^2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlim : Tendsto (fun n : ℕ => L*(1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)))
  intro epsilon hepsilon
  obtain ⟨N,hN⟩ := (hlim.eventually (gt_mem_nhds hepsilon)).exists
  refine ⟨R*theta^N/2,by positivity,?_⟩
  intro x hx y hy hnear
  by_cases hyx : y = x
  · subst y
    simp only [sub_self,abs_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
    refine ⟨le_rfl,le_rfl,?_⟩
    have he : realHessian (P x) x-realHessian (P x) x = 0 := by
      ext v w
      change realHessian (P x) x v w-realHessian (P x) x v w = 0
      ring
    rw [he,ContinuousLinearMap.opNorm_zero]
    exact hepsilon.le
  have hd : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hnear' : ‖y-x‖ < R*theta^N/2 := by simpa only [dist_eq_norm] using hnear
  obtain ⟨k,hlo,hhi⟩ := actual_geometric_half_radius_select_two hR htheta htheta1 N hd hnear'
  let r := R*theta^(N+k)/2
  let a := J*Real.sqrt C*(1/2 : ℝ)^(N+k)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hxy : dist x y ≤ R*theta^(N+k)/2 := by
    simpa only [dist_comm x y,dist_eq_norm] using hlo
  have hrd : r ≤ D*‖y-x‖ := by
    exact hhi.le.trans_eq (by dsimp [D]; ring)
  have hpow : (1/2 : ℝ)^(N+k) ≤ (1/2 : ℝ)^N := by
    rw [pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hacoef : a*D^2 ≤ epsilon := by
    calc
      a*D^2 = L*(1/2 : ℝ)^(N+k) := by dsimp [a,L]; ring
      _ ≤ L*(1/2 : ℝ)^N := mul_le_mul_of_nonneg_left hpow hL
      _ ≤ epsilon := hN.le
  obtain ⟨hv,hg,hH⟩ := hscale x hx y hy (N+k) hxy
  change |P x y-P y y| ≤ a*r^2 at hv
  change ‖fderiv ℝ (P x) y-fderiv ℝ (P y) y‖ ≤ a*r at hg
  change ‖realHessian (P x) x-realHessian (P y) y‖ ≤ a at hH
  refine ⟨?_,?_,?_⟩
  · rw [abs_sub_comm]
    calc
      _ ≤ a*r^2 := hv
      _ ≤ a*(D*‖y-x‖)^2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hr.le (mul_nonneg hD.le (norm_nonneg _))).mpr hrd) ha
      _ = (a*D^2)*‖y-x‖^2 := by ring
      _ ≤ epsilon*‖y-x‖^2 := mul_le_mul_of_nonneg_right hacoef (sq_nonneg _)
  · rw [norm_sub_rev]
    calc
      _ ≤ a*r := hg
      _ ≤ a*(D*‖y-x‖) := mul_le_mul_of_nonneg_left hrd ha
      _ ≤ a*(D^2*‖y-x‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hDD (norm_nonneg _)) ha
      _ = (a*D^2)*‖y-x‖ := by ring
      _ ≤ epsilon*‖y-x‖ := mul_le_mul_of_nonneg_right hacoef (norm_nonneg _)
  · rw [actual_bilinear_opNorm_sub_reverse_two]
    exact hH.trans ((le_mul_of_one_le_right ha hD2).trans hacoef)

theorem actual_polynomial_field_C2_of_uniform_L2_expansion_two
    {U V : Set E} (hV : IsOpen V) {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (P : E → E → ℝ) (hP : ∀ x ∈ V, IsQuadraticPolynomial (P x))
    {R theta C : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) (hC : 0 ≤ C)
    (hballs : ∀ x ∈ V, ball x R ⊆ U)
    (herr : ∀ x ∈ V, ∀ n : ℕ,
      (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) :
    ContDiffOn ℝ 2 (fun x => P x x) V ∧
      (∀ x ∈ V, fderiv ℝ (fun y => P y y) x = fderiv ℝ (P x) x) ∧
      ∀ x ∈ V, realHessian (fun y => P y y) x = realHessian (P x) x := by
  apply actual_polynomial_field_C2_of_two_center_epsilon_two hV P hP
  intro x hx epsilon hepsilon
  obtain ⟨delta,hd,hb⟩ := actual_uniform_quadratic_two_center_compatibility_two hu P hP
    hR htheta htheta1 hC hballs herr epsilon hepsilon
  exact ⟨delta,hd,fun y hy hnear => hb x hx y hy hnear⟩

end PowerConvexity
