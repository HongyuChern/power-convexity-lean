import PowerConvexity.Analysis.ActualUniformQuadraticJetScaleTwo
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # Exact Holder control from geometric actual quadratic expansions

The two-centre estimate permits an arbitrary nonnegative amplitude.  Choosing
that amplitude as the spatial ratio to alpha gives the same exponent alpha.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_family_quadratic_two_center_geometric_two :
    ∃ J > 0, ∀ (U V : Set E) (u : E → ℝ),
    MemLp u 2 (volume.restrict U) →
    ∀ P : E → E → ℝ, (∀ x ∈ V, IsQuadraticPolynomial (P x)) →
    ∀ R theta omega C : ℝ, 0 < R → 0 < theta → theta ≤ 1 → 0 ≤ omega → 0 ≤ C →
    (∀ x ∈ V, ball x R ⊆ U) →
    (∀ x ∈ V, ∀ n : ℕ,
      (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
        C*(omega^n)^2*(R*theta^n)^8) →
    ∀ x ∈ V, ∀ y ∈ V, ∀ n : ℕ,
      dist x y ≤ R*theta^n/2 →
      |P x y-P y y| ≤ J*Real.sqrt C*omega^n*(R*theta^n/2)^2 ∧
      ‖fderiv ℝ (P x) y-fderiv ℝ (P y) y‖ ≤ J*Real.sqrt C*omega^n*(R*theta^n/2) ∧
      ‖realHessian (P x) x-realHessian (P y) y‖ ≤ J*Real.sqrt C*omega^n := by
  obtain ⟨J,hJ,hcompare⟩ := actual_quadratic_two_center_jet_comparison_two
  refine ⟨16*J,by positivity,?_⟩
  intro U V u hu P hP R theta omega C hR htheta htheta1 homega hC hballs herr x hx y hy n hxy
  let r := R*theta^n/2
  let a := 16*Real.sqrt C*omega^n
  have hr : 0 < r := by dsimp [r]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have htwo : 2*r = R*theta^n := by dsimp [r]; ring
  have hscale : a^2*r^8 = C*(omega^n)^2*(R*theta^n)^8 := by
    dsimp [a,r]
    rw [mul_pow,mul_pow,Real.sq_sqrt hC]
    ring
  have hpow : R*theta^n ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ htheta.le htheta1)
  have hux : MemLp u 2 (volume.restrict (ball x (2*r))) := by
    rw [htwo]
    exact hu.mono_measure (Measure.restrict_mono
      ((ball_subset_ball hpow).trans (hballs x hx)) le_rfl)
  have huy : MemLp u 2 (volume.restrict (ball y (R*theta^n))) :=
    hu.mono_measure (Measure.restrict_mono
      ((ball_subset_ball hpow).trans (hballs y hy)) le_rfl)
  have hpy := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff (hP y hy) 0).continuous
    y (R*theta^n)
  have hyI : Integrable (fun z => (u z-P y z)^2) (volume.restrict (ball y (R*theta^n))) :=
    (huy.sub hpy).integrable_sq
  have hysub : ball y r ⊆ ball y (R*theta^n) := ball_subset_ball (by dsimp [r]; nlinarith [mul_pos hR (pow_pos htheta n)])
  have hyerr : (∫ z in ball y r, (u z-P y z)^2) ≤ a^2*r^8 := by
    rw [hscale]
    exact (setIntegral_mono_set hyI (Eventually.of_forall (fun z => sq_nonneg (u z-P y z)))
      (Eventually.of_forall (fun z hz => hysub hz))).trans (herr y hy n)
  have hxerr : (∫ z in ball x (2*r), (u z-P x z)^2) ≤ a^2*(2*r)^8 := by
    rw [htwo]
    apply (herr x hx n).trans
    have hcoef : C*(omega^n)^2 ≤ a^2 := by
      dsimp [a]
      rw [mul_pow,mul_pow,Real.sq_sqrt hC]
      nlinarith [mul_nonneg hC (sq_nonneg (omega^n))]
    exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg (mul_nonneg hR.le (pow_nonneg htheta.le n)) 8)
  have hb := hcompare u (P x) (P y) (hP x hx) (hP y hy) x y r a hr hxy ha hux hxerr hyerr
  simpa only [a,r,mul_assoc,mul_comm,mul_left_comm] using hb



theorem actual_geometric_radius_prescribed_holder_select_two
    {R theta alpha d : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1)
    (halpha : 0 ≤ alpha) (hd : 0 < d) (hsmall : d < R/2) :
    ∃ k : ℕ, d ≤ R*theta^k/2 ∧
      (theta^alpha)^k ≤ (2/(R*theta))^alpha*d^alpha := by
  obtain ⟨k,hlo,hhi⟩ := actual_geometric_half_radius_select_two hR htheta htheta1 0 hd
    (by simpa only [pow_zero,mul_one] using hsmall)
  simp only [zero_add] at hlo hhi
  have hkn : theta^k ≤ (2/(R*theta))*d := by
    have hhi' := (lt_div_iff₀ htheta).mp hhi
    have hh : theta^k ≤ (2*d)/(R*theta) := by
      apply (le_div_iff₀ (mul_pos hR htheta)).mpr
      nlinarith
    exact hh.trans_eq (by ring)
  refine ⟨k,hlo,?_⟩
  calc
    (theta^alpha)^k = (theta^k)^alpha := (actual_nat_power_rpow_comm_two htheta.le alpha k).symm
    _ ≤ ((2/(R*theta))*d)^alpha := Real.rpow_le_rpow (pow_nonneg htheta.le k) hkn halpha
    _ = (2/(R*theta))^alpha*d^alpha := Real.mul_rpow (by positivity) hd.le

theorem actual_family_quadratic_Hessian_prescribed_holder_two
    {R theta C alpha : ℝ} (hR : 0 < R) (htheta : 0 < theta)
    (htheta1 : theta < 1) (hC : 0 ≤ C) (halpha : 0 ≤ alpha) :
    ∃ H ≥ 0,
      ∀ (U V : Set E) (u : E → ℝ), MemLp u 2 (volume.restrict U) →
      ∀ P : E → E → ℝ, (∀ x ∈ V, IsQuadraticPolynomial (P x)) →
      (∀ x ∈ V, ball x R ⊆ U) →
      (∀ x ∈ V, ∀ n : ℕ,
        (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
          C*((theta^alpha)^n)^2*(R*theta^n)^8) →
      ∀ x ∈ V, ∀ y ∈ V, dist x y < R/2 →
        ‖realHessian (P x) x-realHessian (P y) y‖ ≤ H*‖x-y‖^alpha := by
  obtain ⟨J,hJ,hscale⟩ := actual_family_quadratic_two_center_geometric_two
  let H := J*Real.sqrt C*(2/(R*theta))^alpha
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H,hH,?_⟩
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
  obtain ⟨n,hn,hpow⟩ := actual_geometric_radius_prescribed_holder_select_two hR htheta htheta1
    halpha hd (by simpa only [dist_eq_norm] using hnear)
  have hh := (hscale U V u hu P hP R theta (theta^alpha) C hR htheta htheta1.le (Real.rpow_nonneg htheta.le _) hC hballs herr
    x hx y hy n (by simpa only [dist_eq_norm] using hn)).2.2
  exact hh.trans ((mul_le_mul_of_nonneg_left hpow
    (mul_nonneg hJ.le (Real.sqrt_nonneg C))).trans_eq (by dsimp [H]; ring))


end PowerConvexity
