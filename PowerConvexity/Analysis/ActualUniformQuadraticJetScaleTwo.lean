import PowerConvexity.Analysis.ActualGeometricScaleSelectionTwo

/-! # Two-centre jets from one uniform physical L2 approximation family -/
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

theorem actual_uniform_quadratic_two_center_at_scale_two
    {U V : Set E} {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (P : E → E → ℝ) (hP : ∀ x ∈ V, IsQuadraticPolynomial (P x))
    {R theta C : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hC : 0 ≤ C)
    (hballs : ∀ x ∈ V, ball x R ⊆ U)
    (herr : ∀ x ∈ V, ∀ n : ℕ,
      (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) :
    ∃ J > 0, ∀ x ∈ V, ∀ y ∈ V, ∀ n : ℕ,
      dist x y ≤ R*theta^n/2 →
      |P x y-P y y| ≤ J*Real.sqrt C*(1/2 : ℝ)^n*(R*theta^n/2)^2 ∧
      ‖fderiv ℝ (P x) y-fderiv ℝ (P y) y‖ ≤ J*Real.sqrt C*(1/2 : ℝ)^n*(R*theta^n/2) ∧
      ‖realHessian (P x) x-realHessian (P y) y‖ ≤ J*Real.sqrt C*(1/2 : ℝ)^n := by
  obtain ⟨J,hJ,hcompare⟩ := actual_quadratic_two_center_jet_comparison_two
  refine ⟨16*J,by positivity,?_⟩
  intro x hx y hy n hxy
  let r := R*theta^n/2
  let a := 16*Real.sqrt C*(1/2 : ℝ)^n
  have hr : 0 < r := by dsimp [r]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have htwo : 2*r = R*theta^n := by dsimp [r]; ring
  have hscale : a^2*r^8 = C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
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
    have hcoef : C*((1/2 : ℝ)^n)^2 ≤ a^2 := by
      dsimp [a]
      rw [mul_pow,mul_pow,Real.sq_sqrt hC]
      nlinarith [mul_nonneg hC (sq_nonneg ((1/2 : ℝ)^n))]
    exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg (mul_nonneg hR.le (pow_nonneg htheta.le n)) 8)
  have hb := hcompare u (P x) (P y) (hP x hx) (hP y hy) x y r a hr hxy ha hux hxerr hyerr
  simpa only [a,r,mul_assoc,mul_comm,mul_left_comm] using hb

end PowerConvexity
