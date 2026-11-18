import PowerConvexity.Analysis.ActualQuadraticTwoCenterJetsTwo

/-! # Absolute quadratic jets bounded before the actual solution -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_family_quadratic_absolute_jet_bound_two
    {R C N : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hN : 0 ≤ N) :
    ∃ T ≥ 0, ∀ (U : Set E) (u : E → ℝ),
      ∀ hu : MemLp u 2 (volume.restrict U), ‖hu.toLp u‖ ≤ N →
      ∀ (x : E) (p : E → ℝ), IsQuadraticPolynomial p → ball x R ⊆ U →
      (∫ y in ball x R, (u y-p y)^2) ≤ C*R^8 →
      |p x| ≤ T ∧ ‖fderiv ℝ p x‖ ≤ T ∧ ‖realHessian p x‖ ≤ T := by
  obtain ⟨J,hJ,hjets⟩ := actual_quadratic_scaled_L2_jet_bound_at_two
  let a := Real.sqrt ((2*C*R^8+2*N^2)/R^8)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2*R^8 = 2*C*R^8+2*N^2 := by
    rw [show a^2 = (2*C*R^8+2*N^2)/R^8 from Real.sq_sqrt (by positivity)]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hR.ne')
  let T := J*a*(R^2+R+1)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨T,hT,?_⟩
  intro U u hu hun x p hp hsub herr
  have hub := hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpb := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous x R
  have hI : (∫ y in ball x R, (u y)^2) ≤ N^2 := by
    have hm := setIntegral_mono_set hu.integrable_sq
      (Eventually.of_forall (fun y => sq_nonneg (u y)))
      (Eventually.of_forall (fun y hy => hsub hy))
    have hn : (∫ y in U, (u y)^2) ≤ N^2 := by
      rw [← actual_scalar_L2_norm_squared_two hu]
      exact (sq_le_sq₀ (norm_nonneg _) hN).mpr hun
    exact hm.trans hn
  have hpI : (∫ y in ball x R, (p y)^2) ≤ a^2*R^8 := by
    have huI := hub.integrable_sq
    have heI : Integrable (fun y => (u y-p y)^2) (volume.restrict (ball x R)) := by
      simpa only [Pi.sub_apply] using (hub.sub hpb).integrable_sq
    have hh : (∫ y in ball x R, (p y)^2) ≤
        ∫ y in ball x R, 2*(u y-p y)^2+2*(u y)^2 := by
      apply integral_mono_ae hpb.integrable_sq ((heI.const_mul 2).add (huI.const_mul 2))
      filter_upwards with y
      change (p y)^2 ≤ 2*(u y-p y)^2+2*(u y)^2
      nlinarith [sq_nonneg (2*u y-p y)]
    rw [integral_add (heI.const_mul 2) (huI.const_mul 2),integral_const_mul,integral_const_mul] at hh
    rw [ha2]
    exact hh.trans (by linarith)
  obtain ⟨hv,hD,hH⟩ := hjets p hp x R hR a ha hpI
  refine ⟨hv.trans ?_,hD.trans ?_,hH.trans ?_⟩
  · change J*a*R^2 ≤ J*a*(R^2+R+1)
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hJ.le ha)
  · change J*a*R ≤ J*a*(R^2+R+1)
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg R]) (mul_nonneg hJ.le ha)
  · exact le_mul_of_one_le_right (mul_nonneg hJ.le ha) (by nlinarith [sq_nonneg R])

end PowerConvexity
