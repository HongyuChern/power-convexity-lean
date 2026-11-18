import PowerConvexity.Analysis.ActualScalarPrescribedHolderSequenceTwo
import PowerConvexity.Analysis.ActualScalarQuadraticLimitErrorTwo

/-! # Actual interior quadratic limits with arbitrary geometric amplitude

All tails retain the amplitude theta^n and the two, one, or zero powers of
spatial radius needed for the value, first derivative, and Hessian.  The weak
L2 error has its actual four-dimensional scaling.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_geometric_jet_limits_two
    {M r theta : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (htheta : 0 ≤ theta) (htheta2 : theta ≤ (1/2 : ℝ))
    {Q : ℕ → E → ℝ}
    (hi : ∀ n, ActualScalarGeometricIncrementTwo M r theta n (Q n) (Q (n+1))) :
    ∃ (c : ℝ) (l : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ),
      Tendsto (fun n => Q n 0) atTop (𝓝 c) ∧
      Tendsto (fun n => fderiv ℝ (Q n) 0) atTop (𝓝 l) ∧
      Tendsto (fun n => realHessian (Q n) 0) atTop (𝓝 H) ∧
      (∀ n, |Q n 0-c| ≤ 2*M*theta^n*(r^n)^2) ∧
      (∀ n, ‖fderiv ℝ (Q n) 0-l‖ ≤ 2*M*theta^n*r^n) ∧
      (∀ n, ‖realHessian (Q n) 0-H‖ ≤ 2*M*theta^n) := by
  have hr2 : r^2 ≤ 1 := by nlinarith
  have he0 (n : ℕ) : (theta*r^2)^n = theta^n*(r^n)^2 := by
    rw [mul_pow,← pow_mul, Nat.mul_comm 2 n,pow_mul]
  have he1 (n : ℕ) : (theta*r)^n = theta^n*r^n := mul_pow _ _ _
  have hi0 (n : ℕ) : ‖Q (n+1) 0-Q n 0‖ ≤ M*(theta*r^2)^n := by
    rw [Real.norm_eq_abs,he0]
    exact (hi n).1.trans_eq (by ring)
  have hi1 (n : ℕ) : ‖fderiv ℝ (Q (n+1)) 0-fderiv ℝ (Q n) 0‖ ≤ M*(theta*r)^n := by
    rw [he1]
    exact (hi n).2.1.trans_eq (by ring)
  have hi2 (n : ℕ) : ‖realHessian (Q (n+1)) 0-realHessian (Q n) 0‖ ≤ M*theta^n := by
    exact ((hi n).2.2 0).trans_eq (mul_comm _ _)
  obtain ⟨c,hc,hcB⟩ := actual_geometric_increment_limit (X := ℝ) (v := fun n => Q n 0) hM (mul_nonneg htheta (sq_nonneg r))
    ((mul_le_mul_of_nonneg_left hr2 htheta).trans (by simpa only [mul_one] using htheta2)) hi0
  obtain ⟨l,hl,hlB⟩ := actual_geometric_increment_limit (X := E →L[ℝ] ℝ) (v := fun n => fderiv ℝ (Q n) 0) hM (mul_nonneg htheta hr)
    ((mul_le_mul_of_nonneg_left hr1 htheta).trans (by simpa only [mul_one] using htheta2)) hi1
  obtain ⟨H,hH,hHB⟩ := actual_geometric_increment_limit (X := E →L[ℝ] E →L[ℝ] ℝ) (v := fun n => realHessian (Q n) 0) hM htheta htheta2 hi2
  refine ⟨c,l,H,hc,hl,hH,?_,?_,hHB⟩
  · intro n
    have hh := hcB n
    rw [Real.norm_eq_abs,he0] at hh
    exact hh.trans_eq (by ring)
  · intro n
    have hh := hlB n
    rw [he1] at hh
    exact hh.trans_eq (by ring)

theorem actual_scalar_geometric_state_error_two
    {u q : E → ℝ} {M r theta : ℝ} {n : ℕ} (hr : 0 < r) (htheta : 0 < theta)
    (hs : ActualScalarGeometricStateTwo u M r theta n q) :
    (∫ x in ball (0 : E) (r^n), (u x-q x)^2) ≤ (theta^n)^2*(r^n)^8 := by
  obtain ⟨ww,hwn⟩ := hs.2.2.2
  have hR : 0 < r^n := pow_pos hr n
  have ha : 0 < theta^n := pow_pos htheta n
  have hw : MemLp (fun z => (theta^n)⁻¹*((r^n)^2)⁻¹*
      (u ((0 : E)+(r^n) • z)-q ((0 : E)+(r^n) • z)))
      2 (volume.restrict (ball (0 : E) 1)) := by
    have hh := ww.memLp
    change MemLp (fun z => (theta^n)⁻¹*((r^n)^2)⁻¹*(u ((r^n) • z)-q ((r^n) • z)))
      2 (volume.restrict (ball (0 : E) 1)) at hh
    simpa only [zero_add] using hh
  have hi := actual_quadratic_scale_L2_identity_two hR ha (fun x => u x-q x) hw
  have hn : ‖hw.toLp (fun z => (theta^n)⁻¹*((r^n)^2)⁻¹*
      (u ((0 : E)+(r^n) • z)-q ((0 : E)+(r^n) • z)))‖ ≤ 1 := by
    have hh := hwn
    change ‖ww.memLp.toLp (fun z => (theta^n)⁻¹*((r^n)^2)⁻¹*(u ((r^n) • z)-q ((r^n) • z)))‖ ≤ 1 at hh
    simpa only [zero_add] using hh
  have hbound : ((theta^n)^2*(r^n)^8)⁻¹*
      (∫ x in ball (0 : E) (r^n), (u x-q x)^2) ≤ 1 := by
    nlinarith [norm_nonneg (hw.toLp (fun z => (theta^n)⁻¹*((r^n)^2)⁻¹*
      (u ((0 : E)+(r^n) • z)-q ((0 : E)+(r^n) • z))))]
  have hp : 0 < (theta^n)^2*(r^n)^8 := by positivity
  have hh := mul_le_mul_of_nonneg_left hbound hp.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul,mul_one] using hh


theorem actual_scalar_geometric_limit_error_two
    {u : E → ℝ} {M r theta : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (hr1 : r ≤ 1)
    (htheta : 0 < theta) (htheta2 : theta ≤ (1/2 : ℝ))
    (hu : MemLp u 2 (volume.restrict (ball (0 : E) 1)))
    {Q : ℕ → E → ℝ} (hQ0 : Q 0 = fun _ => 0)
    (hs : ∀ n, ActualScalarGeometricStateTwo u M r theta n (Q n))
    (hi : ∀ n, ActualScalarGeometricIncrementTwo M r theta n (Q n) (Q (n+1))) :
    ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
      (∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0) ∧
      |p 0| ≤ 2*M ∧ ‖fderiv ℝ p 0‖ ≤ 2*M ∧
      (∀ x, ‖realHessian p x‖ ≤ 2*M) ∧
      ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
        (2+50*M^2*(volume (ball (0 : E) 1)).toReal)*(theta^n)^2*(r^n)^8 := by
  obtain ⟨c,l,H,hc,hl,hH,hcB,hlB,hHB⟩ := actual_scalar_geometric_jet_limits_two hM hr.le hr1 htheta.le htheta2 hi
  have hQ (n : ℕ) := (hs n).1
  have hsym := actual_realHessian_limit_symmetry_two hQ hH
  let p := actualQuadraticJetFunctionTwo c l H
  obtain ⟨hp,hp0,hp1,hp2⟩ := actual_quadratic_jet_reconstruction_two c l H hsym
  have hc0 : |c| ≤ 2*M := by
    simpa only [hQ0,pow_zero,one_pow,mul_one,zero_sub,abs_neg] using hcB 0
  have hD0 : fderiv ℝ (Q 0) 0 = 0 := by rw [hQ0];simp
  have hH0 : realHessian (Q 0) 0 = 0 := by rw [hQ0];unfold realHessian;simp
  have hl0 : ‖l‖ ≤ 2*M := by
    simpa only [hD0,pow_zero,mul_one,zero_sub,norm_neg] using hlB 0
  have hHz : ‖realHessian (Q 0) 0-H‖ = ‖H‖ := by
    rw [hH0]
    have he : (0 : E →L[ℝ] E →L[ℝ] ℝ)-H = -H := by
      ext v w
      simp only [_root_.sub_apply,_root_.zero_apply,_root_.neg_apply]
      ring
    exact (congrArg norm he).trans (norm_neg H)
  have hH0B : ‖H‖ ≤ 2*M := by
    simpa only [hHz,pow_zero,mul_one] using hHB 0
  refine ⟨p,hp,actual_quadratic_limit_trace_zero_two hQ hH (fun n => (hs n).2.1 0) c l,
    ?_,?_,?_,?_⟩
  · simpa only [p,hp0] using hc0
  · simpa only [p,hp1] using hl0
  · intro x
    simpa only [p,hp2 x] using hH0B
  · intro n
    have hR : 0 < r^n := pow_pos hr n
    have ha : 0 ≤ theta^n := pow_nonneg htheta.le n
    have hR1 : r^n ≤ 1 := pow_le_one₀ hr.le hr1
    letI : IsFiniteMeasure (volume.restrict (ball (0 : E) (r^n))) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hur := hu.mono_measure (Measure.restrict_mono (ball_subset_ball hR1) le_rfl)
    have hQr := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff (hQ n) 1).continuous (0 : E) (r^n)
    have hpr := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 1).continuous (0 : E) (r^n)
    have hb := actual_quadratic_scaled_tail_bound_two (hQ n) hp hM ha hR.le
      (by simpa only [hp0] using hcB n)
      (by simpa only [hp1] using hlB n)
      (by simpa only [hp2 0] using hHB n)
    have hcmp := actual_quadratic_comparison_square_error_two hur hQr hpr
      (by positivity : 0 ≤ 5*M*theta^n*(r^n)^2) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact hb x (ball_subset_closedBall hx))
    rw [actual_scalar_L2_norm_squared_two (u := fun x => u x-Q n x) (hur.sub hQr),
      actual_four_ball_volume_scaling_two hR] at hcmp
    have herr := actual_scalar_geometric_state_error_two hr htheta (hs n)
    calc
      _ ≤ 2*(∫ x in ball (0 : E) (r^n), (u x-Q n x)^2)+
          2*(5*M*theta^n*(r^n)^2)^2*((r^n)^4*(volume (ball (0 : E) 1)).toReal) := hcmp
      _ ≤ 2*((theta^n)^2*(r^n)^8)+
          2*(5*M*theta^n*(r^n)^2)^2*((r^n)^4*(volume (ball (0 : E) 1)).toReal) := by
        exact add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num : 0 ≤ (2 : ℝ))) le_rfl
      _ = _ := by ring


end PowerConvexity
