import PowerConvexity.Analysis.ActualQuadraticApproximationErrorTwo

/-! # Actual second-order L2 approximation of the original weak function.
The single harmonic quadratic is constructed from the proved sequence.
Its error has the full four-dimensional quadratic scaling at every scale.
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

theorem actual_scalar_quadratic_limit_error_two
    {u : E → ℝ} {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (hr1 : r ≤ 1)
    (hu : MemLp u 2 (volume.restrict (ball (0 : E) 1)))
    {Q : ℕ → E → ℝ} (hQ0 : Q 0 = fun _ => 0)
    (hs : ∀ n, ActualScalarQuadraticStateTwo u M r n (Q n))
    (hi : ∀ n, ActualScalarQuadraticIncrementTwo M r n (Q n) (Q (n+1))) :
    ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
      (∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0) ∧
      |p 0| ≤ 2*M ∧ ‖fderiv ℝ p 0‖ ≤ 2*M ∧
      (∀ x, ‖realHessian p x‖ ≤ 2*M) ∧
      ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
        (2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((1/2 : ℝ)^n)^2*(r^n)^8 := by
  obtain ⟨c,l,H,hc,hl,hH,hcB,hlB,hHB⟩ := actual_scalar_quadratic_jet_limits_two hM hr.le hr1 hi
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
    have ha : 0 ≤ (1/2 : ℝ)^n := pow_nonneg (by norm_num) n
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
      (by positivity : 0 ≤ 5*M*(1/2 : ℝ)^n*(r^n)^2) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact hb x (ball_subset_closedBall hx))
    rw [actual_scalar_L2_norm_squared_two (u := fun x => u x-Q n x) (hur.sub hQr),
      actual_four_ball_volume_scaling_two hR] at hcmp
    have herr := actual_scalar_quadratic_state_error_two hr (hs n)
    calc
      _ ≤ 2*(∫ x in ball (0 : E) (r^n), (u x-Q n x)^2)+
          2*(5*M*(1/2 : ℝ)^n*(r^n)^2)^2*((r^n)^4*(volume (ball (0 : E) 1)).toReal) := hcmp
      _ ≤ 2*(((1/2 : ℝ)^n)^2*(r^n)^8)+
          2*(5*M*(1/2 : ℝ)^n*(r^n)^2)^2*((r^n)^4*(volume (ball (0 : E) 1)).toReal) := by
        exact add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num : 0 ≤ (2 : ℝ))) le_rfl
      _ = _ := by ring

theorem actual_scalar_weak_harmonic_quadratic_expansion_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ M > 0, ∃ r > 0, r ≤ (1/32 : ℝ) ∧ ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : E) 1),
      (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ V : Set E, IsOpen V → closedBall (0 : E) 1 ⊆ V →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V) →
      (∀ x ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0) →
      (∀ x ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖)*‖v‖) →
      ∀ f u : E → ℝ, MemLp f 2 (volume.restrict (ball (0 : E) 1)) →
      (∀ x ∈ ball (0 : E) 1, |f x| ≤ epsilon*‖x‖) →
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : E) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0) ∧
        |p 0| ≤ 2*M ∧ ‖fderiv ℝ p 0‖ ≤ 2*M ∧
        (∀ x, ‖realHessian p x‖ ≤ 2*M) ∧
        ∀ n, (∫ x in ball (0 : E) (r^n), (u x-p x)^2) ≤
          (2+50*M^2*(volume (ball (0 : E) 1)).toReal)*((1/2 : ℝ)^n)^2*(r^n)^8 := by
  obtain ⟨M,hM,r,hr,hrb,epsilon,heps,heps1,hseq⟩ := actual_scalar_quadratic_sequence_two hL
  refine ⟨M,hM,r,hr,hrb,epsilon,heps,heps1,?_⟩
  intro A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu uw hun
  obtain ⟨Q,hQ0,hs,hi⟩ := hseq A hlam hAL V hV hclosed hA hdiv hdev f u hf hfn hu uw hun
  exact actual_scalar_quadratic_limit_error_two hM.le hr (by linarith) uw.memLp hQ0 hs hi

end PowerConvexity
