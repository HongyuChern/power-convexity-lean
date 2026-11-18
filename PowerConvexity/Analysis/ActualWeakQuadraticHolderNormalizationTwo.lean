import PowerConvexity.Analysis.ActualWeakQuadraticSourcesTwo

/-! # Actual corrected normalization with continuous coefficients and weak quadratic sources -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_weak_quadratic_holder_corrected_normalization_two
    {epsilon K b alpha : ℝ} (heps : 0 < epsilon) (hK : 0 ≤ K)
    (A : EllipticCoeff (2+2) (ball (0 : E) 1))
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closedBall (0 : E) 1))
    (hquad : ActualWeakQuadraticSourcesTwo A)
    (hdev : ∀ x ∈ ball (0 : E) 1, ∀ v : E,
      ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖^alpha)*‖v‖)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)))
    (hfn : ∀ x ∈ ball (0 : E) 1, |f x-b| ≤ K*‖x‖^alpha)
    (hu : ActualScalarWeakEquationTwo A f u)
    {N : ℝ} (uw : MemW1pWitness 2 u (ball (0 : E) 1)) (hun : ‖uw.memLp.toLp u‖ ≤ N) :
    ∃ S > 0, S ≤ N+(|b|/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal+
        (K+|b| * epsilon)/epsilon+1 ∧
      MemLp (fun x => S⁻¹*(f x-quadraticScalarSourceTwo A.a (scalarConstantSourceQuadraticTwo b) x))
        2 (volume.restrict (ball (0 : E) 1)) ∧
      (∀ x ∈ ball (0 : E) 1,
        |S⁻¹*(f x-quadraticScalarSourceTwo A.a (scalarConstantSourceQuadraticTwo b) x)| ≤ epsilon*‖x‖^alpha) ∧
      ActualScalarWeakEquationTwo A
        (fun x => S⁻¹*(f x-quadraticScalarSourceTwo A.a (scalarConstantSourceQuadraticTwo b) x))
        (fun x => S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x)) ∧
      ∃ ww : MemW1pWitness 2 (fun x => S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x)) (ball (0 : E) 1),
        ‖ww.memLp.toLp (fun x => S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x))‖ ≤ 1 := by
  have hq := scalarConstantSourceQuadraticTwo_isQuadratic b
  have hqf := actual_quadratic_source_memLp_two hA hq
  have hqw := hquad _ hq
  have hr := actual_scalar_weak_sub_two isOpen_ball hf hqf hu hqw
  have hfr : MemLp (fun x => f x-quadraticScalarSourceTwo A.a (scalarConstantSourceQuadraticTwo b) x)
      2 (volume.restrict (ball (0 : E) 1)) := hf.sub hqf
  let vw := MemW1p.someWitness hr.1
  have hqm := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hq 1).continuous (0 : E) 1
  letI : IsFiniteMeasure (volume.restrict (ball (0 : E) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hqn : ‖hqm.toLp (scalarConstantSourceQuadraticTwo b)‖ ≤
      (|b|/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal := by
    apply actual_scalar_L2_bound_of_ae_bound_two hqm (by positivity)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    have hx2 : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    simp only [scalarConstantSourceQuadraticTwo,abs_mul,abs_div,abs_neg,
      abs_of_nonneg (sq_nonneg ‖x‖)]
    rw [show |(8 : ℝ)| = 8 by norm_num]
    exact (mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ |b|/8)).trans_eq (mul_one _)
  have hvn : ‖vw.memLp.toLp (fun x => u x-scalarConstantSourceQuadraticTwo b x)‖ ≤
      N+(|b|/8)*Real.sqrt (volume (ball (0 : E) 1)).toReal := by
    have he : vw.memLp.toLp (fun x => u x-scalarConstantSourceQuadraticTwo b x) =
        uw.memLp.toLp u-hqm.toLp (scalarConstantSourceQuadraticTwo b) := uw.memLp.toLp_sub hqm
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hun hqn)
  obtain ⟨S,hS,hSe,hfm,hfn',hw,ww,hwn⟩ := actual_scalar_weak_normalize_holder_growth_two heps
    (by positivity : 0 ≤ K+|b| * epsilon) A hfr
    (actual_constant_corrected_source_holder_growth_two hdev hfn) hr vw
  refine ⟨S,hS,?_,hfm,hfn',hw,ww,hwn⟩
  rw [hSe]
  linarith

end PowerConvexity
