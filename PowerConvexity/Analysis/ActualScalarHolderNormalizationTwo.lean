import PowerConvexity.Analysis.ActualScalarCorrectedNormalizationTwo

/-! # Actual amplitude normalization after removing the constant source.
The amplitude is constructed from the actual L2 norm and source growth.
All weak identities retain every H01 test and every gradient witness.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_constant_corrected_source_holder_growth_two
    {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {f : E → ℝ}
    {b epsilon K alpha : ℝ} {U : Set E}
    (ha : ∀ x ∈ U, ∀ z : E, ‖z-matMulE (a x) z‖ ≤ (epsilon*‖x‖^alpha)*‖z‖)
    (hf : ∀ x ∈ U, |f x-b| ≤ K*‖x‖^alpha) :
    ∀ x ∈ U, |f x-quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x| ≤
      (K+|b| *epsilon)*‖x‖^alpha := by
  intro x hx
  have hq := actual_constant_source_correction_error_two (b := b) (ha x hx)
  have he : f x-quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x =
      (f x-b)-(quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x-b) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (hf x hx) hq).trans_eq (by ring))

theorem actual_scalar_weak_normalize_holder_growth_two
    {epsilon K alpha : ℝ} (heps : 0 < epsilon) (hK : 0 ≤ K)
    (A : EllipticCoeff (2+2) (ball (0 : E) 1)) {f u : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)))
    (hfn : ∀ x ∈ ball (0 : E) 1, |f x| ≤ K*‖x‖^alpha)
    (hu : ActualScalarWeakEquationTwo A f u)
    (uw : MemW1pWitness 2 u (ball (0 : E) 1)) :
    ∃ S > 0, S = ‖uw.memLp.toLp u‖+K/epsilon+1 ∧
      MemLp (fun x => S⁻¹*f x) 2 (volume.restrict (ball (0 : E) 1)) ∧
      (∀ x ∈ ball (0 : E) 1, |S⁻¹*f x| ≤ epsilon*‖x‖^alpha) ∧
      ActualScalarWeakEquationTwo A (fun x => S⁻¹*f x) (fun x => S⁻¹*u x) ∧
      ∃ ww : MemW1pWitness 2 (fun x => S⁻¹*u x) (ball (0 : E) 1),
        ‖ww.memLp.toLp (fun x => S⁻¹*u x)‖ ≤ 1 := by
  let N := ‖uw.memLp.toLp u‖
  have hN : 0 ≤ N := norm_nonneg _
  let S := N+K/epsilon+1
  have hKe : 0 ≤ K/epsilon := div_nonneg hK heps.le
  have hS : 0 < S := by dsimp [S];linarith
  have hNS : N ≤ S := by dsimp [S];linarith
  have hKS : K ≤ epsilon*S := by
    have hh : K/epsilon ≤ S := by dsimp [S];linarith
    have hh' := (div_le_iff₀ heps).mp hh
    nlinarith only [hh']
  refine ⟨S,hS,rfl,hf.const_mul S⁻¹,?_,actual_scalar_weak_smul_two isOpen_ball hu S⁻¹,?_⟩
  · intro x hx
    rw [abs_mul,abs_of_pos (inv_pos.mpr hS)]
    have hcoef : S⁻¹*K ≤ epsilon :=
      (mul_le_mul_of_nonneg_left hKS (inv_pos.mpr hS).le).trans_eq (by field_simp)
    calc
      _ ≤ S⁻¹*(K*‖x‖^alpha) := mul_le_mul_of_nonneg_left (hfn x hx) (inv_pos.mpr hS).le
      _ = (S⁻¹*K)*‖x‖^alpha := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg x) alpha)
  · let ww := uw.smul S⁻¹
    refine ⟨ww,?_⟩
    have he : ww.memLp.toLp (fun x => S⁻¹*u x) = S⁻¹ • uw.memLp.toLp u :=
      MemLp.toLp_const_smul S⁻¹ uw.memLp
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hS)]
    exact (mul_le_mul_of_nonneg_left hNS (inv_pos.mpr hS).le).trans_eq (inv_mul_cancel₀ hS.ne')

theorem actual_scalar_holder_corrected_normalization_two
    {epsilon K b alpha : ℝ} (heps : 0 < epsilon) (hK : 0 ≤ K)
    (A : EllipticCoeff (2+2) (ball (0 : E) 1))
    {V : Set E} (hV : IsOpen V) (hclosed : closedBall (0 : E) 1 ⊆ V)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V)
    (hdiv : ∀ x ∈ ball (0 : E) 1, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
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
  have hqf := actual_quadratic_source_memLp_two (fun i j => (hA i j).continuousOn.mono hclosed) hq
  have hqw := actual_divergenceFree_quadratic_source_two hV hclosed A hA hdiv hq
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
