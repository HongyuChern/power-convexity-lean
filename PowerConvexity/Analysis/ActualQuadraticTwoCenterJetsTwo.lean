import PowerConvexity.Analysis.ActualQuadraticApproximationUniquenessTwo
import PowerConvexity.Analysis.ActualPhysicalQuadraticTwo
import PowerConvexity.Calculus.QuadraticJointJets

/-! # Actual quadratic jet comparison at two physical centres

Every estimate uses the actual ball integral and the actual derivatives of
the polynomial. The overlap argument is independent of any representative
of the weak function. Its input is two quantitative approximation bounds,
not a compatibility assumption on the resulting jets.
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

theorem actual_setIntegral_translate_ball_two (c : E) (r : ℝ) (f : E → ℝ) :
    (∫ z in ball (0 : E) r, f (c+z)) = ∫ x in ball c r, f x := by
  simpa only [one_smul,one_pow,inv_one,one_mul] using
    crossover_integral_comp_affine_ball (x₀ := c) (R := (1 : ℝ)) (ρ := r) zero_lt_one f

theorem actual_quadratic_translate_jets_two {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (c : E) :
    fderiv ℝ (fun z => q (c+z)) 0 = fderiv ℝ q c ∧
      realHessian (fun z => q (c+z)) 0 = realHessian q c := by
  have hT : HasFDerivAt (fun z : E => c+z) (ContinuousLinearMap.id ℝ E) 0 :=
    (hasFDerivAt_id (0 : E)).const_add c
  have hd : HasFDerivAt (fun z => q (c+z)) (fderiv ℝ q c) 0 := by
    simpa only [add_zero,ContinuousLinearMap.comp_id,Function.comp_def] using
      (((IsQuadraticPolynomial_contDiff hq 1).contDiffAt.differentiableAt
        (by norm_num)).hasFDerivAt.comp 0 hT)
  refine ⟨hd.fderiv,?_⟩
  ext v w
  have hh := realHessian_comp_affine (ContinuousLinearMap.id ℝ E) c
    (x := (0 : E)) (IsQuadraticPolynomial_contDiff hq 2).contDiffAt v w
  simpa only [ContinuousLinearMap.id_apply,add_zero] using hh

theorem actual_quadratic_scaled_L2_jet_bound_at_two :
    ∃ C > 0, ∀ (q : E → ℝ), IsQuadraticPolynomial q →
      ∀ (c : E) (r : ℝ), 0 < r → ∀ a ≥ 0,
      (∫ x in ball c r, (q x)^2) ≤ a^2*r^8 →
        |q c| ≤ C*a*r^2 ∧
        ‖fderiv ℝ q c‖ ≤ C*a*r ∧ ‖realHessian q c‖ ≤ C*a := by
  obtain ⟨C,hC,hbound⟩ := actual_quadratic_scaled_L2_jet_bound_two
  refine ⟨C,hC,?_⟩
  intro q hq c r hr a ha herr
  have hp : IsQuadraticPolynomial (fun z => q (c+z)) := by
    simpa only [ContinuousLinearMap.id_apply] using
      IsQuadraticPolynomial_comp_affine hq (ContinuousLinearMap.id ℝ E) c
  have he : (∫ z in ball (0 : E) r, (q (c+z))^2) ≤ a^2*r^8 := by
    rw [actual_setIntegral_translate_ball_two c r (fun x => (q x)^2)]
    exact herr
  have hh := hbound _ hp r hr a ha he
  obtain ⟨hD,hH⟩ := actual_quadratic_translate_jets_two hq c
  simpa only [add_zero,hD,hH] using hh

theorem actual_quadratic_two_center_difference_energy_two
    {u p q : E → ℝ} (hp : IsQuadraticPolynomial p) (hq : IsQuadraticPolynomial q)
    {x y : E} {r a : ℝ} (hr : 0 < r) (hxy : dist x y ≤ r) (ha : 0 ≤ a)
    (hu : MemLp u 2 (volume.restrict (ball x (2*r))))
    (hpE : (∫ z in ball x (2*r), (u z-p z)^2) ≤ a^2*(2*r)^8)
    (hqE : (∫ z in ball y r, (u z-q z)^2) ≤ a^2*r^8) :
    (∫ z in ball y r, (p z-q z)^2) ≤ (24*a)^2*r^8 := by
  have hsub : ball y r ⊆ ball x (2*r) :=
    ball_subset_ball' (by rw [dist_comm]; linarith)
  have huy := hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpx := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous x (2*r)
  have hpy := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous y r
  have hqy := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hq 0).continuous y r
  have hpi : Integrable (fun z => (u z-p z)^2) (volume.restrict (ball x (2*r))) := by
    simpa only [Pi.sub_apply] using (hu.sub hpx).integrable_sq
  have hsmall : (∫ z in ball y r, (u z-p z)^2) ≤ a^2*(2*r)^8 := by
    apply le_trans (setIntegral_mono_set hpi
      (Filter.Eventually.of_forall (fun z => sq_nonneg (u z-p z)))
      (Filter.Eventually.of_forall (fun z hz => hsub hz))) hpE
  have hpiY : Integrable (fun z => 2*(u z-p z)^2) (volume.restrict (ball y r)) := by
    simpa only [Pi.sub_apply] using (huy.sub hpy).integrable_sq.const_mul 2
  have hqiY : Integrable (fun z => 2*(u z-q z)^2) (volume.restrict (ball y r)) := by
    simpa only [Pi.sub_apply] using (huy.sub hqy).integrable_sq.const_mul 2
  have hdiff : Integrable (fun z => (p z-q z)^2) (volume.restrict (ball y r)) := by
    simpa only [Pi.sub_apply] using (hpy.sub hqy).integrable_sq
  have hi : (∫ z in ball y r, (p z-q z)^2) ≤
      ∫ z in ball y r, 2*(u z-p z)^2+2*(u z-q z)^2 := by
    apply integral_mono_ae hdiff (hpiY.add hqiY)
    filter_upwards with z
    change (p z-q z)^2 ≤ 2*(u z-p z)^2+2*(u z-q z)^2
    nlinarith [sq_nonneg ((u z-p z)+(u z-q z))]
  rw [integral_add hpiY hqiY,integral_const_mul,integral_const_mul] at hi
  calc
    _ ≤ 2*(a^2*(2*r)^8)+2*(a^2*r^8) :=
      hi.trans (add_le_add (mul_le_mul_of_nonneg_left hsmall (by norm_num))
        (mul_le_mul_of_nonneg_left hqE (by norm_num)))
    _ ≤ (24*a)^2*r^8 := by
      nlinarith [mul_nonneg (sq_nonneg a) (pow_nonneg hr.le 8)]

theorem actual_quadratic_two_center_jet_comparison_two :
    ∃ C > 0, ∀ (u p q : E → ℝ), IsQuadraticPolynomial p → IsQuadraticPolynomial q →
      ∀ (x y : E) (r a : ℝ), 0 < r → dist x y ≤ r → 0 ≤ a →
      MemLp u 2 (volume.restrict (ball x (2*r))) →
      (∫ z in ball x (2*r), (u z-p z)^2) ≤ a^2*(2*r)^8 →
      (∫ z in ball y r, (u z-q z)^2) ≤ a^2*r^8 →
        |p y-q y| ≤ C*a*r^2 ∧
        ‖fderiv ℝ p y-fderiv ℝ q y‖ ≤ C*a*r ∧
        ‖realHessian p x-realHessian q y‖ ≤ C*a := by
  obtain ⟨C,hC,hbound⟩ := actual_quadratic_scaled_L2_jet_bound_at_two
  refine ⟨24*C,by positivity,?_⟩
  intro u p q hp hq x y r a hr hxy ha hu hpE hqE
  have he := actual_quadratic_two_center_difference_energy_two hp hq hr hxy ha hu hpE hqE
  have hb := hbound _ (IsQuadraticPolynomial_sub hp hq) y r hr (24*a)
    (mul_nonneg (by norm_num) ha) he
  have hpc : ContDiffAt ℝ 2 p y := (IsQuadraticPolynomial_contDiff hp 2).contDiffAt
  have hqc : ContDiffAt ℝ 2 q y := (IsQuadraticPolynomial_contDiff hq 2).contDiffAt
  rw [fderiv_fun_sub (hpc.differentiableAt (by norm_num))
    (hqc.differentiableAt (by norm_num)),realHessian_sub_at hpc hqc] at hb
  have hH : realHessian p x = realHessian p y :=
    (quadratic_realHessian_from_jet_zero hp x).trans (quadratic_realHessian_from_jet_zero hp y).symm
  rw [hH]
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hb

end PowerConvexity
