import PowerConvexity.Analysis.ActualQuadraticJetReconstructionTwo

/-! # Actual physical-ball error and polynomial tail estimates.
These statements concern the original measurable weak function and the
actual polynomials, with all four-dimensional scaling factors retained.
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
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_quadratic_state_error_two
    {u q : E → ℝ} {M r : ℝ} {n : ℕ} (hr : 0 < r)
    (hs : ActualScalarQuadraticStateTwo u M r n q) :
    (∫ x in ball (0 : E) (r^n), (u x-q x)^2) ≤ ((1/2 : ℝ)^n)^2*(r^n)^8 := by
  obtain ⟨ww,hwn⟩ := hs.2.2.2
  have hR : 0 < r^n := pow_pos hr n
  have ha : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
  have hw : MemLp (fun z => ((1/2 : ℝ)^n)⁻¹*((r^n)^2)⁻¹*
      (u ((0 : E)+(r^n) • z)-q ((0 : E)+(r^n) • z)))
      2 (volume.restrict (ball (0 : E) 1)) := by
    have hh := ww.memLp
    change MemLp (fun z => ((1/2 : ℝ)^n)⁻¹*((r^n)^2)⁻¹*(u ((r^n) • z)-q ((r^n) • z)))
      2 (volume.restrict (ball (0 : E) 1)) at hh
    simpa only [zero_add] using hh
  have hi := actual_quadratic_scale_L2_identity_two hR ha (fun x => u x-q x) hw
  have hn : ‖hw.toLp (fun z => ((1/2 : ℝ)^n)⁻¹*((r^n)^2)⁻¹*
      (u ((0 : E)+(r^n) • z)-q ((0 : E)+(r^n) • z)))‖ ≤ 1 := by
    have hh := hwn
    change ‖ww.memLp.toLp (fun z => ((1/2 : ℝ)^n)⁻¹*((r^n)^2)⁻¹*(u ((r^n) • z)-q ((r^n) • z)))‖ ≤ 1 at hh
    simpa only [zero_add] using hh
  have hbound : (((1/2 : ℝ)^n)^2*(r^n)^8)⁻¹*
      (∫ x in ball (0 : E) (r^n), (u x-q x)^2) ≤ 1 := by
    nlinarith [norm_nonneg (hw.toLp (fun z => ((1/2 : ℝ)^n)⁻¹*((r^n)^2)⁻¹*
      (u ((0 : E)+(r^n) • z)-q ((0 : E)+(r^n) • z))))]
  have hp : 0 < ((1/2 : ℝ)^n)^2*(r^n)^8 := by positivity
  have hh := mul_le_mul_of_nonneg_left hbound hp.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul,mul_one] using hh

theorem actual_quadratic_difference_value_bound_two {q p : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p) (x : E) :
    |q x-p x| ≤ |q 0-p 0|+‖fderiv ℝ q 0-fderiv ℝ p 0‖*‖x‖+
      (1/2 : ℝ)*‖realHessian q 0-realHessian p 0‖*‖x‖^2 := by
  have he : q x-p x = (q 0-p 0)+(fderiv ℝ q 0-fderiv ℝ p 0) x+
      (1/2 : ℝ)*(realHessian q 0-realHessian p 0) x x := by
    rw [quadratic_exact_Taylor hq 0 x,quadratic_exact_Taylor hp 0 x]
    simp only [sub_zero,_root_.sub_apply]
    ring
  have hl : |(fderiv ℝ q 0-fderiv ℝ p 0) x| ≤ ‖fderiv ℝ q 0-fderiv ℝ p 0‖*‖x‖ := by
    simpa only [Real.norm_eq_abs] using (fderiv ℝ q 0-fderiv ℝ p 0).le_opNorm x
  have hH : |(realHessian q 0-realHessian p 0) x x| ≤
      ‖realHessian q 0-realHessian p 0‖*‖x‖^2 := by
    calc
      _ = ‖(realHessian q 0-realHessian p 0) x x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(realHessian q 0-realHessian p 0) x‖*‖x‖ :=
        ((realHessian q 0-realHessian p 0) x).le_opNorm x
      _ ≤ (‖realHessian q 0-realHessian p 0‖*‖x‖)*‖x‖ :=
        mul_le_mul_of_nonneg_right ((realHessian q 0-realHessian p 0).le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ |q 0-p 0|+|(fderiv ℝ q 0-fderiv ℝ p 0) x|+
        |(1/2 : ℝ)*(realHessian q 0-realHessian p 0) x x| := abs_add_three _ _ _
    _ = |q 0-p 0|+|(fderiv ℝ q 0-fderiv ℝ p 0) x|+
        (1/2 : ℝ)*|(realHessian q 0-realHessian p 0) x x| := by rw [abs_mul];norm_num
    _ ≤ _ := by nlinarith

theorem actual_quadratic_scaled_tail_bound_two {q p : E → ℝ} {M a R : ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (h0 : |q 0-p 0| ≤ 2*M*a*R^2)
    (h1 : ‖fderiv ℝ q 0-fderiv ℝ p 0‖ ≤ 2*M*a*R)
    (h2 : ‖realHessian q 0-realHessian p 0‖ ≤ 2*M*a) :
    ∀ x ∈ closedBall (0 : E) R, |q x-p x| ≤ 5*M*a*R^2 := by
  intro x hx
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hx2 : ‖x‖^2 ≤ R^2 := by nlinarith [norm_nonneg x]
  have hl := mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
  have hl' := mul_le_mul_of_nonneg_left hxR (by positivity : 0 ≤ 2*M*a*R)
  have hH := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x‖)
  have hH' := mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ 2*M*a)
  have hb := actual_quadratic_difference_value_bound_two hq hp x
  nlinarith

end PowerConvexity
