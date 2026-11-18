import PowerConvexity.Calculus.MatrixQuotientRatioHessianBridgeTwo

/-! # Actual complex derivative norms controlled by the four real Hermitian jets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_fderiv_norm_le_real_imag {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ (fun y => (f y).re) x‖+
      ‖fderiv ℝ (fun y => (f y).im) x‖ := by
  have hr : fderiv ℝ (fun y => (f y).re) x = Complex.reCLM.comp (fderiv ℝ f x) :=
    (Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  have hi : fderiv ℝ (fun y => (f y).im) x = Complex.imCLM.comp (fderiv ℝ f x) :=
    (Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hrv : (fderiv ℝ f x v).re = fderiv ℝ (fun y => (f y).re) x v := by rw [hr]; rfl
  have hiv : (fderiv ℝ f x v).im = fderiv ℝ (fun y => (f y).im) x v := by rw [hi]; rfl
  have h1 := (fderiv ℝ (fun y => (f y).re) x).le_opNorm v
  have h2 := (fderiv ℝ (fun y => (f y).im) x).le_opNorm v
  have hh := Complex.norm_le_abs_re_add_abs_im (fderiv ℝ f x v)
  rw [hrv,hiv] at hh
  rw [Real.norm_eq_abs] at h1 h2
  nlinarith only [hh,h1,h2]

noncomputable def hermitianDerivativeSumTwo (M : E → Matrix (Fin 2) (Fin 2) ℂ) (x : E) : ℝ :=
  ‖fderiv ℝ (fun y => (M y 0 0).re) x‖+‖fderiv ℝ (fun y => (M y 1 1).re) x‖+
    ‖fderiv ℝ (fun y => (M y 0 1).re) x‖+‖fderiv ℝ (fun y => (M y 0 1).im) x‖

theorem hermitianDerivativeSumTwo_nonneg (M : E → Matrix (Fin 2) (Fin 2) ℂ) (x : E) :
    0 ≤ hermitianDerivativeSumTwo M x := by unfold hermitianDerivativeSumTwo; positivity

theorem hermitian_matrix_entry_fderiv_norm_le_sum_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian) (i j : Fin 2) :
    ‖fderiv ℝ (fun y => M y i j) x‖ ≤ hermitianDerivativeSumTwo M x := by
  have hdiag (k : Fin 2) : (fun y => (M y k k).im) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hherm] with y hy
    have hh := congrArg Complex.im (hy.apply k k)
    change -(M y k k).im = (M y k k).im at hh
    linarith
  have hre : (fun y => (M y 1 0).re) =ᶠ[𝓝 x] fun y => (M y 0 1).re := by
    filter_upwards [hherm] with y hy
    have hh := congrArg Complex.re (hy.apply 1 0)
    exact hh.symm
  have him : (fun y => (M y 1 0).im) =ᶠ[𝓝 x] fun y => -(M y 0 1).im := by
    filter_upwards [hherm] with y hy
    have hh := congrArg Complex.im (hy.apply 1 0)
    exact hh.symm
  have h00 := complex_fderiv_norm_le_real_imag (hM 0 0)
  have h11 := complex_fderiv_norm_le_real_imag (hM 1 1)
  have h01 := complex_fderiv_norm_le_real_imag (hM 0 1)
  have h10 := complex_fderiv_norm_le_real_imag (hM 1 0)
  have hz : fderiv ℝ (fun _ : E => (0:ℝ)) x = 0 := (hasFDerivAt_const (0:ℝ) x).fderiv
  rw [(hdiag 0).fderiv_eq,hz,norm_zero,add_zero] at h00
  rw [(hdiag 1).fderiv_eq,hz,norm_zero,add_zero] at h11
  rw [hre.fderiv_eq,him.fderiv_eq,fderiv_fun_neg,norm_neg] at h10
  have h0 := norm_nonneg (fderiv ℝ (fun y => (M y 0 0).re) x)
  have h1 := norm_nonneg (fderiv ℝ (fun y => (M y 1 1).re) x)
  have h2 := norm_nonneg (fderiv ℝ (fun y => (M y 0 1).re) x)
  have h3 := norm_nonneg (fderiv ℝ (fun y => (M y 0 1).im) x)
  unfold hermitianDerivativeSumTwo
  fin_cases i <;> fin_cases j
  · change ‖fderiv ℝ (fun y => M y 0 0) x‖ ≤ _
    linarith
  · change ‖fderiv ℝ (fun y => M y 0 1) x‖ ≤ _
    linarith
  · change ‖fderiv ℝ (fun y => M y 1 0) x‖ ≤ _
    linarith
  · change ‖fderiv ℝ (fun y => M y 1 1) x‖ ≤ _
    linarith

end PowerConvexity
