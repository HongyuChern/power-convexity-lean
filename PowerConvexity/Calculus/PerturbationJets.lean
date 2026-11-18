import PowerConvexity.Calculus.PluriharmonicQuadratic

/-! # Exact jets of actual pluriharmonic perturbations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

theorem complexHessian_add_at {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) (a b : ι → E) :
    complexHessian a b (fun y => u y + q y) x =
      complexHessian a b u x + complexHessian a b q x := by
  ext i j
  rw [complexHessian_real_entry (hu.add hq)]
  simp only [realHessian_add hu hq, add_apply, Matrix.add_apply,
    complexHessian_real_entry hu, complexHessian_real_entry hq, Complex.ofReal_add]
  ring

theorem pureHessian_add_at {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) (a b : ι → E) :
    pureHessian a b (fun y => u y + q y) x =
      pureHessian a b u x + pureHessian a b q x := by
  ext i j
  rw [pureHessian_real_entry (hu.add hq)]
  simp only [realHessian_add hu hq, add_apply, Matrix.add_apply,
    pureHessian_real_entry hu, pureHessian_real_entry hq, Complex.ofReal_add]
  ring

theorem complexHessian_const_mul_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (c : ℝ) (a b : ι → E) :
    complexHessian a b (fun y => c * u y) x = (c : ℂ) • complexHessian a b u x := by
  ext i j
  rw [complexHessian_real_entry (contDiffAt_const.mul hu)]
  simp only [realHessian_const_mul, smul_apply, smul_eq_mul, Matrix.smul_apply,
    complexHessian_real_entry hu, Complex.ofReal_mul]
  ring

theorem pureHessian_const_mul_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (c : ℝ) (a b : ι → E) :
    pureHessian a b (fun y => c * u y) x = (c : ℂ) • pureHessian a b u x := by
  ext i j
  rw [pureHessian_real_entry (contDiffAt_const.mul hu)]
  simp only [realHessian_const_mul, smul_apply, smul_eq_mul, Matrix.smul_apply,
    pureHessian_real_entry hu, Complex.ofReal_mul]
  ring

theorem complexGradient_add_at {u q : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hq : DifferentiableAt ℝ q x) (a b : ι → E) :
    complexGradient a b (fun y => u y + q y) x =
      complexGradient a b u x + complexGradient a b q x := by
  have hs : DifferentiableAt ℝ (fun y => u y + q y) x := hu.add hq
  funext i
  rw [complexGradient_real_entry hs]
  simp only [complexGradient_real_entry hu,
    complexGradient_real_entry hq, fderiv_fun_add hu hq, add_apply, Pi.add_apply,
    Complex.ofReal_add]
  ring

theorem complexGradient_zero_of_fderiv_zero {q : E → ℝ} {x : E}
    (hq : DifferentiableAt ℝ q x) (hDq : fderiv ℝ q x = 0) (a b : ι → E) :
    complexGradient a b q x = 0 := by
  funext i
  simp only [complexGradient_real_entry hq, hDq, zero_apply,
    Complex.ofReal_zero, mul_zero, sub_zero, Pi.zero_apply]

theorem modifiedA_centered_pluriharmonic {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) (a b : ι → E)
    (hq0 : q x = 0) (hDq : fderiv ℝ q x = 0) (hAq : complexHessian a b q x = 0) :
    modifiedA a b (fun y => u y + q y) x = modifiedA a b u x := by
  have hg : complexGradient a b (fun y => u y + q y) x = complexGradient a b u x := by
    rw [complexGradient_add_at (hu.differentiableAt (by norm_num))
      (hq.differentiableAt (by norm_num)),
      complexGradient_zero_of_fderiv_zero (hq.differentiableAt (by norm_num)) hDq, add_zero]
  have hH : complexHessian a b (fun y => u y + q y) x = complexHessian a b u x := by
    rw [complexHessian_add_at hu hq, hAq, add_zero]
  ext i j
  simp only [modifiedA, hH, hg, hq0, add_zero]

theorem modifiedB_centered_perturbation {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) (a b : ι → E)
    (hq0 : q x = 0) (hDq : fderiv ℝ q x = 0) :
    modifiedB a b (fun y => u y + q y) x =
      modifiedB a b u x + pureHessian a b q x := by
  have hg : complexGradient a b (fun y => u y + q y) x = complexGradient a b u x := by
    rw [complexGradient_add_at (hu.differentiableAt (by norm_num))
      (hq.differentiableAt (by norm_num)),
      complexGradient_zero_of_fderiv_zero (hq.differentiableAt (by norm_num)) hDq, add_zero]
  have hH := pureHessian_add_at hu hq a b
  ext i j
  simp only [modifiedB, hH, hg, hq0, add_zero, Matrix.add_apply]
  ring

variable [Fintype ι] [DecidableEq ι]

theorem constantDensity_pluriharmonic_add {u q : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hq : ContDiffOn ℝ 2 q U)
    (a b : ι → E) (ρ : ℂ)
    (hρ : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hAq : ∀ y ∈ U, complexHessian a b q y = 0) :
    ∀ y ∈ U, (complexHessian a b (fun z => u z + q z) y).det = ρ := by
  intro y hy
  rw [complexHessian_add_at (hu.contDiffAt (hU.mem_nhds hy))
    (hq.contDiffAt (hU.mem_nhds hy)), hAq y hy, add_zero, hρ y hy]

theorem strictPsh_pluriharmonic_add_iff {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) (a b : ι → E)
    (hAq : complexHessian a b q x = 0) :
    (complexHessian a b (fun y => u y + q y) x).PosDef ↔
      (complexHessian a b u x).PosDef := by
  rw [complexHessian_add_at hu hq, hAq, add_zero]

end PowerConvexity
