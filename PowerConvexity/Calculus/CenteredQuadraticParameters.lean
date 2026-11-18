import PowerConvexity.Calculus.PerturbationJets
import PowerConvexity.Calculus.TakagiNormalizationTwo

/-! # Exact modified jets along centered pluriharmonic diagonal paths -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

theorem complexGradient_const_mul_at {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) (a b : ι → E) :
    complexGradient a b (fun y => c*u y) x = (c:ℂ) • complexGradient a b u x := by
  funext i
  rw [complexGradient_real_entry (hu.const_mul c)]
  simp only [Pi.smul_apply,complexGradient_real_entry hu,fderiv_const_mul hu c,
    smul_apply,smul_eq_mul,Complex.ofReal_mul]
  ring

theorem modifiedA_centered_scaled_pluriharmonic {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) (a b : ι → E)
    (h0 : h x = 0) (h1 : fderiv ℝ h x = 0) (h2 : complexHessian a b h x = 0) (t : ℝ) :
    modifiedA a b (fun y => u y+t*h y) x = modifiedA a b u x := by
  apply modifiedA_centered_pluriharmonic hu (contDiffAt_const.mul hh) a b
  · simp [h0]
  · change fderiv ℝ (fun y => t • h y) x = 0
    rw [fderiv_fun_const_smul (hh.differentiableAt (by norm_num)),h1,smul_zero]
  · rw [complexHessian_const_mul_at hh,h2,smul_zero]

theorem modifiedB_centered_scaled_perturbation {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) (a b : ι → E)
    (h0 : h x = 0) (h1 : fderiv ℝ h x = 0) (t : ℝ) :
    modifiedB a b (fun y => u y+t*h y) x =
      modifiedB a b u x+(t:ℂ) • pureHessian a b h x := by
  rw [modifiedB_centered_perturbation hu (contDiffAt_const.mul hh) a b
    (by simp [h0]) (by
      change fderiv ℝ (fun y => t • h y) x = 0
      rw [fderiv_fun_const_smul (hh.differentiableAt (by norm_num)),h1,smul_zero]),
    pureHessian_const_mul_at hh]

variable [Fintype ι] [DecidableEq ι]

theorem modifiedSchur_centered_diagonal_path {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) (a b : ι → E)
    (h0 : h x = 0) (h1 : fderiv ℝ h x = 0) (h2 : complexHessian a b h x = 0)
    (d s : ι → ℝ) (hA : modifiedA a b u x = 1)
    (hB : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hH : pureHessian a b h x = Matrix.diagonal (fun i => (s i:ℂ))) (t : ℝ) :
    modifiedSchur a b (fun y => u y+t*h y) x =
      Matrix.diagonal (fun i => ((1-(d i+t*s i)^2:ℝ):ℂ)) := by
  have hB' : modifiedB a b (fun y => u y+t*h y) x =
      Matrix.diagonal (fun i => ((d i+t*s i:ℝ):ℂ)) := by
    rw [modifiedB_centered_scaled_perturbation hu hh a b h0 h1,hB,hH]
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,hij,Complex.ofReal_add,Complex.ofReal_mul]
  unfold modifiedSchur
  rw [modifiedA_centered_scaled_pluriharmonic hu hh a b h0 h1 h2,hA,hB']
  exact matrixSchur_one_real_diagonal _

theorem modifiedRayleigh_centered_diagonal_path {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) (a b : ι → E)
    (h0 : h x = 0) (h1 : fderiv ℝ h x = 0) (h2 : complexHessian a b h x = 0)
    (d s : ι → ℝ) (hA : modifiedA a b u x = 1)
    (hB : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hH : pureHessian a b h x = Matrix.diagonal (fun i => (s i:ℂ))) (i : ι) (t : ℝ) :
    (modifiedSchur a b (fun y => u y+t*h y) x i i).re /
      (modifiedA a b (fun y => u y+t*h y) x i i).re = 1-(d i+t*s i)^2 := by
  rw [modifiedSchur_centered_diagonal_path hu hh a b h0 h1 h2 d s hA hB hH,
    modifiedA_centered_scaled_pluriharmonic hu hh a b h0 h1 h2,hA]
  simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Complex.ofReal_re,Complex.one_re,div_one]

theorem modifiedRayleigh_centered_diagonal_hasDerivAt {u h : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hh : ContDiffAt ℝ 2 h x) (a b : ι → E)
    (h0 : h x = 0) (h1 : fderiv ℝ h x = 0) (h2 : complexHessian a b h x = 0)
    (d s : ι → ℝ) (hA : modifiedA a b u x = 1)
    (hB : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hH : pureHessian a b h x = Matrix.diagonal (fun i => (s i:ℂ))) (i : ι) :
    HasDerivAt (fun t : ℝ =>
      (modifiedSchur a b (fun y => u y+t*h y) x i i).re /
      (modifiedA a b (fun y => u y+t*h y) x i i).re) (-2*d i*s i) 0 := by
  have he : (fun t : ℝ =>
      (modifiedSchur a b (fun y => u y+t*h y) x i i).re /
      (modifiedA a b (fun y => u y+t*h y) x i i).re) =
      (fun t : ℝ => 1-(d i+t*s i)^2) :=
    funext fun t => modifiedRayleigh_centered_diagonal_path hu hh a b h0 h1 h2 d s hA hB hH i t
  rw [he]
  convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub
    ((((hasDerivAt_id (0:ℝ)).mul_const (s i)).const_add (d i)).pow 2) using 1 <;> try rfl
  all_goals norm_num [id_eq] <;> ring

end PowerConvexity
